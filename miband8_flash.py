#!/usr/bin/env python3
"""
Прошивка Xiaomi Smart Band 8 по Bluetooth LE с macOS (или Linux).

Протокол перенесён из Gadgetbridge (AGPLv3, https://codeberg.org/Freeyourgadget/Gadgetbridge):
XiaomiAuthService, XiaomiCharacteristicV1, XiaomiDataUploadService, XiaomiSystemService.

Команды:
  scan                          найти браслет поблизости
  info  --key KEY               авторизоваться и показать модель, прошивку, заряд (ничего не меняет)
  flash --key KEY FILE.bin      загрузить файл прошивки в браслет
"""
from __future__ import annotations

import argparse
import asyncio
import hashlib
import hmac
import logging
import math
import os
import re
import struct
import sys
import time
import zlib
from typing import Callable, Dict, List, Optional, Tuple

try:
    from bleak import BleakClient, BleakScanner
    from bleak.exc import BleakError
    from cryptography.exceptions import InvalidTag
    from cryptography.hazmat.primitives.ciphers.aead import AESCCM
except ImportError as e:  # pragma: no cover
    sys.exit(f"Не хватает зависимостей ({e.name}). Выполните: pip install -r requirements.txt")

log = logging.getLogger("miband8")

SERVICE_UUID = "0000fe95-0000-1000-8000-00805f9b34fb"
CHAR_CMD_READ = "00000051-0000-1000-8000-00805f9b34fb"   # ответы браслета
CHAR_CMD_WRITE = "00000052-0000-1000-8000-00805f9b34fb"  # наши команды
CHAR_ACTIVITY = "00000053-0000-1000-8000-00805f9b34fb"   # данные активности (не используем)
CHAR_UPLOAD = "00000055-0000-1000-8000-00805f9b34fb"     # загрузка файлов
# Gadgetbridge ждёт "Xiaomi Smart Band 8 XXXX"; китайская версия может называться "小米手环8 XXXX"
NAME_RE = re.compile(r"(Smart Band 8|手环\s*8)(?!\s*(Pro|Active))", re.I)

# Типы команд (Command.type / Command.subtype)
AUTH_TYPE, AUTH_NONCE, AUTH_CONFIRM = 1, 26, 27
SYSTEM_TYPE, SYS_BATTERY, SYS_DEVICE_INFO, SYS_FIRMWARE_INSTALL = 2, 1, 2, 5
UPLOAD_TYPE, UPLOAD_START = 22, 0
UPLOAD_KIND_FIRMWARE = 32

PAYLOAD_ACK = b"\x00\x00\x03\x00"
CHUNK_START_ACK = b"\x00\x00\x01\x01"
CHUNK_END_ACK = b"\x00\x00\x01\x00"
DEFAULT_MAX_WRITE = 244  # MTU 247 - 3 байта заголовка ATT, как в Gadgetbridge
TIMING_EVERY = 50  # через сколько частей прошивки писать в лог средние задержки
RETRY_DELAY = 30  # с, пауза перед переподключением при --retry: браслету может понадобиться перезапуск


class FlashError(Exception):
    pass


class LinkError(FlashError):
    """Связь оборвалась или браслет не ответил: загрузку можно продолжить после переподключения."""


# ---------------------------------------------------------------- protobuf ---
# Минимальный кодек protobuf, чтобы не тащить protoc: нужны всего несколько сообщений.

def _varint(n: int) -> bytes:
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def _read_varint(data: bytes, i: int) -> Tuple[int, int]:
    shift = result = 0
    while True:
        b = data[i]
        i += 1
        result |= (b & 0x7F) << shift
        if not b & 0x80:
            return result, i
        shift += 7


def pb(*fields) -> bytes:
    """pb((номер, значение), ...): int → varint, float → fixed32, bytes/str → length-delimited."""
    out = bytearray()
    for num, val in fields:
        if val is None:
            continue
        if isinstance(val, bool):
            val = int(val)
        if isinstance(val, int):
            out += _varint(num << 3) + _varint(val)
        elif isinstance(val, float):
            out += _varint(num << 3 | 5) + struct.pack("<f", val)
        else:
            if isinstance(val, str):
                val = val.encode()
            out += _varint(num << 3 | 2) + _varint(len(val)) + bytes(val)
    return bytes(out)


def pb_parse(data: bytes) -> Dict[int, list]:
    fields: Dict[int, list] = {}
    i = 0
    while i < len(data):
        key, i = _read_varint(data, i)
        num, wire = key >> 3, key & 7
        if wire == 0:
            val, i = _read_varint(data, i)
        elif wire == 1:
            val, i = data[i:i + 8], i + 8
        elif wire == 2:
            ln, i = _read_varint(data, i)
            val, i = bytes(data[i:i + ln]), i + ln
        elif wire == 5:
            val, i = data[i:i + 4], i + 4
        else:
            raise ValueError(f"неизвестный wire type {wire}")
        fields.setdefault(num, []).append(val)
    return fields


def pb_get(data: bytes, *path: int, default=None):
    """pb_get(msg, 4, 3, 2): пройти по вложенным полям и вернуть значение последнего."""
    cur = data
    for num in path:
        f = pb_parse(cur)
        if num not in f:
            return default
        cur = f[num][-1]
    return cur


def command(type_: int, subtype: int, *extra) -> bytes:
    return pb((1, type_), (2, subtype), *extra)


# ------------------------------------------------------------------ crypto ---

def hmac_sha256(key: bytes, data: bytes) -> bytes:
    return hmac.new(key, data, hashlib.sha256).digest()


class XiaomiCrypto:
    def __init__(self, secret_key: bytes):
        self.secret_key = secret_key
        self.phone_nonce = os.urandom(16)
        self.enc_key = self.dec_key = None
        self.enc_nonce = self.dec_nonce = None
        self.ready = False  # True после успешной авторизации: дальше всё шифруется

    @property
    def has_keys(self) -> bool:
        return self.dec_key is not None

    def derive(self, watch_nonce: bytes, watch_hmac: bytes) -> bytes:
        """Вычисляет сеансовые ключи (HKDF-SHA256, info="miwear-auth"), проверяет ответ браслета
        и возвращает наш HMAC для подтверждения."""
        prk = hmac_sha256(self.phone_nonce + watch_nonce, self.secret_key)
        okm, t, counter = b"", b"", 1
        while len(okm) < 64:
            t = hmac_sha256(prk, t + b"miwear-auth" + bytes([counter]))
            okm += t
            counter += 1
        self.dec_key, self.enc_key = okm[0:16], okm[16:32]
        self.dec_nonce, self.enc_nonce = okm[32:36], okm[36:40]

        expected = hmac_sha256(self.dec_key, watch_nonce + self.phone_nonce)
        if not hmac.compare_digest(expected, watch_hmac):
            raise FlashError("Неверный ключ авторизации: браслет его не принял. "
                             "Проверьте ключ (32 hex-символа) и что браслет не перепривязывали после его получения.")
        return hmac_sha256(self.enc_key, self.phone_nonce + watch_nonce)

    def encrypt(self, data: bytes, index: int) -> bytes:
        nonce = self.enc_nonce + struct.pack("<II", 0, index & 0xFFFFFFFF)
        return AESCCM(self.enc_key, tag_length=4).encrypt(nonce, data, None)

    def decrypt(self, data: bytes) -> bytes:
        nonce = self.dec_nonce + bytes(8)
        return AESCCM(self.dec_key, tag_length=4).decrypt(nonce, data, None)


# --------------------------------------------------------------- transport ---

class Link:
    """Сериализует записи в GATT: подтверждения и данные не должны перемешиваться."""

    def __init__(self, client):
        self.client = client
        self.loop = asyncio.get_running_loop()
        self.lock = asyncio.Lock()
        self._tasks = set()
        self.no_response = set()  # UUID характеристик, куда пишем без подтверждения (--fast)
        self.peripheral = getattr(getattr(client, "_backend", None), "_peripheral", None)

    async def write(self, char, data: bytes):
        log.debug("→ %s %s", char.uuid[4:8], data.hex())
        async with self.lock:
            if char.uuid in self.no_response:
                await self._wait_ready()
                await self.client.write_gatt_char(char, data, response=False)
            else:
                await self.client.write_gatt_char(char, data, response="write" in char.properties)

    async def _wait_ready(self):
        # CoreBluetooth молча выбрасывает запись без подтверждения, если его очередь полна
        ready = getattr(self.peripheral, "canSendWriteWithoutResponse", None)
        if ready is None:
            return
        deadline = self.loop.time() + 10
        while not ready():
            if not self.client.is_connected:
                raise LinkError("Браслет отключился")
            if self.loop.time() > deadline:
                # на Band 8 с CN 1.8.124 так выглядело зависание браслета: он переставал отвечать совсем
                raise LinkError("Браслет 10 с не принимает данные, похоже, он завис в быстром режиме "
                                "(без --fast такого не было). Загрузка продолжится с места остановки.")
            await asyncio.sleep(0.002)

    def write_soon(self, char, data: bytes):
        task = self.loop.create_task(self.write(char, data))
        self._tasks.add(task)
        task.add_done_callback(self._write_done)

    def _write_done(self, task):
        self._tasks.discard(task)
        if task.cancelled() or task.exception() is None:
            return
        # Подтверждение не ушло. Если связь уже закрыта, это нормально (например, после info);
        # если нет, ожидающая сторона сама получит тайм-аут или повтор от браслета.
        level = logging.WARNING if self.client.is_connected else logging.DEBUG
        log.log(level, "Подтверждение не отправлено: %s", task.exception())


class Channel:
    """Одна характеристика с протоколом Xiaomi V1: одиночные пакеты и передача частями."""

    def __init__(self, link: Link, char, crypto: XiaomiCrypto, name: str,
                 increment_nonce: bool = True, on_message: Optional[Callable[[bytes], None]] = None):
        self.link, self.char, self.crypto, self.name = link, char, crypto, name
        self.increment_nonce = increment_nonce
        self.on_message = on_message
        self.max_write = DEFAULT_MAX_WRITE
        self.events: asyncio.Queue = asyncio.Queue()
        self.tx_lock = asyncio.Lock()
        self.last_timing = (0.0, 0.0, 0.0)
        self.reset()

    def reset(self):
        self.enc_index = 1  # 0 занят авторизацией
        self.rx_total = 0
        self.rx_chunks: Dict[int, bytes] = {}

    # приём -------------------------------------------------------------------
    def on_notify(self, _sender, data: bytearray):
        data = bytes(data)
        log.debug("← %s %s", self.char.uuid[4:8], data.hex())
        if len(data) < 4:
            return
        chunk = struct.unpack_from("<H", data)[0]
        if chunk:
            if chunk > self.rx_total:
                log.warning("%s: лишний фрагмент %d из %d", self.name, chunk, self.rx_total)
                return
            self.rx_chunks[chunk] = data[2:]
            if len(self.rx_chunks) == self.rx_total:
                self.link.write_soon(self.char, CHUNK_END_ACK)
                payload = b"".join(self.rx_chunks[i] for i in range(1, self.rx_total + 1))
                self.rx_total, self.rx_chunks = 0, {}
                self._deliver(payload, encrypted=self.crypto.has_keys)
            return

        kind = data[2]
        if kind == 0 and len(data) >= 6:  # браслет начинает передачу частями
            self.rx_total = struct.unpack_from("<H", data, 4)[0]
            self.rx_chunks = {}
            self.link.write_soon(self.char, CHUNK_START_ACK)
        elif kind == 1:  # подтверждения для нашей передачи частями
            sub = data[3]
            if sub == 5:
                missing = list(struct.unpack_from(f"<{(len(data) - 4) // 2}H", data, 4))
                self.events.put_nowait(("resend", missing))
            else:
                self.events.put_nowait(({0: "end", 1: "start", 2: "nack"}.get(sub, f"chunk-ack-{sub}"), None))
        elif kind == 2:  # одиночное сообщение
            self.link.write_soon(self.char, PAYLOAD_ACK)
            self._deliver(data[4:], encrypted=data[3] == 1)
        elif kind == 3:  # подтверждение нашего одиночного сообщения
            self.events.put_nowait(("ack", data[3]))

    def _deliver(self, payload: bytes, encrypted: bool):
        if encrypted:
            try:
                payload = self.crypto.decrypt(payload)
            except InvalidTag:
                log.warning("%s: не удалось расшифровать сообщение, пропускаю", self.name)
                return
        if self.on_message:
            self.on_message(payload)

    def on_disconnect(self):
        self.events.put_nowait(("disconnected", None))

    # отправка ----------------------------------------------------------------
    async def _event(self, timeout: float):
        try:
            ev = await asyncio.wait_for(self.events.get(), timeout)
        except asyncio.TimeoutError:
            raise LinkError(f"{self.name}: браслет не ответил за {timeout:.0f} с") from None
        if ev[0] == "disconnected":
            raise LinkError("Браслет отключился")
        return ev

    async def send(self, payload: bytes, timeout: float = 15.0):
        async with self.tx_lock:
            while not self.events.empty():
                self.events.get_nowait()

            encrypt = self.crypto.ready
            index = self.enc_index if self.increment_nonce else 0
            data = self.crypto.encrypt(payload, index) if encrypt else payload
            max_write = self.max_write

            if len(data) + 6 <= max_write:
                header = struct.pack("<HBB", 0, 2, 1 if encrypt else 2)
                if encrypt:
                    header += struct.pack("<H", index & 0xFFFF)
                    if self.increment_nonce:
                        self.enc_index += 1
                await self.link.write(self.char, header + data)
                kind, result = await self._event(timeout)
                if kind != "ack" or result != 0:
                    raise FlashError(f"{self.name}: браслет отклонил сообщение ({kind} {result})")
                return

            if encrypt and self.increment_nonce:
                data = struct.pack("<H", index & 0xFFFF) + data
                self.enc_index += 1
            size = max_write - 2
            parts = [data[i:i + size] for i in range(0, len(data), size)]
            t0 = time.monotonic()
            await self.link.write(self.char, struct.pack("<HBBH", 0, 0, 1 if encrypt else 0, len(parts)))
            kind, _ = await self._event(timeout)
            if kind != "start":
                raise LinkError(f"{self.name}: браслет не принял начало передачи ({kind})")
            t1 = time.monotonic()
            for n, part in enumerate(parts, 1):
                await self.link.write(self.char, struct.pack("<H", n) + part)
            t2 = time.monotonic()
            while True:
                kind, arg = await self._event(timeout)
                if kind == "end":
                    # ожидание ответа на начало, отправка частей, ожидание ответа на конец
                    self.last_timing = (t1 - t0, t2 - t1, time.monotonic() - t2)
                    return
                if kind == "resend" and arg:
                    log.info("%s: браслет просит повторить фрагменты %s", self.name, arg)
                    for n in arg:
                        await self.link.write(self.char, struct.pack("<H", n) + parts[n - 1])
                    continue
                raise LinkError(f"{self.name}: браслет отклонил передачу ({kind})")


# -------------------------------------------------------------------- band ---

class Band:
    def __init__(self, client, secret_key: bytes, max_write: Optional[int] = None, fast: bool = False):
        self.client = client
        self.crypto = XiaomiCrypto(secret_key)
        self.max_write_override = max_write
        self.fast = fast
        self.fast_writes = False
        self.inbox: asyncio.Queue = asyncio.Queue()
        self.channels: List[Channel] = []

    async def setup(self):
        link = Link(self.client)

        def char(uuid):
            c = self.client.services.get_characteristic(uuid)
            if c is None:
                raise FlashError(f"У устройства нет характеристики {uuid}: это не Xiaomi Smart Band 8?")
            return c

        self.cmd_read = Channel(link, char(CHAR_CMD_READ), self.crypto, "команды", on_message=self._on_command)
        self.cmd_write = Channel(link, char(CHAR_CMD_WRITE), self.crypto, "команды")
        self.activity = Channel(link, char(CHAR_ACTIVITY), self.crypto, "активность")
        self.upload = Channel(link, char(CHAR_UPLOAD), self.crypto, "загрузка", increment_nonce=False)
        self.channels = [self.cmd_write, self.cmd_read, self.activity, self.upload]

        mtu = getattr(self.client, "mtu_size", 247) or 247
        max_write = self.max_write_override or min(mtu - 3, DEFAULT_MAX_WRITE)
        log.info("MTU %d, размер пакета %d байт", mtu, max_write)
        log.info("Свойства характеристики загрузки: %s", ", ".join(self.upload.char.properties))
        # Android (а значит, Gadgetbridge и Mi Fitness) пишет без подтверждения, если характеристика
        # это поддерживает; по умолчанию мы ждём подтверждения на каждый пакет, это в разы медленнее
        self.fast_writes = self.fast and "write-without-response" in self.upload.char.properties
        if self.fast_writes:
            link.no_response.add(self.upload.char.uuid)
        for ch in self.channels:
            ch.max_write = max_write
            await self.client.start_notify(ch.char, ch.on_notify)

    def on_disconnect(self):
        for ch in self.channels:
            ch.on_disconnect()
        self.inbox.put_nowait((-1, -1, b""))

    def _on_command(self, payload: bytes):
        try:
            f = pb_parse(payload)
            type_, sub = f[1][0], f.get(2, [0])[0]
        except Exception:
            log.warning("Не удалось разобрать команду: %s", payload.hex())
            return
        log.debug("команда %d/%d: %s", type_, sub, payload.hex())
        self.inbox.put_nowait((type_, sub, payload))

    async def request(self, payload: bytes, type_: int, sub: int, timeout: float = 20.0) -> bytes:
        await self.cmd_write.send(payload)
        loop = asyncio.get_running_loop()
        deadline = loop.time() + timeout
        while True:
            remaining = deadline - loop.time()
            if remaining <= 0:
                raise LinkError(f"Нет ответа на команду {type_}/{sub}")
            try:
                t, s, p = await asyncio.wait_for(self.inbox.get(), remaining)
            except asyncio.TimeoutError:
                continue
            if t == -1:
                raise LinkError("Браслет отключился")
            if (t, s) == (type_, sub):
                return p
            log.debug("пропускаю сообщение %d/%d", t, s)

    async def authenticate(self):
        c = self.crypto
        reply = await self.request(
            command(AUTH_TYPE, AUTH_NONCE, (3, pb((30, pb((1, c.phone_nonce)))))),
            AUTH_TYPE, AUTH_NONCE)
        verify = pb_get(reply, 3, 31)
        if verify is None:
            raise FlashError("Браслет не начал авторизацию (возможно, он не привязан к аккаунту Xiaomi).")
        our_hmac = c.derive(pb_get(verify, 1), pb_get(verify, 2))

        companion = pb((1, 0), (2, 34.0), (3, "MacBook"), (4, 224), (5, "EN"))
        confirm = pb((1, our_hmac), (2, c.encrypt(companion, 0)))
        await self.request(command(AUTH_TYPE, AUTH_CONFIRM, (3, pb((32, confirm)))), AUTH_TYPE, AUTH_CONFIRM)

        c.ready = True
        for ch in self.channels:
            ch.reset()

    async def device_info(self) -> Dict[str, str]:
        reply = await self.request(command(SYSTEM_TYPE, SYS_DEVICE_INFO), SYSTEM_TYPE, SYS_DEVICE_INFO)
        f = pb_parse(pb_get(reply, 4, 3, default=b""))

        def s(n):
            return f[n][0].decode(errors="replace") if n in f else "?"
        return {"serial": s(1), "firmware": s(2), "model": s(4)}

    async def battery(self) -> Optional[int]:
        reply = await self.request(command(SYSTEM_TYPE, SYS_BATTERY), SYSTEM_TYPE, SYS_BATTERY)
        return pb_get(reply, 4, 2, 1, 1)

    async def install_firmware(self, fw: bytes, version: str, progress: Callable[[int, int, int], None]):
        """progress(загружено байт файла, размер файла, с какого байта браслет продолжил)"""
        md5 = hashlib.md5(fw).digest()

        request = pb((1, 0), (2, 0), (3, version), (4, md5.hex()))
        reply = await self.request(command(SYSTEM_TYPE, SYS_FIRMWARE_INSTALL, (4, pb((16, request)))),
                                   SYSTEM_TYPE, SYS_FIRMWARE_INSTALL, timeout=30)
        status = pb_get(reply, 4, 17, 1, default=0)
        if status != 0:
            # Коды отказа нигде не описаны (Gadgetbridge проверяет только 0). Браслет видел лишь версию
            # и md5, сам файл ещё не передавался.
            raise FlashError(f"Браслет отказался начинать установку (status={status}, ответ {reply.hex()}). "
                             "Файл ещё не передавался, на браслет ничего не записано. Возможные причины: "
                             "заряд, версия, которую браслет не принимает, или занятость браслета.")

        upload = pb((1, UPLOAD_KIND_FIRMWARE), (2, md5), (3, len(fw)))
        reply = await self.request(command(UPLOAD_TYPE, UPLOAD_START, (24, pb((1, upload)))),
                                   UPLOAD_TYPE, UPLOAD_START, timeout=30)
        ack = pb_parse(pb_get(reply, 24, 2, default=b""))
        errno = ack.get(2, [0])[0]
        resume = ack.get(4, [0])[0]
        chunk_size = ack.get(5, [2048])[0]
        if errno:
            raise FlashError(f"Браслет отказался принимать файл (errno={errno})")
        if resume:
            log.info("Браслет продолжает прерванную загрузку с байта %d", resume)

        # тип + md5 + размер + данные + crc32, затем части по chunk_size - 4 байта
        body = bytes([0, UPLOAD_KIND_FIRMWARE]) + md5 + struct.pack("<I", len(fw)) + fw[resume:]
        body += struct.pack("<I", zlib.crc32(body))
        part_size = chunk_size - 4
        total = math.ceil(len(body) / part_size)
        timing = [0.0, 0.0, 0.0]
        for i in range(total):
            part = struct.pack("<HH", total, i + 1) + body[i * part_size:(i + 1) * part_size]
            await self.upload.send(part, timeout=30)
            timing = [a + b for a, b in zip(timing, self.upload.last_timing)]
            if (i + 1) % TIMING_EVERY == 0:
                log.info("Части %d-%d из %d, в среднем: ответ на начало %.0f мс, отправка %.0f мс, "
                         "ответ на конец %.0f мс", i + 2 - TIMING_EVERY, i + 1, total,
                         *(t * 1000 / TIMING_EVERY for t in timing))
                timing = [0.0, 0.0, 0.0]
            progress(resume + (len(fw) - resume) * (i + 1) // total, len(fw), resume)


# --------------------------------------------------------------------- CLI ---

def parse_key(text: str) -> bytes:
    text = text.strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if not re.fullmatch(r"[0-9a-f]{32}", text):
        raise SystemExit("Ключ должен состоять из 32 hex-символов (можно с префиксом 0x).")
    return bytes.fromhex(text)


def detect_version(fw: bytes) -> Optional[str]:
    # Так определяет версию Gadgetbridge (проверено разработчиками на Band 8 Pro)
    if len(fw) > 16 and fw[0] == 0x60 and fw[1] == 0x5A and fw[2] == 0x5A and fw[4] == 0x7E:
        return fw[4:15].decode("utf-8", "replace")
    # Файлы Band 8 (M2239B1): 78 56 34 12, затем два uint32 и строка версии с 12-го байта
    if len(fw) > 32 and fw[:4] == b"\x78\x56\x34\x12":
        m = re.match(rb"(\d{1,2}\.\d{1,2}\.\d{1,3})\0", fw[12:32])
        if m:
            return m.group(1).decode()
    return None


def version_candidates(fw: bytes) -> List[str]:
    found = re.findall(rb"(?<![\d.])\d{1,2}\.\d{1,2}\.\d{1,3}(?![\d.])", fw[:262144])
    return list(dict.fromkeys(v.decode() for v in found))[:8]


def connected_bands() -> list:
    """Браслеты, которые macOS уже держит подключёнными (например, как устройство ввода HID).
    Подключённый браслет не вещает, поэтому поиск его не видит, но к нему можно подключиться."""
    if sys.platform != "darwin":
        return []
    try:
        from CoreBluetooth import CBUUID
        from bleak.backends.corebluetooth.CentralManagerDelegate import CentralManagerDelegate
        from bleak.backends.device import BLEDevice

        manager = CentralManagerDelegate.alloc().init()
        services = [CBUUID.UUIDWithString_("FE95"), CBUUID.UUIDWithString_("1812")]  # Xiaomi, HID
        peripherals = manager.central_manager.retrieveConnectedPeripheralsWithServices_(services)
        # детали в том же виде, что у устройств из BleakScanner: (CBPeripheral, CentralManagerDelegate)
        return [BLEDevice(p.identifier().UUIDString(), p.name(), (p, manager))
                for p in peripherals if NAME_RE.search(p.name() or "")]
    except Exception as e:  # внутренности bleak могут измениться; тогда просто ищем как обычно
        log.debug("Не удалось получить подключённые устройства: %r", e)
        return []


async def find_band(args):
    connected = connected_bands()
    if args.address:
        dev = next((d for d in connected if d.address.lower() == args.address.lower()), None)
        dev = dev or await BleakScanner.find_device_by_address(args.address, timeout=args.timeout)
        if dev is None:
            raise LinkError(f"Устройство {args.address} не найдено")
        return dev
    if len(connected) > 1:
        names = ", ".join(f"{d.name} ({d.address})" for d in connected)
        raise FlashError(f"К Mac подключено несколько браслетов: {names}. Укажите нужный через --address.")
    if connected:
        print(f"Найден: {connected[0].name} ({connected[0].address}), уже подключён к Mac")
        return connected[0]
    print(f"Ищу браслет ({args.timeout:.0f} с)... Bluetooth на телефоне лучше выключить.")
    found = await BleakScanner.discover(timeout=args.timeout, return_adv=True)
    bands = [(d, adv) for d, adv in found.values() if NAME_RE.search(adv.local_name or d.name or "")]
    if not bands:
        raise LinkError("Xiaomi Smart Band 8 не найден. Отключите браслет от телефона и попробуйте ещё раз. "
                         "Если не поможет, запустите scan: он покажет все устройства Xiaomi рядом, "
                         "и браслет можно будет указать через --address.")
    if len(bands) > 1:
        names = ", ".join(f"{adv.local_name} ({d.address})" for d, adv in bands)
        raise FlashError(f"Найдено несколько браслетов: {names}. Укажите нужный через --address.")
    dev, adv = bands[0]
    print(f"Найден: {adv.local_name} ({dev.address}), RSSI {adv.rssi}")
    return dev


async def connect(args):
    dev = await find_band(args)
    band_ref: List[Band] = []
    loop = asyncio.get_running_loop()

    def on_disconnect(_client):
        if band_ref:
            loop.call_soon_threadsafe(band_ref[0].on_disconnect)

    client = BleakClient(dev, disconnected_callback=on_disconnect, timeout=30)
    await client.connect()
    try:
        band = Band(client, args.key_bytes, max_write=args.max_write, fast=getattr(args, "fast", False))
        band_ref.append(band)
        await band.setup()
        print("Авторизация...")
        await band.authenticate()
    except BaseException:
        await client.disconnect()
        raise
    print("Авторизация успешна.")
    return client, band


async def print_info(band: Band) -> Tuple[Dict[str, str], Optional[int]]:
    info = await band.device_info()
    level = await band.battery()
    print(f"  Модель:    {info['model']}")
    print(f"  Серийный:  {info['serial']}")
    print(f"  Прошивка:  {info['firmware']}")
    print(f"  Заряд:     {level if level is not None else '?'}%")
    return info, level


async def cmd_scan(args):
    connected = connected_bands()
    for d in connected:
        print(f"  {d.name:32} {d.address}  уже подключён к Mac  <- браслет")
    print(f"Сканирую {args.timeout:.0f} с...")
    found = await BleakScanner.discover(timeout=args.timeout, return_adv=True)
    any_found = bool(connected)
    for d, adv in sorted(found.values(), key=lambda x: -(x[1].rssi or -999)):
        name = adv.local_name or d.name or ""
        xiaomi = SERVICE_UUID in (adv.service_uuids or []) or SERVICE_UUID in (adv.service_data or {})
        if NAME_RE.search(name) or xiaomi or (args.all and name):
            any_found = True
            mark = "  <- браслет" if NAME_RE.search(name) else ("  <- устройство Xiaomi" if xiaomi else "")
            print(f"  {name or '(без имени)':32} {d.address}  RSSI {adv.rssi}{mark}")
    if not any_found:
        print("Ничего не найдено. Браслет виден, только когда не подключён к телефону.")
        if not args.all:
            print("Запустите scan --all, чтобы увидеть все устройства с именем.")


async def cmd_info(args):
    client, band = await connect(args)
    try:
        await print_info(band)
    finally:
        await client.disconnect()


def retryable(e: BaseException) -> bool:
    """Обрыв связи, после которого браслет продолжит загрузку с места остановки."""
    if isinstance(e, LinkError):
        return True
    if isinstance(e, BleakError):
        text = str(e)
        return "turned off" not in text and "not authorized" not in text
    return isinstance(e, (asyncio.TimeoutError, TimeoutError))


def duration(sec: float) -> str:
    minutes = int(sec // 60)
    if minutes >= 60:
        return f"{minutes // 60} ч {minutes % 60:02d} мин"
    return f"{minutes} мин {int(sec % 60):02d} с"


async def cmd_flash(args):
    fw = open(args.file, "rb").read()
    if not 100_000 <= len(fw) <= 64 * 1024 * 1024:
        raise FlashError(f"Подозрительный размер файла: {len(fw)} байт")
    detected = detect_version(fw)
    if args.version and detected and args.version != detected:
        raise FlashError(f"В заголовке файла версия {detected}, а указана --version {args.version}. "
                         "Проверьте файл или уберите --version.")
    version = args.version or detected
    if not version:
        hint = ", ".join(version_candidates(fw)) or "не найдено"
        raise FlashError("Не удалось определить версию прошивки из файла. Укажите её явно: --version X.Y.Z\n"
                         f"Похожие на версию строки в начале файла: {hint}")

    client, band = await connect(args)
    try:
        info, level = await print_info(band)
        md5 = hashlib.md5(fw).hexdigest()
        print(f"\n  Файл:      {args.file}")
        print(f"  Размер:    {len(fw)} байт, md5 {md5}")
        print(f"  Версия:    {version}")
        announce = args.announce_version or version
        if announce != version:
            print(f"  Браслету будет сообщена версия: {announce}")
        if band.fast_writes:
            print("  Режим:     быстрый (пакеты без подтверждения каждого)")
            if args.retry:
                print("             при зависании браслета скрипт переподключится и продолжит")
        elif args.fast:
            print("  Режим:     обычный: браслет не поддерживает запись без подтверждения "
                  f"({', '.join(band.upload.char.properties)})")

        if level is not None and level < 50 and not args.ignore_battery:
            raise FlashError("Заряд ниже 50%. Зарядите браслет (или --ignore-battery, если он на зарядке).")
        if info["firmware"] == version:
            print("\n  Внимание: версия в браслете совпадает с версией файла.")

        print("\nВо время загрузки не закрывайте крышку MacBook и держите браслет рядом.")
        # input() пишет подсказку в stderr, а его можно перенаправить в файл лога: печатаем сами
        if not args.yes:
            print("Чтобы начать прошивку, введите YES: ", end="", flush=True)
            if input().strip() != "YES":
                print("Отменено.")
                return

        def make_progress():
            started = time.monotonic()
            resume_shown = False

            def progress(done, total, resumed_from):
                nonlocal resume_shown, parts_sent
                parts_sent += 1
                if resumed_from and not resume_shown:
                    resume_shown = True
                    print(f"  Браслет продолжает прерванную загрузку с {resumed_from * 100 // total}%.")
                elapsed = time.monotonic() - started
                speed = (done - resumed_from) / elapsed if elapsed > 0 else 0
                eta = (total - done) / speed if speed > 0 else 0
                print(f"\r  Загрузка: {done * 100 // total:3d}%  {speed / 1024:5.1f} КБ/с  "
                      f"осталось ~{duration(eta)}   ", end="", flush=True)
            return progress

        # попытки считаются подряд: если до обрыва что-то загрузилось, счётчик начинается заново
        retries_left = args.retry
        while True:
            parts_sent = 0
            try:
                if band is None:
                    client, band = await connect(args)
                await band.install_firmware(fw, announce, make_progress())
                break
            except Exception as e:
                if parts_sent:
                    retries_left = args.retry
                if retries_left <= 0 or not retryable(e):
                    raise
                retries_left -= 1
                print(f"\n\n  Связь прервалась: {e}\n  Переподключусь через {RETRY_DELAY} с "
                      f"(осталось попыток: {retries_left}).", flush=True)
                log.warning("Связь прервалась (%r), повтор через %d с, осталось попыток %d",
                            e, RETRY_DELAY, retries_left)
                band = None
                if client.is_connected:
                    try:
                        await client.disconnect()
                    except Exception:
                        pass
                await asyncio.sleep(RETRY_DELAY)
        print("\n\nФайл загружен. Браслет проверит его, установит и перезагрузится (до 10 минут).")
        print("Не трогайте браслет и не снимайте его с зарядки, пока он не загрузится.")
        await asyncio.sleep(5)
    finally:
        if client.is_connected:
            await client.disconnect()


def fail(message: str):
    # stderr часто перенаправляют в файл лога; тогда без этого ошибку в Терминале не видно
    if not sys.stderr.isatty():
        print(message, flush=True)
    sys.exit(message)


def main():
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("-v", "--verbose", action="store_true", help="подробный лог с hex-дампами")
    common.add_argument("--timeout", type=float, default=15.0, help="время поиска браслета, с")

    band_opts = argparse.ArgumentParser(add_help=False, parents=[common])
    band_opts.add_argument("--key", required=True, help="ключ авторизации (32 hex-символа)")
    band_opts.add_argument("--address", help="адрес/UUID браслета из команды scan")
    band_opts.add_argument("--max-write", type=int, help="размер BLE-пакета (по умолчанию MTU-3, не больше 244)")

    p = argparse.ArgumentParser(description="Прошивка Xiaomi Smart Band 8 по Bluetooth с Mac")
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("scan", parents=[common], help="найти браслет")
    s.add_argument("--all", action="store_true", help="показать все BLE-устройства с именем")

    sub.add_parser("info", parents=[band_opts], help="авторизоваться и показать сведения о браслете")

    f = sub.add_parser("flash", parents=[band_opts], help="загрузить прошивку")
    f.add_argument("file", help="файл прошивки .bin")
    f.add_argument("--version", help="версия прошивки, если не определилась из файла")
    # Mi Fitness при переходе CN -> Global сообщает браслету не версию файла: при подмене файла
    # на iPhone это версия китайского обновления, в патче для Android строка "firmware.bin"
    f.add_argument("--announce-version", metavar="TEXT",
                   help="какую версию сообщить браслету в запросе установки (по умолчанию версия файла)")
    f.add_argument("--fast", action="store_true",
                   help="экспериментально: слать пакеты прошивки без подтверждения каждого, как телефон "
                        "(Band 8 с CN 1.8.124 в этом режиме зависал через 1-2 минуты)")
    f.add_argument("--retry", type=int, default=0, metavar="N",
                   help="при обрыве связи переподключиться и продолжить загрузку; N попыток подряд "
                        "без продвижения, например --retry 10; YES повторно не спрашивается")
    f.add_argument("--ignore-battery", action="store_true", help="не проверять заряд")
    f.add_argument("--yes", action="store_true", help="не спрашивать подтверждение")

    args = p.parse_args()
    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S")
    if not args.verbose:
        logging.getLogger("bleak").setLevel(logging.WARNING)
    if getattr(args, "key", None):
        args.key_bytes = parse_key(args.key)

    handler = {"scan": cmd_scan, "info": cmd_info, "flash": cmd_flash}[args.cmd]
    try:
        asyncio.run(handler(args))
    except FlashError as e:
        fail(f"\nОшибка: {e}")
    except BleakError as e:
        text = str(e)
        if "turned off" in text or "not authorized" in text:
            # CoreBluetooth не сообщает «включён», если у запустившей программы нет доступа к Bluetooth
            fail("\nBluetooth недоступен для этой программы. Если на Mac Bluetooth включён, значит, "
                 "у программы, из которой запущен скрипт, нет к нему доступа. Запустите скрипт "
                 "из приложения «Терминал» и разрешите доступ, когда macOS спросит "
                 "(или включите «Терминал» в «Системные настройки → Конфиденциальность и "
                 "безопасность → Bluetooth»).")
        fail(f"\nОшибка Bluetooth: {text}")
    except KeyboardInterrupt:
        fail("\nПрервано. Если загрузка не дошла до 100%, запустите flash ещё раз: "
             "браслет может продолжить с места остановки.")
    except Exception as e:
        log.exception("Непредвиденная ошибка")  # traceback остаётся в логе
        fail(f"\nНепредвиденная ошибка: {e!r}")


if __name__ == "__main__":
    main()
