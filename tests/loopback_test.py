"""Loopback test: drives miband8_flash.Band against a fake band that implements the
band side of the Gadgetbridge Xiaomi V1 protocol independently (no shared helpers for framing)."""
import asyncio
import hashlib
import hmac
import importlib.util
import os
import struct
import sys
import zlib

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESCCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

SCRIPT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "miband8_flash.py")
spec = importlib.util.spec_from_file_location("m", SCRIPT)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

R, W, A, U = m.CHAR_CMD_READ, m.CHAR_CMD_WRITE, m.CHAR_ACTIVITY, m.CHAR_UPLOAD


def hm(k, d):
    return hmac.new(k, d, hashlib.sha256).digest()


class Char:
    def __init__(self, uuid, no_response=False):
        self.uuid = uuid
        self.properties = ["write", "write-without-response", "notify"] if no_response else ["write", "notify"]


class Services:
    def __init__(self, upload_no_response=False):
        self.chars = {u: Char(u, no_response=(u == U and upload_no_response)) for u in (R, W, A, U)}

    def get_characteristic(self, uuid):
        return self.chars.get(uuid)


class Peripheral:
    """CoreBluetooth: очередь записи без подтверждения иногда занята."""

    def __init__(self):
        self.calls = 0
        self.busy = 0

    def canSendWriteWithoutResponse(self):
        self.calls += 1
        if self.calls % 4 == 0:
            self.busy += 1
            return False
        return True


class Backend:
    def __init__(self):
        self._peripheral = Peripheral()


class FakeBand:
    def __init__(self, key, mtu=185, encrypt_auth_reply=True, install_status=0,
                 upload_no_response=False, stored=b"", drop_after=None):
        self.key, self.mtu_size = key, mtu
        self.max_write = min(mtu - 3, 244)
        self.services = Services(upload_no_response)
        self._backend = Backend()
        self.is_connected = True
        self.drop_after = drop_after  # оборвать связь после стольких частей прошивки
        self.on_drop = None
        self.responses = []  # (uuid, response) для каждой записи
        self.stored = stored  # часть файла, полученная браслетом в прошлый раз
        self.cbs = {}
        self.rx = {}
        self.pending = None
        self.loop = asyncio.get_running_loop()
        self.encrypt_auth_reply = encrypt_auth_reply
        self.install_status = install_status
        self.parts = []
        self.firmware = None
        self.install_request = None
        self.writes = 0

    async def disconnect(self):
        self.is_connected = False

    async def start_notify(self, char, cb):
        self.cbs[char.uuid] = cb

    def notify(self, uuid, data):
        self.loop.call_soon(self.cbs[uuid], self.services.chars[uuid], bytearray(data))

    async def write_gatt_char(self, char, data, response=True):
        if not self.is_connected:
            raise m.BleakError("Not connected")
        assert len(data) <= self.max_write, f"write of {len(data)} > {self.max_write}"
        self.writes += 1
        self.responses.append((char.uuid, response))
        await asyncio.sleep(0)
        self.on_write(char.uuid, bytes(data))

    # band-side crypto: band encrypts with the phone's decryption key and vice versa
    def derive(self, pn):
        self.pn, self.wn = pn, os.urandom(16)
        okm = HKDF(hashes.SHA256(), 64, salt=pn + self.wn, info=b"miwear-auth").derive(self.key)
        self.phone_dec_key, self.phone_enc_key = okm[0:16], okm[16:32]
        self.phone_dec_nonce, self.phone_enc_nonce = okm[32:36], okm[36:40]

    def band_decrypt(self, data, idx):
        nonce = self.phone_enc_nonce + struct.pack("<II", 0, idx)
        return AESCCM(self.phone_enc_key, tag_length=4).decrypt(nonce, data, None)

    def band_encrypt(self, data):
        nonce = self.phone_dec_nonce + bytes(8)
        return AESCCM(self.phone_dec_key, tag_length=4).encrypt(nonce, data, None)

    def send(self, payload, encrypt=True, chunked=False):
        data = self.band_encrypt(payload) if encrypt else payload
        if chunked or len(data) + 6 > self.max_write:
            size = self.max_write - 2
            self.pending = [data[i:i + size] for i in range(0, len(data), size)]
            self.notify(R, struct.pack("<HBBH", 0, 0, 1, len(self.pending)))
        else:
            self.notify(R, struct.pack("<HBB", 0, 2, 1 if encrypt else 2) + data)

    def on_write(self, uuid, data):
        chunk = struct.unpack_from("<H", data)[0]
        if chunk:
            st = self.rx[uuid]
            st["chunks"][chunk] = data[2:]
            if len(st["chunks"]) == st["total"]:
                self.notify(uuid, b"\x00\x00\x01\x00")
                payload = b"".join(st["chunks"][i] for i in range(1, st["total"] + 1))
                if st["enc"]:
                    if uuid == W:
                        idx, payload = struct.unpack_from("<H", payload)[0], payload[2:]
                    else:
                        idx = 0
                    payload = self.band_decrypt(payload, idx)
                self.on_message(uuid, payload)
            return
        kind = data[2]
        if kind == 0:
            self.rx[uuid] = {"total": struct.unpack_from("<H", data, 4)[0], "enc": data[3], "chunks": {}}
            self.notify(uuid, b"\x00\x00\x01\x01")
        elif kind == 2:
            self.notify(uuid, b"\x00\x00\x03\x00")
            if data[3] == 1:
                idx = struct.unpack_from("<H", data, 4)[0]
                payload = self.band_decrypt(data[6:], idx if uuid == W else 0)
            else:
                payload = data[4:]
            self.on_message(uuid, payload)
        elif kind == 1 and uuid == R:
            if data[3] == 1:
                for n, part in enumerate(self.pending, 1):
                    self.notify(R, struct.pack("<H", n) + part)
            elif data[3] == 0:
                self.pending = None
        elif kind == 3:
            pass

    def on_message(self, uuid, payload):
        pb, get = m.pb, m.pb_get
        if uuid == U:
            total, n = struct.unpack_from("<HH", payload)
            self.parts.append(payload[4:])
            assert n == len(self.parts), (n, len(self.parts))
            if self.drop_after and n == self.drop_after:
                # браслет сохранил всё, что получил, кроме заголовка (тип, md5, размер)
                self.stored += b"".join(self.parts)[22:]
                self.is_connected = False
                self.loop.call_soon(self.on_drop)
                return
            if n == total:
                body = b"".join(self.parts)
                assert struct.unpack("<I", body[-4:])[0] == zlib.crc32(body[:-4]), "crc"
                assert body[0:2] == bytes([0, 32])
                md5, size = body[2:18], struct.unpack_from("<I", body, 18)[0]
                fw = self.stored + body[22:-4]
                assert len(fw) == size and hashlib.md5(fw).digest() == md5, "md5/size"
                self.firmware = fw
            return
        assert uuid == W, uuid
        f = m.pb_parse(payload)
        t, s = f[1][0], f[2][0]
        if (t, s) == (1, 26):
            self.derive(get(payload, 3, 30, 1))
            h = hm(self.phone_dec_key, self.wn + self.pn)
            self.send(m.command(1, 26, (3, pb((31, pb((1, self.wn), (2, h)))))), encrypt=False)
        elif (t, s) == (1, 27):
            ac = get(payload, 3, 32)
            assert get(ac, 1) == hm(self.phone_enc_key, self.pn + self.wn), "phone hmac"
            info = m.pb_parse(self.band_decrypt(get(ac, 2), 0))
            assert info[1] == [0] and info[3] == [b"MacBook"] and info[4] == [224]
            assert struct.unpack("<f", info[2][0])[0] == 34.0
            self.send(m.command(1, 27, (3, pb((8, 1)))), encrypt=self.encrypt_auth_reply)
        elif (t, s) == (2, 2):
            di = pb((1, "SN-TEST-123"), (2, "2.1.8"), (3, ""), (4, "M2239B1"))
            self.send(m.command(2, 2, (4, pb((3, di)))), chunked=True)  # exercise chunked receive
        elif (t, s) == (2, 1):
            self.send(m.command(2, 1, (4, pb((2, pb((1, pb((1, 77), (2, 2)))))))))
        elif (t, s) == (2, 5):
            req = m.pb_parse(get(payload, 4, 16))
            self.install_request = {k: v[0] for k, v in req.items()}
            resp = pb((1, self.install_status)) if self.install_status else b""
            self.send(m.command(2, 5, (4, pb((17, resp)))))
        elif (t, s) == (22, 0):
            req = m.pb_parse(get(payload, 24, 1))
            assert req[1] == [32] and len(req[2][0]) == 16
            self.send(m.command(22, 0, (24, pb((2, pb((2, 0), (4, len(self.stored))))))))
        else:
            raise AssertionError(f"unexpected command {t}/{s}")


async def run(key_band, key_phone, fast=False, resume=0, **kw):
    fw = os.urandom(300_000)
    fake = FakeBand(key_band, stored=fw[:resume], **kw)
    band = m.Band(fake, key_phone, fast=fast)
    await band.setup()
    await band.authenticate()
    info = await band.device_info()
    level = await band.battery()
    seen = []
    await band.install_firmware(fw, "2.3.14", lambda d, t, r: seen.append((d, t, r)))
    return fake, band, info, level, fw, seen


async def main():
    # KDF matches standard HKDF
    c = m.XiaomiCrypto(os.urandom(16))
    wn = os.urandom(16)
    okm = HKDF(hashes.SHA256(), 64, salt=c.phone_nonce + wn, info=b"miwear-auth").derive(c.secret_key)
    try:
        c.derive(wn, b"\x00" * 32)
    except m.FlashError:
        pass
    assert c.dec_key == okm[:16] and c.enc_key == okm[16:32] and c.dec_nonce == okm[32:36] and c.enc_nonce == okm[36:40]
    print("ok  KDF == HKDF-SHA256(info=miwear-auth)")

    # protobuf round trip
    msg = m.pb((1, 2), (2, 300), (3, b"\x01" * 200), (4, 1.5), (5, "тест"))
    f = m.pb_parse(msg)
    assert f[1] == [2] and f[2] == [300] and f[3] == [b"\x01" * 200] and f[5] == ["тест".encode()]
    assert m.pb((1, 0)) == b"\x08\x00"
    print("ok  protobuf encode/decode")

    key = os.urandom(16)
    for mtu, enc_reply in ((185, True), (247, False), (23 + 40, True)):
        fake, band, info, level, fw, seen = await run(key, key, mtu=mtu, encrypt_auth_reply=enc_reply)
        assert info == {"serial": "SN-TEST-123", "firmware": "2.1.8", "model": "M2239B1"}, info
        assert level == 77
        assert fake.firmware == fw
        assert fake.install_request[3] == b"2.3.14" and fake.install_request[4] == hashlib.md5(fw).hexdigest().encode()
        assert seen[-1][0] == seen[-1][1] == len(fw) and all(r == 0 for _, _, r in seen)
        assert all(resp for _, resp in fake.responses), "default mode must write with response"
        print(f"ok  mtu={mtu} auth+info+battery+upload ({len(seen)} parts, {fake.writes} BLE writes)")

    # --fast: загрузка без подтверждения, команды по-прежнему с подтверждением
    fake, band, _, _, fw, seen = await run(key, key, fast=True, mtu=247, upload_no_response=True)
    assert band.fast_writes and fake.firmware == fw
    up = [resp for u, resp in fake.responses if u == U]
    assert up and not any(up), "upload must go without response"
    assert all(resp for u, resp in fake.responses if u != U), "commands must keep response"
    assert fake._backend._peripheral.busy > 0
    print(f"ok  --fast upload without response ({len(up)} writes, waited {fake._backend._peripheral.busy}x)")

    # --fast, но характеристика не умеет писать без подтверждения: обычный режим
    fake, band, _, _, fw, _ = await run(key, key, fast=True)
    assert not band.fast_writes and fake.firmware == fw and all(resp for _, resp in fake.responses)
    print("ok  --fast falls back when write-without-response is missing")

    # продолжение прерванной загрузки (как doUpload в Gadgetbridge: md5 и размер всего файла)
    fake, band, _, _, fw, seen = await run(key, key, fast=True, upload_no_response=True, resume=123_457)
    assert fake.firmware == fw
    assert seen[0][2] == 123_457 and seen[0][0] > 123_457 and seen[-1][0] == len(fw)
    print(f"ok  resume from byte 123457 ({len(seen)} parts)")

    try:
        await run(key, os.urandom(16))
        raise AssertionError("wrong key accepted")
    except m.FlashError as e:
        print("ok  wrong key rejected:", str(e)[:50], "...")

    try:
        await run(key, key, install_status=3)
        raise AssertionError("bad status accepted")
    except m.FlashError as e:
        print("ok  install refusal surfaced:", str(e)[:60], "...")

    assert m.detect_version(bytes([0x60, 0x5A, 0x5A, 0, 0x7E]) + b"V2.3.14abcdefgh" + bytes(10)) is not None
    assert m.version_candidates(b"\x00garbage 2.3.14\x00 1.2.3.4 v10.1.200 ") == ["2.3.14", "10.1.200"]
    print("ok  version helpers")

    # --retry: связь дважды обрывается посреди загрузки, скрипт переподключается и продолжает
    import argparse, tempfile
    fw = os.urandom(300_000)
    path = os.path.join(tempfile.mkdtemp(), "fw.bin")
    open(path, "wb").write(fw)
    st = {"stored": b"", "connects": 0}

    async def fake_connect(args):
        st["connects"] += 1
        if st["connects"] == 3:
            raise m.LinkError("Xiaomi Smart Band 8 не найден.")  # браслет ещё перезапускается
        fake = FakeBand(key, mtu=247, stored=st["stored"], drop_after=40 if st["connects"] < 3 else None,
                        upload_no_response=args.fast)
        band = m.Band(fake, key, fast=args.fast)
        fake.on_drop = lambda: (st.update(stored=fake.stored), band.on_disconnect())
        await band.setup()
        await band.authenticate()
        st["fake"] = fake
        return fake, band

    async def fake_info(band):
        return {"firmware": "1.8.124", "model": "M2239B1", "serial": "x"}, 80

    m.connect, m.print_info, m.RETRY_DELAY = fake_connect, fake_info, 0
    args = argparse.Namespace(file=path, version="2.3.14", announce_version=None, fast=False, retry=2,
                              ignore_battery=False, yes=True)
    await m.cmd_flash(args)
    assert st["fake"].firmware == fw and st["connects"] == 4, st["connects"]
    print("ok  --retry: 2 drops + 1 failed reconnect, upload resumed and completed")

    st.update(stored=b"", connects=0)
    args.retry = 0
    try:
        await m.cmd_flash(args)
        raise AssertionError("drop without --retry must fail")
    except (m.FlashError, m.BleakError) as e:
        assert st["connects"] == 1
        print("ok  without --retry a drop stops with:", str(e)[:40])

    st.update(stored=b"", connects=0)
    args.retry, args.fast = 3, True
    await m.cmd_flash(args)
    up = [resp for u, resp in st["fake"].responses if u == U]
    assert st["fake"].firmware == fw and st["connects"] == 4 and up and not any(up)
    print("ok  --fast --retry: drops survived, upload without response completed")
    print("ALL OK")


asyncio.run(main())
