"""Rejoint slither.io sans navigateur.

Exemples:
  python slither-party.py
  python slither-party.py --name jjj
  python slither-party.py --name jjj --seconds 30
  python slither-party.py --name jjj --server 3619
"""

import argparse
import asyncio
import random
import re
import sys
import time

import requests
import websockets

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36"
)
HEADERS = {"User-Agent": UA}
ORIGIN = "http://slither.com"
CLIENT_VERSION = 291
LOGIN_KIND = 30
CPW = bytes(
    [
        54, 206, 204, 169, 97, 178, 74, 136, 124, 117,
        14, 210, 106, 236, 8, 208, 136, 213, 140, 111,
    ]
)
LIST_URL = "https://slither.io/i80124.txt"


def discover():
    version = CLIENT_VERSION
    kind = LOGIN_KIND
    cpw = CPW
    list_url = LIST_URL
    page = requests.get("https://slither.io", headers=HEADERS, timeout=20)
    page.raise_for_status()
    script = re.search(r"https://slither\.io/s/game\d+\.js", page.text)
    if not script:
        return version, kind, cpw, list_url
    js = requests.get(script.group(0), headers=HEADERS, timeout=20)
    js.raise_for_status()
    text = js.text
    found = re.search(r"https://slither\.io/i\d+\.txt", text)
    if found:
        list_url = found.group(0)
    found = re.search(r"client_version=(\d+)", text)
    if found:
        version = int(found.group(1))
    found = re.search(r"ba\[0\]=115;ba\[1\]=(\d+)", text)
    if found:
        kind = int(found.group(1))
    found = re.search(r"cpw=\[([0-9,]+)\]", text)
    if found:
        raw = bytes(int(part) for part in found.group(1).split(",") if part)
        if len(raw) == 20:
            cpw = raw
    return version, kind, cpw, list_url


def decode_servers(text):
    servers = []
    if not text:
        return servers
    j = 1
    m = 0
    n = 0
    cv = 0
    cav = 0
    ia = []
    i6a = []
    pa = []
    aa = []
    clu = []
    sida = []
    active = False
    while j < len(text):
        v = (ord(text[j]) - 97 - cav) % 26
        j += 1
        cv = cv * 16 + v
        cav += 7
        if n == 1:
            if m == 0:
                active = cv <= 26
                m += 1
            elif m == 1:
                ia.append(cv)
                if len(ia) == 4:
                    m += 1
            elif m == 2:
                i6a.append(cv)
                if len(i6a) == 16:
                    m += 1
            elif m == 3:
                pa.append(cv)
                if len(pa) == 2:
                    m += 1
            elif m == 4:
                aa.append(cv)
                if len(aa) == 2:
                    m += 1
            elif m == 5:
                clu.append(cv)
                if len(clu) == 1:
                    m += 1
            elif m == 6:
                sida.append(cv)
                if len(sida) == 2:
                    po = 0
                    for part in pa:
                        po = po * 256 + part
                    ac = 0
                    for part in aa:
                        ac = ac * 256 + part
                    sid = 0
                    for part in sida:
                        sid = sid * 256 + part
                    for z in (1, 2):
                        if z == 1:
                            ip = ".".join(str(part) for part in ia)
                        elif len(i6a) == 16:
                            groups = []
                            used = False
                            for k in range(0, 16, 2):
                                q = i6a[k] * 256 + i6a[k + 1]
                                if q:
                                    used = True
                                groups.append(format(q, "x"))
                            if not used:
                                break
                            ip = "[" + ":".join(groups) + "]"
                        else:
                            break
                        servers.append(
                            {
                                "ip": ip,
                                "po": po,
                                "ac": ac,
                                "sid": sid,
                                "active": active,
                            }
                        )
                    ia = []
                    i6a = []
                    pa = []
                    aa = []
                    clu = []
                    sida = []
                    m = 0
            cv = 0
            n = 0
        else:
            n += 1
    return servers


def fetch_servers(list_url):
    response = requests.get(list_url, headers=HEADERS, timeout=20)
    response.raise_for_status()
    servers = decode_servers(response.text)
    if not servers:
        raise SystemExit("aucun serveur dans la liste")
    return servers


def prefer_active(servers):
    active = [item for item in servers if item["active"]]
    return active or servers


def choose_servers(servers, ip, port, server_id):
    if server_id:
        picked = [item for item in servers if item["sid"] == server_id]
        if ip:
            picked = [item for item in picked if item["ip"] == ip and (not port or item["po"] == port)]
        if not picked:
            raise SystemExit(f"serveur {server_id} introuvable")
        ipv4 = [item for item in picked if ":" not in item["ip"]]
        ipv6 = [item for item in picked if ":" in item["ip"]]
        return prefer_active(ipv4) + prefer_active(ipv6)
    if ip:
        picked = [item for item in servers if item["ip"] == ip and (not port or item["po"] == port)]
        if not picked and port:
            return [{"ip": ip, "po": port, "ac": 0, "sid": 0, "active": True}]
        if not picked:
            raise SystemExit(f"serveur introuvable: {ip}")
        return picked
    servers = [item for item in servers if item["active"]]
    ipv4 = [item for item in servers if ":" not in item["ip"] and item["ac"] > 20]
    pool = ipv4 or [item for item in servers if item["ac"] > 20] or servers
    random.shuffle(pool)
    return pool


def asciize(name):
    name = name[:24]
    out = bytearray()
    for ch in name:
        code = ord(ch)
        out.append(code if 32 <= code <= 127 else 32)
    return bytes(out)


def login_packet(name, version, kind, cpw, skin=None):
    nick = asciize(name)
    body = bytearray(28 + len(nick))
    body[0] = 115
    body[1] = kind
    body[2] = (version >> 8) & 255
    body[3] = version & 255
    body[4:24] = cpw
    body[24] = random.randrange(9) if skin is None else int(skin) & 255
    body[25] = len(nick)
    body[26 : 26 + len(nick)] = nick
    body[26 + len(nick)] = 0
    body[27 + len(nick)] = 255
    return bytes(body)


def decode_challenge(text):
    out = []
    value = 0
    salt = 23
    pair = 0
    index = 0
    while index < len(text):
        code = text[index]
        index += 1
        if code <= 96:
            code += 32
        code = (code - 97 - salt) % 26
        value = value * 16 + code
        salt += 17
        if pair == 1:
            out.append(chr(value))
            pair = 0
            value = 0
        else:
            pair += 1
    return "".join(out)


def js_mod(value, modulus):
    return value - modulus * int(value / modulus)


def mix_secret(secret):
    data = bytearray(secret)
    carry = 0
    for index, value in enumerate(data):
        base = 0x41
        if value >= 0x61:
            base += 0x20
            value -= 0x20
        value -= 0x41
        if index == 0:
            carry = 3 + value
        mixed = js_mod(value + carry, 26)
        carry += 4 + value
        data[index] = (mixed + base) & 255
    return bytes(data)


def challenge_id(version_text):
    script = decode_challenge(version_text)
    parts = re.findall(r'"([^"\\]*)"', script)
    secret = "".join(parts)
    if len(secret) != 27:
        raise ValueError("reponse du serveur illisible")
    return mix_secret(secret.encode("latin1"))


def iter_packets(data):
    if not data:
        return
    m = 0
    if data[0] >= 32:
        yield data
        return
    while m < len(data):
        if data[m] < 32:
            if m + 2 > len(data):
                return
            length = (data[m] << 8) | data[m + 1]
            m += 2
        else:
            length = data[m] - 32
            m += 1
        end = m + length
        if end > len(data):
            return
        yield data[m:end]
        m = end


def valid_version(text):
    return bool(text) and all(65 <= ord(ch) <= 122 for ch in text)


async def play(server, name, seconds, version, kind, cpw):
    url = f"ws://{server['ip']}:{server['po']}/slither"
    label = f", server {server['sid']}" if server.get("sid") else ""
    print(f"connexion {url} ({server['ac']} joueurs){label}", flush=True)
    headers = {"Origin": ORIGIN, "User-Agent": UA}
    async with websockets.connect(
        url,
        additional_headers=headers,
        max_size=None,
        open_timeout=8,
        ping_interval=None,
        compression=None,
    ) as ws:
        await ws.send(bytes([1]))
        await ws.send(b"c\x00")
        protocol = 2
        playing = False
        announced = False
        server_id = 0
        waiting_pong = False
        last_ping = 0.0
        last_angle = 0.0
        angle = 40
        started = time.monotonic()
        while True:
            now = time.monotonic()
            if seconds and now - started >= seconds:
                print("temps ecoule", flush=True)
                return True
            if not playing and now - started > 8:
                print("pas de partie sur ce serveur", flush=True)
                return False
            try:
                message = await asyncio.wait_for(ws.recv(), timeout=0.2)
            except asyncio.TimeoutError:
                message = None
            if isinstance(message, str):
                message = message.encode("latin1", "replace")
            if message:
                for packet in iter_packets(message):
                    if not packet:
                        continue
                    cmd = packet[0]
                    if cmd == ord("6"):
                        server_version = packet[1:].decode("latin1", "replace")
                        if not valid_version(server_version):
                            print(f"version refusee: {server_version!r}", flush=True)
                            return False
                        await ws.send(challenge_id(packet[1:]))
                        await ws.send(login_packet(name, version, kind, cpw))
                        print(f"pseudo {name} envoye", flush=True)
                    elif cmd == ord("a"):
                        playing = True
                        if len(packet) > 23:
                            protocol = packet[23]
                        if not server_id and len(packet) > 26:
                            server_id = (packet[25] << 8) | packet[26]
                            if server_id:
                                print(f"server {server_id}", flush=True)
                    elif cmd == ord("s") and playing and not announced:
                        announced = True
                        where = f"server {server_id}" if server_id else f"{server['ip']}:{server['po']}"
                        print(f"{name} est en jeu, {where}", flush=True)
                    elif cmd == ord("p"):
                        waiting_pong = False
            now = time.monotonic()
            if playing and not waiting_pong and now - last_ping >= 0.25:
                await ws.send(bytes([251 if protocol >= 5 else 112]))
                waiting_pong = True
                last_ping = now
            if playing and announced and now - last_angle >= 0.1:
                angle = (angle + 8) % 251
                if protocol >= 5:
                    await ws.send(bytes([angle]))
                else:
                    sang = int(16777215 * angle / 250)
                    await ws.send(
                        bytes([101, (sang >> 16) & 255, (sang >> 8) & 255, sang & 255])
                    )
                last_angle = now


async def main_async(name, seconds, ip, port, server_id):
    version, kind, cpw, list_url = discover()
    servers = choose_servers(fetch_servers(list_url), ip, port, server_id)
    print(f"{len(servers)} serveur(s)", flush=True)
    errors = 0
    for server in servers:
        try:
            stayed = await play(server, name, seconds, version, kind, cpw)
        except (OSError, websockets.WebSocketException, asyncio.TimeoutError) as exc:
            errors += 1
            print(f"echec {server['ip']}:{server['po']}: {exc}", flush=True)
            if errors >= 6 and not ip and not server_id:
                break
            continue
        if stayed:
            return
        errors += 1
        if errors >= 6 and not ip and not server_id:
            break
    raise SystemExit("aucune partie rejointe")


def main():
    parser = argparse.ArgumentParser(description="Rejoint slither.io sans navigateur")
    parser.add_argument("--name", default="jjj", help="pseudo, 24 caracteres max")
    parser.add_argument("--seconds", type=float, default=0, help="duree, 0 = jusqu'a Ctrl+C")
    parser.add_argument("--server", type=int, default=0, help="id du serveur, par exemple 3619")
    parser.add_argument("--ip", default="", help="ip du serveur, sinon choix automatique")
    parser.add_argument("--port", type=int, default=0, help="port, avec --ip")
    args = parser.parse_args()
    try:
        asyncio.run(main_async(args.name, args.seconds, args.ip, args.port or None, args.server))
    except KeyboardInterrupt:
        print("arret", flush=True)


if __name__ == "__main__":
    sys.exit(main())
