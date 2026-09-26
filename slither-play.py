"""Joue a slither.io dans une fenetre, avec les vraies requetes du jeu.

La souris dirige le serpent. Le clic gauche accelere.
Les boules et les autres serpents viennent du serveur.

  python slither-play.py --name jjj
  python slither-play.py --name jjj --server 3619
  python slither-play.py --name jjj --count 10 --server 3619
  Tous les serpents de --count utilisent le meme pseudo.
  python slither-play.py --skins
  Les positions des bots sont sur http://127.0.0.1:8765/bots
"""

import argparse
import asyncio
import base64
import ctypes
import importlib.util
import json
import math
import os
import re
import socket
import subprocess
import sys
import threading
import time
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import websockets

ROOT = os.path.dirname(os.path.abspath(__file__))
pygame = None


def load_pygame():
    global pygame
    if pygame is None:
        os.environ["PYGAME_HIDE_SUPPORT_PROMPT"] = "1"
        import pygame as pygame_mod

        pygame = pygame_mod
    return pygame

spec = importlib.util.spec_from_file_location(
    "slither_party", os.path.join(ROOT, "slither-party.py")
)
party = importlib.util.module_from_spec(spec)
spec.loader.exec_module(party)

TAU = math.tau
COLORS = (
    "#5cff4a",
    "#ff5a36",
    "#4ad4ff",
    "#ffe14a",
    "#d44aff",
    "#4a6bff",
    "#ffffff",
    "#ff9a3c",
    "#7dffb2",
    "#ff6b93",
    "#8fd0ff",
    "#e8ff8a",
)


def color_of(cv):
    return COLORS[cv % len(COLORS)]


def u16(data, index):
    return (data[index] << 8) | data[index + 1], index + 2


def u24(data, index):
    return (data[index] << 16) | (data[index + 1] << 8) | data[index + 2], index + 3


class Pilot:
    def __init__(self, name, color, slot):
        self.name = name
        self.color = color
        self.slot = slot
        self.self_id = None
        self.sang = 0
        self.dirty = False
        self.steered = False
        self.boost = None
        self.boosting = False
        self.alive = False
        self.status = "connexion"
        self.hx = 0.0
        self.hy = 0.0
        self.length = 0
        self.sides = {}
        self.proxy = None
        self.manual = False


def pilot_names(base, count):
    count = max(1, int(count))
    nick = (base or "jjj")[:23]
    return [nick] * count


class Game:
    def __init__(self):
        self.lock = threading.Lock()
        self.snakes = {}
        self.foods = {}
        self.food_at = {}
        self.preys = {}
        self.self_id = None
        self.protocol = 2
        self.sector = 300
        self.grd = 0
        self.msl = 42
        self.server_id = 0
        self.rank = 0
        self.player_count = 0
        self.board = []
        self.nmscps = 100
        self.status = "connexion"
        self.sang = 0
        self.dirty = False
        self.steered = False
        self.boost = None
        self.boosting = False
        self.boxes = False
        self.tracers = False
        self.autoplay = False
        self.track = False
        self.rally = False
        self.shield = False
        self.player_xy = None
        self.player_at = 0.0
        self.track_name = ""
        self.track_edit = False
        self.track_xy = None
        self.track_sid = None
        self.name = ""
        self.pilots = []
        self.manual = False
        self.alive = False
        self.quit = False
        self.board_mode = False
        self.deaths = 0
        self.proxy_stats = {}
        self.lfsx = 0
        self.lfsy = 0
        self.lfcv = 0
        self.lfvsx = 0
        self.lfvsy = 0
        self.hx = 0.0
        self.hy = 0.0
        self.length = 0

    def snapshot(self, camx, camy, focus_id=None):
        with self.lock:
            local_ids = {pilot.self_id: pilot for pilot in self.pilots if pilot.self_id is not None}
            focus = None
            if focus_id is not None and focus_id in self.snakes:
                me = self.snakes.get(focus_id)
            else:
                for pilot in self.pilots:
                    if pilot.alive and pilot.self_id in self.snakes and self.snakes[pilot.self_id]["pts"]:
                        focus = pilot
                        break
                me = self.snakes.get(focus.self_id) if focus else None
            pts = list(me["pts"]) if me else []
            locals_out = []
            for pilot in self.pilots:
                snake = self.snakes.get(pilot.self_id) if pilot.self_id is not None else None
                if snake and snake["pts"]:
                    locals_out.append((pilot.name, list(snake["pts"]), pilot.color))
            radius = max(700, self.sector * 2.4)
            others = []
            for sid, snake in self.snakes.items():
                if not snake["pts"] or snake.get("away"):
                    continue
                if focus_id is None and sid in local_ids:
                    continue
                if focus_id is not None and sid == focus_id:
                    continue
                hx, hy = snake["pts"][-1]
                if (hx - camx) ** 2 + (hy - camy) ** 2 > (radius * 1.4) ** 2:
                    continue
                others.append((sid, list(snake["pts"]), snake["cv"], snake["nick"], bool(snake.get("fast"))))
            foods = []
            if self.sector:
                sx0 = int((camx - radius) / self.sector) - 1
                sx1 = int((camx + radius) / self.sector) + 1
                sy0 = int((camy - radius) / self.sector) - 1
                sy1 = int((camy + radius) / self.sector) + 1
                for sx in range(sx0, sx1 + 1):
                    for sy in range(sy0, sy1 + 1):
                        for fid in self.food_at.get((sx, sy), ()):
                            food = self.foods.get(fid)
                            if food:
                                foods.append(food)
            preys = [
                prey
                for prey in self.preys.values()
                if (prey[0] - camx) ** 2 + (prey[1] - camy) ** 2 <= radius ** 2
            ]
            alive_n = sum(1 for pilot in self.pilots if pilot.alive)
            if self.pilots and alive_n:
                status = f"en jeu {alive_n}/{len(self.pilots)}"
            elif any(pilot.status == "Mort" for pilot in self.pilots):
                status = "Mort"
            else:
                status = self.status
            return {
                "pts": pts,
                "locals": locals_out,
                "others": others,
                "status": status,
                "foods": foods,
                "preys": preys,
                "server_id": self.server_id,
                "length": len(pts),
                "sector": self.sector,
                "alive": self.alive,
            }

    def players(self):
        with self.lock:
            rows = []
            for sid, snake in self.snakes.items():
                if not snake["pts"]:
                    continue
                x, y = snake["pts"][-1]
                local_ids = {pilot.self_id for pilot in self.pilots if pilot.self_id is not None}
                rows.append(
                    (
                        sid in local_ids,
                        snake["nick"] or "?",
                        int(x),
                        int(y),
                        len(snake["pts"]),
                        sid,
                    )
                )
            known = {row[1] for row in rows}
            for nick, score, _cv in self.board:
                if nick and nick not in known:
                    rows.append((False, nick, None, None, score, 0))
                    known.add(nick)
            rows.sort(key=lambda row: (-(row[4] or 0), row[1].lower()))
            return rows


def parse_snake(game, pilot, data):
    if len(data) < 3:
        return
    sid, index = u16(data, 1)
    if len(data) - 1 <= 6:
        killed = len(data) > 3 and data[3] == 1
        with game.lock:
            snake = game.snakes.get(sid)
            if killed:
                game.snakes.pop(sid, None)
                if sid == pilot.self_id:
                    pilot.self_id = None
                    pilot.alive = False
                    pilot.status = "Mort"
            elif snake is not None:
                snake["away"] = True
        return
    index += 3 + 1 + 3 + 2 + 3
    if index >= len(data):
        return
    cv = data[index]
    index += 1
    snx, index = u24(data, index)
    sny, index = u24(data, index)
    nick_len = data[index]
    index += 1
    nick = data[index : index + nick_len].decode("latin1", "replace")
    index += nick_len
    if game.protocol >= 11 and index < len(data):
        skin_len = data[index]
        index += 1
        if 0 < skin_len <= 40 and index + skin_len <= len(data):
            index += skin_len
    if game.protocol >= 12 and index < len(data):
        index += 1
    xx = snx / 5
    yy = sny / 5
    pts = []
    started = False
    while index < len(data):
        if not started:
            if index + 5 >= len(data):
                break
            raw_x, index = u24(data, index)
            raw_y, index = u24(data, index)
            xx = raw_x / 5
            yy = raw_y / 5
            started = True
        elif game.protocol >= 15 and index == len(data) - 2:
            iang, index = u16(data, index)
            ang = iang * TAU / 65536
            xx += math.cos(ang) * game.msl
            yy += math.sin(ang) * game.msl
        elif index + 1 < len(data):
            xx += (data[index] - 127) / 2
            yy += (data[index + 1] - 127) / 2
            index += 2
        else:
            break
        pts.append((xx, yy))
    if not pts:
        pts = [(snx / 5, sny / 5)]
    with game.lock:
        taken = {
            other.self_id
            for other in game.pilots
            if other is not pilot and other.self_id is not None
        }
        if sid == pilot.self_id:
            own = True
        elif pilot.self_id is None and sid not in taken and (nick == pilot.name or not nick):
            own = True
        else:
            own = False
        if own:
            pilot.self_id = sid
            pilot.alive = True
            pilot.status = "en jeu"
            if not nick:
                nick = pilot.name
        game.snakes[sid] = {
            "pts": pts[-160:],
            "cv": cv,
            "nick": nick or pilot.name if own else nick,
            "iang": 0,
            "msl": game.msl,
            "away": False,
        }
        if own and pts:
            pilot.hx, pilot.hy = pts[-1]
            pilot.length = len(pts)


def move_snake(game, pilot, cmd, data):
    if len(data) < 2:
        return
    dlen = len(data) - 1
    index = 1
    char = chr(cmd)
    adding = char in "nN+"
    with game.lock:
        protocol = game.protocol
        self_id = pilot.self_id
    own = False
    if protocol >= 15:
        if char in "GN" or (char == "=" and dlen == 6) or (char == "+" and dlen == 9):
            own = True
        else:
            if index + 1 >= len(data):
                return
            sid, index = u16(data, index)
            own = sid == self_id
    elif (char == "g" and dlen == 4) or (char == "G" and dlen == 2) or (
        char == "n" and dlen == 7
    ) or (char == "N" and dlen == 5):
        own = True
    else:
        if index + 1 >= len(data):
            return
        sid, index = u16(data, index)
        own = sid == self_id
    target = self_id if own else sid
    with game.lock:
        snake = game.snakes.get(target)
        if not snake or not snake["pts"]:
            return
        last = snake["pts"][-1]
        msl = snake["msl"]
        try:
            if protocol >= 15 and char in "+=":
                iang, index = u16(data, index)
                xx, index = u16(data, index)
                yy, index = u16(data, index)
                xx = float(xx)
                yy = float(yy)
            elif protocol >= 15:
                short = (char == "G" and dlen == 2) or (char == "N" and dlen == 5) or (
                    char == "g" and dlen == 4
                ) or (char == "n" and dlen == 7)
                if short and index + 1 < len(data):
                    iang, index = u16(data, index)
                else:
                    iang = snake["iang"]
                ang = iang * TAU / 65536
                xx = last[0] + math.cos(ang) * msl
                yy = last[1] + math.sin(ang) * msl
            elif char in "gn":
                xx, index = u16(data, index)
                yy, index = u16(data, index)
                xx = float(xx)
                yy = float(yy)
                iang = snake["iang"]
            else:
                if index + 1 >= len(data):
                    return
                xx = last[0] + data[index] - 128
                yy = last[1] + data[index + 1] - 128
                iang = snake["iang"]
        except IndexError:
            return
        snake["iang"] = iang
        dx = xx - last[0]
        dy = yy - last[1]
        limit = max(80.0, msl * 3)
        if dx * dx + dy * dy > limit * limit:
            snake["pts"][-1] = (xx, yy)
        else:
            if not adding and len(snake["pts"]) > 6:
                snake["pts"].pop(0)
            snake["pts"].append((xx, yy))
        now_tick = time.monotonic()
        previous_tick = snake.get("tick")
        if previous_tick is not None and now_tick - previous_tick > 0.004:
            gap = now_tick - previous_tick
            rush = snake.get("rush", gap) * 0.65 + gap * 0.35
            snake["rush"] = rush
            snake["fast"] = rush < (0.07 if snake.get("fast") else 0.04)
        snake["tick"] = now_tick
        if len(snake["pts"]) > 160:
            del snake["pts"][:-160]
        if own:
            pilot.hx, pilot.hy = xx, yy
            pilot.length = len(snake["pts"])
            pilot.alive = True


def add_foods(game, items):
    if not items:
        return
    with game.lock:
        foods = game.foods
        at = game.food_at
        for fid, xx, yy, rad, cv, sx, sy in items:
            foods[fid] = (xx, yy, rad, cv)
            bucket = at.get((sx, sy))
            if bucket is None:
                bucket = set()
                at[(sx, sy)] = bucket
            bucket.add(fid)


def score_tables(nmscps):
    if nmscps < 2:
        nmscps = 2
    scales = []
    steps = [0.0]
    for index in range(nmscps + 1):
        if index >= nmscps:
            scales.append(scales[-1])
        else:
            scales.append((1 - index / nmscps) ** 2.25)
        if index:
            steps.append(steps[-1] + 1 / scales[index - 1])
    return scales, steps


def parse_board(game, data):
    if len(data) < 6:
        return
    index = 1
    try:
        _my_pos = data[index]
        index += 1
        rank, index = u16(data, index)
        count, index = u16(data, index)
        scales, steps = score_tables(game.nmscps)
        rows = []
        while index + 6 < len(data):
            length, index = u16(data, index)
            fam, index = u24(data, index)
            cv = data[index] % 9
            index += 1
            nick_len = data[index]
            index += 1
            nick = data[index : index + nick_len].decode("latin1", "replace")
            index += nick_len
            if length < len(steps) and scales[min(length, len(scales) - 1)]:
                score = int((steps[length] + (fam / 16777215) / scales[min(length, len(scales) - 1)] - 1) * 15 - 5)
            else:
                score = length
            rows.append((nick, max(score, 0), cv))
        with game.lock:
            game.rank = rank
            game.player_count = count
            game.board = rows
    except IndexError:
        return


def parse_food(game, cmd, data):
    char = chr(cmd)
    if len(data) < 4:
        return
    sector = game.sector or 1
    step = sector / 256
    index = 1
    dlen = len(data) - 1
    try:
        if char == "F" and game.protocol >= 14:
            sx = data[index]
            sy = data[index + 1]
            index += 2
            found = []
            base_x = sx * sector
            base_y = sy * sector
            while index + 3 < len(data):
                cv = data[index]
                rx = data[index + 1]
                ry = data[index + 2]
                rad = data[index + 3] / 5
                index += 4
                fid = (sx << 24) | (sy << 16) | (rx << 8) | ry
                found.append((fid, base_x + rx * step, base_y + ry * step, rad, cv, sx, sy))
            add_foods(game, found)
            return
        if char in "bf" and game.protocol >= 14:
            if dlen >= 5:
                sx = data[index]
                sy = data[index + 1]
                index += 2
                game.lfsx, game.lfsy = sx, sy
            else:
                sx, sy = game.lfsx, game.lfsy
            rx = data[index]
            ry = data[index + 1]
            index += 2
            if dlen in (4, 6) and index < len(data):
                cv = data[index]
                index += 1
                game.lfcv = cv
            else:
                cv = game.lfcv
            rad = data[index] / 5 if index < len(data) else 2
            xx = sx * sector + rx * step
            yy = sy * sector + ry * step
            fid = (sx << 24) | (sy << 16) | (rx << 8) | ry
            add_foods(game, [(fid, xx, yy, rad, cv, sx, sy)])
            return
        if char in "cC<":
            if (char == "c" and dlen == 2) or (char == "<" and dlen == 4) or (
                char == "C" and dlen == 2
            ):
                sx, sy = game.lfvsx, game.lfvsy
            else:
                sx = data[index]
                sy = data[index + 1]
                index += 2
                game.lfvsx, game.lfvsy = sx, sy
            rx = data[index]
            ry = data[index + 1]
            fid = (sx << 24) | (sy << 16) | (rx << 8) | ry
            with game.lock:
                game.foods.pop(fid, None)
                bucket = game.food_at.get((sx, sy))
                if bucket:
                    bucket.discard(fid)
            return
        if char == "w" and game.protocol >= 8 and len(data) >= 3:
            sx = data[1]
            sy = data[2]
            with game.lock:
                for fid in game.food_at.pop((sx, sy), ()):
                    game.foods.pop(fid, None)
            return
        if char == "y" and len(data) > 8:
            pid, index = u16(data, 1)
            if dlen == 2:
                with game.lock:
                    game.preys.pop(pid, None)
                return
            if dlen == 4:
                with game.lock:
                    game.preys.pop(pid, None)
                return
            cv = data[index]
            index += 1
            xx, index = u24(data, index)
            yy, index = u24(data, index)
            rad = data[index] / 5
            with game.lock:
                game.preys[pid] = (xx / 5, yy / 5, rad, cv)
    except IndexError:
        return


def handle(game, pilot, packet):
    if not packet:
        return
    cmd = packet[0]
    if cmd == ord("a") and len(packet) > 26:
        with game.lock:
            game.grd = (packet[1] << 16) | (packet[2] << 8) | packet[3] or game.grd
            game.sector = (packet[6] << 8) | packet[7] or game.sector
            game.nmscps = (packet[4] << 8) | packet[5] or game.nmscps
            game.protocol = packet[23]
            game.msl = packet[24] or game.msl
            game.server_id = (packet[25] << 8) | packet[26]
            game.status = "en jeu"
        return
    if cmd == ord("s"):
        try:
            parse_snake(game, pilot, packet)
        except (IndexError, ValueError):
            return
        return
    if cmd in b"gnGN+=":
        try:
            move_snake(game, pilot, cmd, packet)
        except (IndexError, ValueError):
            return
        return
    if cmd in b"FbfcC<wy":
        parse_food(game, cmd, packet)
        return
    if cmd == ord("l"):
        parse_board(game, packet)
        return
    if cmd == ord("v") and len(packet) == 2 and packet[1] in (0, 1):
        with game.lock:
            if pilot.alive:
                pilot.alive = False
                pilot.self_id = None
                pilot.status = "Mort"


SKINS = (
    (0, "violet"),
    (1, "bleu clair"),
    (2, "turquoise"),
    (3, "vert"),
    (4, "jaune"),
    (5, "orange"),
    (6, "rose"),
    (7, "rouge"),
    (8, "magenta"),
    (9, "rouge et blanc"),
    (10, "blanc bleu rouge"),
    (11, "gris rouge or"),
    (12, "rouge blanc vert"),
    (13, "bleu blanc rouge"),
    (14, "blanc et rouge"),
    (15, "arc-en-ciel"),
    (16, "bleu et jaune"),
    (17, "blanc et bleu"),
    (18, "rouge et blanc"),
    (19, "blanc"),
    (20, "vert et violet"),
    (21, "vert bleu jaune"),
    (22, "orange blanc vert"),
    (23, "bleu jaune rouge"),
    (24, "antenne cyan"),
    (25, "antenne orange"),
    (26, "gris"),
    (27, "cyclope"),
    (28, "jaune vert rouge"),
    (29, "gris et jaune"),
    (30, "bleu et or"),
    (31, "bleu"),
    (32, "bleu fonce"),
    (33, "or et rouge"),
    (34, "bandes multicolores"),
    (35, "rouge blanc rose"),
    (36, "bleu blanc violet"),
    (37, "couronne"),
    (38, "jaune dore"),
    (39, "eclair"),
    (40, "yeux mobiles"),
    (41, "gros yeux"),
    (42, "play"),
    (43, "rouge sombre"),
    (44, "yeux gris"),
    (45, "feuille"),
    (46, "suisse"),
    (47, "moldavie"),
    (48, "vietnam"),
    (49, "argentine"),
    (50, "jaune bleu rouge"),
    (51, "rouge blanc bleu"),
    (52, "rouge et jaune"),
    (53, "bleu vif"),
    (54, "rouge vif"),
    (55, "jaune vif"),
    (56, "orange vif"),
    (57, "magenta vif"),
    (58, "vert vif"),
    (59, "film"),
    (60, "drez"),
    (61, "arc-en-ciel 2"),
    (62, "bonk"),
    (63, "noir"),
    (64, "jaune pale"),
)


PROXY_FILE = os.path.join(ROOT, "proxy.txt")
RECORD_FILE = os.path.join(ROOT, "bot-record.json")
IP_LINE = re.compile(r"^\d{1,3}(?:\.\d{1,3}){3}$")
_record_lock = threading.Lock()
_record_name = ""
_record_size = 0


def load_record():
    global _record_name, _record_size
    try:
        with open(RECORD_FILE, encoding="utf-8") as handle:
            data = json.load(handle)
        _record_name = str(data.get("name") or "")
        _record_size = int(data.get("size") or 0)
    except (OSError, ValueError, TypeError, json.JSONDecodeError):
        _record_name, _record_size = "", 0


def note_record(name, size):
    global _record_name, _record_size
    try:
        size = int(size)
    except (TypeError, ValueError):
        return
    if size <= _record_size:
        return
    with _record_lock:
        if size <= _record_size:
            return
        _record_name = str(name or "")
        _record_size = size
        try:
            with open(RECORD_FILE, "w", encoding="utf-8") as handle:
                json.dump({"name": _record_name, "size": _record_size}, handle)
        except OSError:
            pass


load_record()


def load_proxies(path):
    try:
        lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    except OSError:
        return []
    proxies = []
    index = 0
    while index < len(lines):
        host = lines[index].strip()
        if IP_LINE.match(host) and index + 3 < len(lines) and lines[index + 1].strip().isdigit():
            proxies.append(
                {
                    "host": host,
                    "port": int(lines[index + 1].strip()),
                    "user": lines[index + 2].strip(),
                    "password": lines[index + 3].strip(),
                }
            )
            index += 4
        else:
            index += 1
    return proxies


async def open_proxy_socket(proxy, host, port):
    last_error = None
    loop = asyncio.get_running_loop()
    token = base64.b64encode(f"{proxy['user']}:{proxy['password']}".encode()).decode()
    target = f"{host}:{port}"
    request = (
        f"CONNECT {target} HTTP/1.1\r\n"
        f"Host: {target}\r\n"
        f"Proxy-Authorization: Basic {token}\r\n"
        f"Connection: keep-alive\r\n"
        f"\r\n"
    ).encode()
    for _attempt in range(4):
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.setblocking(False)
        try:
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
            await asyncio.wait_for(loop.sock_connect(sock, (proxy["host"], proxy["port"])), 12)
            await loop.sock_sendall(sock, request)
            data = b""
            while b"\r\n\r\n" not in data:
                chunk = await asyncio.wait_for(loop.sock_recv(sock, 1), 12)
                if not chunk:
                    raise OSError(f"proxy {proxy['host']} ferme")
                data += chunk
                if len(data) > 8192:
                    break
            status = data.split(b"\r\n", 1)[0]
            if b" 200 " not in status:
                raise OSError(f"proxy {proxy['host']} {status.decode('latin1', 'replace').strip()}")
            return sock
        except Exception as exc:
            last_error = exc
            sock.close()
            await asyncio.sleep(0.05)
    raise last_error or OSError(f"proxy {proxy['host']} injoignable")


async def proxy_answers(proxy, host, port):
    loop = asyncio.get_running_loop()
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.setblocking(False)
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        await asyncio.wait_for(loop.sock_connect(sock, (proxy["host"], proxy["port"])), 8)
        token = base64.b64encode(f"{proxy['user']}:{proxy['password']}".encode()).decode()
        target = f"{host}:{port}"
        request = (
            f"CONNECT {target} HTTP/1.1\r\n"
            f"Host: {target}\r\n"
            f"Proxy-Authorization: Basic {token}\r\n"
            f"\r\n"
        ).encode()
        await loop.sock_sendall(sock, request)
        data = bytearray()

        async def read_header():
            while b"\r\n\r\n" not in data and len(data) <= 8192:
                chunk = await loop.sock_recv(sock, 1)
                if not chunk:
                    return False
                data.extend(chunk)
            return b" 200 " in bytes(data).split(b"\r\n", 1)[0]

        return await asyncio.wait_for(read_header(), 8)
    except Exception:
        return False
    finally:
        sock.close()


async def working_proxies(game, proxies, host, port, needed):
    good = []
    gate = asyncio.Semaphore(40)

    async def one(proxy):
        if game.quit:
            return
        async with gate:
            with game.lock:
                filled = len(good) >= needed
            if filled or game.quit:
                return
            ok = await proxy_answers(proxy, host, port)
            with game.lock:
                if ok and len(good) < needed:
                    good.append(proxy)
                elif not ok:
                    stat = game.proxy_stats.setdefault(proxy["host"], {"ok": 0, "fail": 0})
                    stat["fail"] += 1
                game.status = f"test proxys {len(good)}/{needed}"

    await asyncio.gather(*(one(proxy) for proxy in proxies))
    return good


def skin_name(skin):
    for number, name in SKINS:
        if number == skin:
            return name
    return ""


async def session(game, pilot, server, version, kind, cpw, skin=None):
    name = pilot.name
    url = f"ws://{server['ip']}:{server['po']}/slither"
    label = f", server {server['sid']}" if server.get("sid") else ""
    proxy = pilot.proxy
    via = f" via {proxy['host']}" if proxy else ""
    if not game.board_mode:
        print(f"connexion {url} ({server['ac']} joueurs){label}{via}", flush=True)
    headers = {"Origin": party.ORIGIN, "User-Agent": party.UA}
    owned = None
    try:
        kwargs = {
            "additional_headers": headers,
            "max_size": None,
            "open_timeout": 15,
            "ping_interval": None,
            "compression": None,
        }
        if proxy:
            owned = await open_proxy_socket(proxy, server["ip"], server["po"])
            kwargs["sock"] = owned
        async with websockets.connect(url, **kwargs) as ws:
            owned = None
            await ws.send(bytes([1]))
            await ws.send(b"c\x00")
            waiting_pong = False
            last_ping = asyncio.get_running_loop().time()
            last_angle = 0.0
            started = last_ping
            seen = False
            told = False
            setup = False
            last_boost = 0.0
            while not game.quit:
                now = asyncio.get_running_loop().time()
                with game.lock:
                    alive = pilot.alive
                    protocol = game.protocol
                if not alive and now - started > 25 and game.server_id == 0:
                    if not game.board_mode:
                        print("pas de partie sur ce serveur", flush=True)
                    return False
                try:
                    message = await asyncio.wait_for(ws.recv(), timeout=0.008)
                except asyncio.TimeoutError:
                    message = None
                if isinstance(message, str):
                    message = message.encode("latin1", "replace")
                if message:
                    for packet in party.iter_packets(message):
                        if not packet:
                            continue
                        if packet[0] == ord("6"):
                            text = packet[1:].decode("latin1", "replace")
                            if not party.valid_version(text):
                                return False
                            await ws.send(party.challenge_id(packet[1:]))
                            await ws.send(party.login_packet(name, version, kind, cpw, skin))
                            label = f", skin {skin} {skin_name(skin)}".rstrip() if skin is not None else ""
                            if not game.board_mode:
                                print(f"pseudo {name} envoye{label}", flush=True)
                        elif packet[0] == ord("p"):
                            waiting_pong = False
                        else:
                            if packet[0] == ord("a"):
                                setup = True
                            handle(game, pilot, packet)
                with game.lock:
                    if game.server_id and not told:
                        told = True
                        if not game.board_mode:
                            print(f"server {game.server_id}", flush=True)
                    if pilot.alive and not seen:
                        seen = True
                        if pilot.proxy:
                            stat = game.proxy_stats.setdefault(pilot.proxy["host"], {"ok": 0, "fail": 0})
                            stat["ok"] += 1
                        if not game.board_mode:
                            print(f"{name} est en jeu, server {game.server_id}", flush=True)
                    sang = pilot.sang
                    dirty = pilot.dirty
                    steered = pilot.steered
                    boost = pilot.boost
                    boosting = pilot.boosting
                    pilot.dirty = False
                    pilot.boost = None
                    dead = pilot.status == "Mort"
                    alive = pilot.alive
                    protocol = game.protocol
                if dead:
                    with game.lock:
                        game.deaths += 1
                    if not game.board_mode:
                        print("mort", flush=True)
                    try:
                        await ws.close()
                    except websockets.WebSocketException:
                        pass
                    return "dead"
                if alive and steered and (dirty or now - last_angle >= 0.016):
                    await ws.send(bytes([sang]))
                    last_angle = now
                if boost is not None:
                    await ws.send(bytes([boost]))
                    last_boost = now
                elif alive and boosting and now - last_boost >= 0.2:
                    await ws.send(bytes([253]))
                    last_boost = now
                if setup and not waiting_pong and now - last_ping >= 0.25:
                    await ws.send(bytes([251 if protocol >= 5 else 112]))
                    waiting_pong = True
                    last_ping = now
                elif setup and waiting_pong and now - last_ping >= 1.0:
                    waiting_pong = False
            return True
    finally:
        if owned is not None:
            owned.close()


async def net_main(game, names, server_id, skin=None):
    version, kind, cpw, list_url = party.discover()
    colors = (ME,) + PALETTE
    game.pilots = [Pilot(nick, colors[index % len(colors)], index) for index, nick in enumerate(names)]
    game.name = names[0]
    proxies = load_proxies(PROXY_FILE)
    if not proxies and not game.board_mode:
        print("pas de proxy", flush=True)

    def pick_server():
        found = party.choose_servers(party.fetch_servers(list_url), "", None, server_id)
        if server_id:
            found = found[:1]
        return found[0] if found else None

    try:
        server = await asyncio.to_thread(pick_server)
    except SystemExit as exc:
        with game.lock:
            game.status = str(exc)
        return
    if server is None:
        if not game.board_mode:
            print("serveur introuvable", flush=True)
        return
    if proxies:
        needed = max(1, (len(game.pilots) + 2) // 3)
        with game.lock:
            game.status = f"test proxys 0/{needed}"
        good = await working_proxies(game, proxies, server["ip"], server["po"], needed)
        if game.quit:
            return
        if not good:
            with game.lock:
                game.status = "aucun proxy ne repond"
            if not game.board_mode:
                print("aucun proxy ne repond", flush=True)
            return
        for pilot in game.pilots:
            pilot.proxy = good[(pilot.slot // 3) % len(good)]
        if not game.board_mode:
            print(f"{len(good)} proxys repondent, 3 joueurs par ip", flush=True)
        with game.lock:
            game.status = "connexion"

    async def pilot_loop(pilot):
        while not game.quit:
            with game.lock:
                pilot.self_id = None
                pilot.alive = False
                pilot.status = "connexion"
                pilot.steered = False
                game.server_id = server.get("sid") or game.server_id
                game.status = "connexion"
            try:
                await session(game, pilot, server, version, kind, cpw, skin)
            except (OSError, websockets.WebSocketException, asyncio.TimeoutError) as exc:
                if pilot.proxy:
                    with game.lock:
                        stat = game.proxy_stats.setdefault(pilot.proxy["host"], {"ok": 0, "fail": 0})
                        stat["fail"] += 1
                if not game.board_mode:
                    via = f" via {pilot.proxy['host']}" if pilot.proxy else ""
                    print(f"echec {pilot.name}{via} {server['ip']}:{server['po']}: {type(exc).__name__}: {exc}", flush=True)
            if game.quit:
                return
            with game.lock:
                died = pilot.status == "Mort"
            if not died:
                await asyncio.sleep(0.08)

    async def drive_loop():
        while not game.quit:
            if game.board_mode:
                for pilot in list(game.pilots):
                    if pilot.alive and not pilot.manual:
                        autoplay(game, pilot)
            await asyncio.sleep(0.05)

    driver = asyncio.create_task(drive_loop())
    try:
        await asyncio.gather(*(pilot_loop(pilot) for pilot in game.pilots))
    finally:
        driver.cancel()


def network(game, names, server_id, skin=None):
    try:
        asyncio.run(net_main(game, names, server_id, skin))
    except Exception as exc:
        with game.lock:
            game.status = str(exc)


BG = (22, 22, 40)
PALETTE = (
    (92, 255, 74),
    (255, 90, 54),
    (74, 212, 255),
    (255, 225, 74),
    (212, 74, 255),
    (74, 107, 255),
    (255, 255, 255),
    (255, 154, 60),
    (125, 255, 178),
    (255, 107, 147),
    (143, 208, 255),
    (232, 255, 138),
)
FRAME = 1 / 120
ME = (184, 255, 154)


def pane_at(pos, width, height, count):
    cols, rows = pane_grid(count, width, height)
    cell_w = width / cols
    cell_h = height / rows
    col = min(cols - 1, max(0, int(pos[0] / cell_w))) if cell_w else 0
    row = min(rows - 1, max(0, int(pos[1] / cell_h))) if cell_h else 0
    return min(count - 1, row * cols + col)


def pane_grid(count, width, height):
    count = max(1, count)
    if count == 1:
        return 1, 1
    best = None
    for cols in range(1, count + 1):
        rows = math.ceil(count / cols)
        cell_w = width / cols
        cell_h = height / rows
        ratio = cell_w / max(cell_h, 1)
        empty = cols * rows - count
        score = abs(math.log(ratio)) + empty * 0.35
        if best is None or score < best[0]:
            best = (score, cols, rows)
    return best[1], best[2]


def smooth_points(shown, target, alpha):
    if shown and target:
        dx = shown[-1][0] - target[-1][0]
        dy = shown[-1][1] - target[-1][1]
        if dx * dx + dy * dy > 250 * 250:
            return [[x, y] for x, y in target]
    if not shown or abs(len(shown) - len(target)) > 1:
        return [[x, y] for x, y in target]
    if len(target) == len(shown) + 1:
        shown.append(shown[-1][:])
    elif len(target) + 1 == len(shown):
        shown.pop(0)
    for point, (tx, ty) in zip(shown, target):
        point[0] += (tx - point[0]) * alpha
        point[1] += (ty - point[1]) * alpha
    return shown


class View:
    def __init__(self):
        self.shown = {}
        self.camx = None
        self.camy = None
        self.last = time.perf_counter()
        self.fps_t = self.last
        self.frames = 0
        self.fps = 0.0
        self.font = pygame.font.SysFont("arial", 18)
        self.small = pygame.font.SysFont("arial", 15)
        self.hud_text = ""
        self.hud_img = None
        self.hint = self.small.render(
            "souris pour diriger, clic pour accelerer, molette pour le zoom",
            True,
            (154, 160, 181),
        )
        self.zoom = 1.0
        self.cams = {}

    def follow(self, key, pts, alpha):
        if not pts:
            return self.cams.get(key, (0.0, 0.0))
        hx, hy = pts[-1]
        cam = self.cams.get(key)
        if cam is None:
            cam = [hx, hy]
            self.cams[key] = cam
        else:
            cam[0] += (hx - cam[0]) * alpha
            cam[1] += (hy - cam[1]) * alpha
        return cam

    def project_chain(self, pts, key, alpha, scale, origin_x, origin_y, camx, camy):
        shown = smooth_points(self.shown.get(key), pts, alpha)
        self.shown[key] = shown
        return [
            (origin_x + (x - camx) * scale, origin_y + (y - camy) * scale)
            for x, y in shown
        ]

    def draw_pov(self, screen, game, pilot, rect, alpha, cam_alpha):
        screen.set_clip(rect)
        pygame.draw.rect(screen, BG, rect)
        origin_x = rect.x + rect.w / 2
        origin_y = rect.y + rect.h / 2
        focus = pilot.self_id if pilot and pilot.self_id is not None else None
        hx = pilot.hx if pilot else 0.0
        hy = pilot.hy if pilot else 0.0
        state = game.snapshot(hx, hy, focus)
        pts = state["pts"] if focus is not None else []
        camx, camy = self.follow(pilot.slot if pilot else "solo", pts, cam_alpha)
        view = max(80, state["sector"] * 2.6) / max(self.zoom, 0.000001)
        scale = min(rect.w, rect.h) / view
        margin = 16
        for xx, yy, rad, cv in state["foods"]:
            px = origin_x + (xx - camx) * scale
            py = origin_y + (yy - camy) * scale
            if px < rect.left - margin or py < rect.top - margin or px > rect.right + margin or py > rect.bottom + margin:
                continue
            pygame.draw.circle(screen, PALETTE[cv % len(PALETTE)], (px, py), max(2, rad * scale))
        for xx, yy, rad, cv in state["preys"]:
            px = origin_x + (xx - camx) * scale
            py = origin_y + (yy - camy) * scale
            pygame.draw.circle(screen, PALETTE[cv % len(PALETTE)], (px, py), max(3, rad * scale))
        for sid, body, cv, nick, _fast in state["others"]:
            chain = self.project_chain(body, sid, alpha, scale, origin_x, origin_y, camx, camy)
            draw_body(screen, chain, PALETTE[cv % len(PALETTE)], 7)
            if game.boxes:
                draw_box(screen, chain)
            if game.tracers and chain:
                pygame.draw.line(screen, (255, 255, 255), (origin_x, origin_y), chain[-1], 1)
            if nick and chain:
                label = self.small.render(nick, True, (255, 255, 255))
                screen.blit(label, (chain[-1][0] - label.get_width() / 2, chain[-1][1] - 18))
        if pts:
            color = pilot.color if pilot else ME
            chain = self.project_chain(pts, ("me", pilot.slot if pilot else 0), alpha, scale, origin_x, origin_y, camx, camy)
            draw_body(screen, chain, color, 10)
            if game.boxes:
                draw_box(screen, chain)
        name = pilot.name if pilot else ""
        status = pilot.status if pilot else state["status"]
        label = self.small.render(f"{name}  {status}  {pilot.length if pilot else 0}", True, (255, 255, 255))
        screen.blit(label, (rect.x + 8, rect.y + 6))
        screen.set_clip(None)

    def render(self, screen, game):
        now = time.perf_counter()
        dt = min(0.05, now - self.last)
        self.last = now
        self.frames += 1
        if now - self.fps_t >= 0.5:
            self.fps = self.frames / (now - self.fps_t)
            self.frames = 0
            self.fps_t = now
        width, height = screen.get_size()
        screen.fill(BG)
        alpha = min(1.0, 1 - math.exp(-dt * 22))
        cam_alpha = min(1.0, 1 - math.exp(-dt * 30))
        pilots = game.pilots or [None]
        cols, rows = pane_grid(len(pilots), width, height)
        cell_w = width / cols
        cell_h = height / rows
        for index, pilot in enumerate(pilots):
            col = index % cols
            row = index // cols
            x = int(col * cell_w)
            y = int(row * cell_h)
            pane_w = int(width - x) if col == cols - 1 else int((col + 1) * cell_w) - x
            pane_h = int(height - y) if row == rows - 1 else int((row + 1) * cell_h) - y
            rect = pygame.Rect(x, y, pane_w, pane_h)
            self.draw_pov(screen, game, pilot, rect, alpha, cam_alpha)
            pygame.draw.rect(screen, (48, 52, 70), rect, 2)
        title = f"{self.fps:.0f} fps"
        if title != self.hud_text:
            self.hud_text = title
            self.hud_img = self.font.render(title, True, (255, 255, 255))
        screen.blit(self.hud_img, (width - self.hud_img.get_width() - 12, 8))


def draw_box(screen, chain):
    if len(chain) < 1:
        return
    xs = [point[0] for point in chain]
    ys = [point[1] for point in chain]
    pad = 10
    rect = pygame.Rect(min(xs) - pad, min(ys) - pad, max(xs) - min(xs) + pad * 2, max(ys) - min(ys) + pad * 2)
    pygame.draw.rect(screen, (255, 255, 255), rect, 2)


def draw_body(screen, chain, color, width):
    if len(chain) < 2:
        return
    chunk = [chain[0]]
    limit = 70 * 70
    for x, y in chain[1:]:
        px, py = chunk[-1]
        if (x - px) ** 2 + (y - py) ** 2 > limit:
            if len(chunk) >= 2:
                pygame.draw.lines(screen, color, False, chunk, width)
            chunk = [(x, y)]
        else:
            chunk.append((x, y))
    if len(chunk) >= 2:
        pygame.draw.lines(screen, color, False, chunk, width)
    hx, hy = chain[-1]
    pygame.draw.circle(screen, color, (hx, hy), width // 2 + 2)
    if width >= 12:
        pygame.draw.circle(screen, (255, 255, 255), (hx, hy), width // 2 + 2, 1)


def set_drive(game, pilot, ang, boost):
    if ang < 0:
        ang += TAU
    sang = int(251 * ang / TAU) % 251
    if sang > 250:
        sang = 250
    with game.lock:
        if sang != pilot.sang:
            pilot.sang = sang
            pilot.dirty = True
            pilot.steered = True
        if boost != pilot.boosting:
            pilot.boosting = boost
            pilot.boost = 253 if boost else 254


def path_blocked(others, hx, hy, tx, ty):
    dx, dy = tx - hx, ty - hy
    dist = math.hypot(dx, dy) or 1.0
    for row in others:
        other = row[1]
        if not other:
            continue
        if math.hypot(other[-1][0] - hx, other[-1][1] - hy) > 800:
            continue
        for x, y in other[:-1:3]:
            along = ((x - hx) * dx + (y - hy) * dy) / dist
            if along <= 0 or along >= dist:
                continue
            if abs((x - hx) * dy - (y - hy) * dx) / dist < 28:
                return True
    return False


def death_feast(foods, preys, others, hx, hy, length):
    foods_l = []
    for xx, yy, rad, _cv in foods:
        if rad > 0 and math.hypot(xx - hx, yy - hy) <= 1500:
            foods_l.append((xx, yy, rad))
    preys_l = [(xx, yy, max(float(rad), 10.0)) for xx, yy, rad, _cv in preys if math.hypot(xx - hx, yy - hy) <= 1500]
    pieces = list(preys_l)
    left = set(range(len(foods_l)))
    reach2 = 200 * 200
    while left:
        start = left.pop()
        group_i = [start]
        stack = [start]
        while stack:
            current = stack.pop()
            cx, cy = foods_l[current][0], foods_l[current][1]
            near = [other for other in left if (foods_l[other][0] - cx) ** 2 + (foods_l[other][1] - cy) ** 2 <= reach2]
            for other in near:
                left.remove(other)
                stack.append(other)
                group_i.append(other)
        group = [foods_l[index] for index in group_i]
        mass = sum(item[2] for item in group)
        top = max(item[2] for item in group)
        if len(group) >= 7 or mass >= 18 or top >= 6:
            pieces.extend(group)
    if preys_l:
        for xx, yy, rad in foods_l:
            if any((xx - px) ** 2 + (yy - py) ** 2 <= 220 * 220 for px, py, _rad in preys_l):
                pieces.append((xx, yy, rad))
    if not pieces:
        return None

    def dist_of(item):
        return math.hypot(item[0] - hx, item[1] - hy) or 1.0

    nearest = min(pieces, key=dist_of)
    near_dist = dist_of(nearest)
    if near_dist < 260:
        pool = [item for item in pieces if dist_of(item) < near_dist + 150]
        under = [item for item in pool if dist_of(item) < 55]
        target = min(under, key=dist_of) if under else max(pool, key=lambda item: item[2])
    else:
        target = max(pieces, key=lambda item: item[2])
    dx, dy = target[0] - hx, target[1] - hy
    dist = math.hypot(dx, dy) or 1.0
    blocked = path_blocked(others, hx, hy, target[0], target[1])
    boost = length > 8 and not blocked and 25 < dist < 780
    return (dx / dist, dy / dist, True, boost, dist)


def meal_plan(foods, preys, others, hx, hy, length):
    nearby = []
    for xx, yy, rad, _cv in foods:
        dist = math.hypot(xx - hx, yy - hy)
        if rad > 0 and dist <= 1400:
            nearby.append((xx, yy, rad, dist))
    for xx, yy, rad, _cv in preys:
        dist = math.hypot(xx - hx, yy - hy)
        if dist <= 1400:
            nearby.append((xx, yy, max(rad, 8.0), dist))
    if not nearby:
        return None
    clusters = []
    for xx, yy, rad, _dist in sorted(nearby, key=lambda item: -item[2]):
        placed = False
        for cluster in clusters:
            if (xx - cluster["seedx"]) ** 2 + (yy - cluster["seedy"]) ** 2 > 180 * 180:
                continue
            cluster["pts"].append((xx, yy, rad))
            cluster["mass"] += rad
            if rad > cluster["top"]:
                cluster["top"] = rad
                cluster["tx"] = xx
                cluster["ty"] = yy
            placed = True
            break
        if not placed:
            clusters.append(
                {
                    "seedx": xx,
                    "seedy": yy,
                    "pts": [(xx, yy, rad)],
                    "mass": rad,
                    "top": rad,
                    "tx": xx,
                    "ty": yy,
                }
            )
    best = None
    best_rank = None
    for cluster in clusters:
        mass = cluster["mass"]
        top = cluster["top"]
        cx, cy = cluster["tx"], cluster["ty"]
        dx, dy = cx - hx, cy - hy
        dist = math.hypot(dx, dy) or 1.0
        blocked = path_blocked(others, hx, hy, cx, cy)
        gros = top >= 4 or mass >= 12 or len(cluster["pts"]) >= 6
        score = (top * top) * 80 + mass * 18 - dist * 0.35
        rank = (0 if not blocked else 1, -score)
        if best_rank is not None and rank >= best_rank:
            continue
        pile_boost = gros and not blocked and length > 14 and 40 < dist < 560
        best_rank = rank
        best = (dx / dist, dy / dist, gros, pile_boost, dist)
    return best


BINS = 16
ARC = TAU / BINS


def bin_of(ang):
    return int((ang % TAU) / ARC) % BINS


def ang_delta(a, b):
    return (a - b + math.pi) % TAU - math.pi


def angle_bins(hx, hy, pts, others):
    danger = [9999.0] * BINS
    reach2 = 220 * 220

    def mark(x, y, widen):
        dx, dy = x - hx, y - hy
        dist2 = dx * dx + dy * dy
        if dist2 >= reach2 or dist2 < 1:
            return
        dist = math.sqrt(dist2)
        slot = bin_of(math.atan2(dy, dx))
        width = widen + (1 if dist < 85 else 0)
        for offset in range(-width, width + 1):
            index = (slot + offset) % BINS
            if dist < danger[index]:
                danger[index] = dist

    if len(pts) > 8:
        for x, y in pts[:-6:2]:
            mark(x, y, 0)
    for row in others:
        other = row[1]
        if len(other) < 2:
            if other:
                mark(other[-1][0], other[-1][1], 1)
            continue
        evx = other[-1][0] - other[-2][0]
        evy = other[-1][1] - other[-2][1]
        mark(other[-1][0] + evx * 3, other[-1][1] + evy * 3, 1)
        for x, y in other[:-1:2]:
            mark(x, y, 0)
    return danger


def clearest(prefer, danger, goal_dist):
    need = min(150.0, max(72.0, goal_dist * 0.82))
    prefer = prefer % TAU
    start = bin_of(prefer)
    if danger[start] >= need:
        return prefer
    for step in range(1, BINS):
        for sign in (1, -1):
            slot = (start + sign * step) % BINS
            if danger[slot] >= need:
                return slot * ARC + ARC * 0.5
    slot = max(range(BINS), key=lambda index: danger[index])
    return slot * ARC + ARC * 0.5


def refresh_track(game):
    name = game.track_name.strip().lower()
    if not game.track or not name:
        return
    with game.lock:
        local_ids = {pilot.self_id for pilot in game.pilots if pilot.self_id is not None}
        snake = game.snakes.get(game.track_sid) if game.track_sid is not None else None
        if snake is not None and (snake.get("nick") or "").strip().lower() != name:
            game.track_xy = None
            game.track_sid = None
        found = None
        for sid, snake in game.snakes.items():
            if sid in local_ids or not snake.get("pts"):
                continue
            nick = (snake.get("nick") or "").strip().lower()
            if nick != name:
                continue
            x, y = snake["pts"][-1]
            found = (x, y, sid)
            if not snake.get("away"):
                break
        if found:
            game.track_xy = (found[0], found[1])
            game.track_sid = found[2]


def flank_angle(hx, hy, ex, ey, ux, uy, side, radius):
    if ux * ux + uy * uy < 0.01:
        dx, dy = ex - hx, ey - hy
        dist = math.hypot(dx, dy) or 1.0
        ux, uy = dx / dist, dy / dist
    tx = ex + ux * 30 - uy * side * radius
    ty = ey + uy * 30 + ux * side * radius
    return math.atan2(ty - hy, tx - hx)


def body_gap(hx, hy, pts):
    best = 9999.0
    nearest = (hx, hy)
    for x, y in (pts[:-1:2] or pts[:1]):
        dist = math.hypot(x - hx, y - hy)
        if dist < best:
            best = dist
            nearest = (x, y)
    return best, nearest


def body_field(hx, hy, others, local_ids):
    best = None
    for row in others:
        if row[0] in local_ids:
            continue
        other = row[1]
        if not other or len(other) < 4:
            continue
        body = other[:-8] if len(other) > 12 else other[:-2]
        for x, y in body[::2]:
            dist = math.hypot(x - hx, y - hy)
            if dist < 82 and (best is None or dist < best[0]):
                best = (dist, math.atan2(hy - y, hx - x))
    return best


def nose_hit(hx, hy, facing, others, local_ids, friends=False):
    fx, fy = math.cos(facing), math.sin(facing)
    best = None
    for row in others:
        if not friends and row[0] in local_ids:
            continue
        other = row[1]
        if not other:
            continue
        points = list(other[:-4:2] if len(other) > 8 else other[:-1:2])
        points.append(other[-1])
        for index, (x, y) in enumerate(points):
            dx, dy = x - hx, y - hy
            along = dx * fx + dy * fy
            if along < 16 or along > 300:
                continue
            side = dx * fy - dy * fx
            pad = 52 if index == len(points) - 1 else 84
            if abs(side) > pad:
                continue
            turn = -1.0 if side > 8 else (1.0 if side < -8 else 1.0)
            swing = 2.15 if along < 150 else 1.65
            away = facing + turn * swing
            if best is None or along < best[0]:
                best = (along, away)
    return best


def choose_move(hx, hy, facing, pts, others, foods, preys, length, msl, grd, local_ids, sides, track_xy=None, track_sid=None, rally_xy=None, role=None, gathered=False, shield_xy=None, escort_xy=None, shield_sid=None):
    danger = angle_bins(hx, hy, pts, others)
    front = bin_of(facing)
    front_dist = min(danger[front], danger[(front - 1) % BINS], danger[(front + 1) % BINS])
    now = time.monotonic()
    mid = pts[len(pts) // 2] if len(pts) > 4 else (hx, hy)
    threat = None
    attack = None
    friend = None
    for row in others:
        sid = row[0]
        other = row[1]
        fast = bool(row[4]) if len(row) > 4 else False
        if not other:
            continue
        ex, ey = other[-1]
        if len(other) >= 2:
            evx = other[-1][0] - other[-2][0]
            evy = other[-1][1] - other[-2][1]
        else:
            evx = evy = 0.0
        speed = math.hypot(evx, evy) or float(msl or 1)
        ux, uy = evx / speed, evy / speed
        edist = math.hypot(ex - hx, ey - hy) or 1.0
        if sid in local_ids or sid == shield_sid:
            if sid in local_ids and (friend is None or edist < friend[0]):
                friend = (edist, math.atan2(hy - ey, hx - ex))
            continue
        touched, _point = body_gap(hx, hy, other)
        inside = touched < 48
        if len(pts) > 10 and edist < 210:
            for x, y in pts[:-8:3]:
                if (x - ex) ** 2 + (y - ey) ** 2 < 52 * 52:
                    inside = True
                    break
        along = (hx - ex) * ux + (hy - ey) * uy
        perp_head = (hx - ex) * -uy + (hy - ey) * ux
        aims_head = along > 16 and along < 280 and abs(perp_head) < 68
        forward_x = math.cos(facing)
        forward_y = math.sin(facing)
        body_across = False
        for x, y in other[:-1:3]:
            ahead = (x - hx) * forward_x + (y - hy) * forward_y
            aside = abs((x - hx) * forward_y - (y - hy) * forward_x)
            if 16 < ahead < 160 and aside < 34:
                body_across = True
                break
        attacking_us = (fast and aims_head) or (aims_head and edist < 150) or (body_across and (fast or aims_head))
        previous = sides.get(sid)
        if previous and attacking_us and edist < 420:
            old_x, old_y = previous
            turned = evx * old_y - evy * old_x
            toward_head = turned * ((hx - ex) * old_y - (hy - ey) * old_x)
            if toward_head < 0:
                sides[sid + 100000] = -sides.get(sid + 100000, 1)
        if evx or evy:
            sides[sid] = (evx, evy)
        side = sides.get(sid + 100000)
        if side not in (1, -1):
            left = math.atan2(ey - uy * 90 - hy, ex - ux * 90 - hx)
            right = math.atan2(ey + uy * 90 - hy, ex + ux * 90 - hx)
            side = 1 if danger[bin_of(left)] >= danger[bin_of(right)] else -1
            sides[sid + 100000] = side
        if inside or attacking_us or (body_across and edist < 120):
            away = math.atan2(hy - ey, hx - ex) if inside else flank_angle(hx, hy, ex, ey, ux, uy, side, 170)
            rank = 0 if inside or edist < 80 else 1
            use_boost = length > 12 and (inside or touched < 62 or (attacking_us and edist < 220))
            if threat is None or rank < threat[0] or (rank == threat[0] and edist < threat[1]):
                threat = (rank, edist, away, use_boost)
            continue
        tracked = track_sid is not None and sid == track_sid
        beside = along > 20 and 60 < abs(perp_head) < 150 and not aims_head
        if not beside or edist > 210:
            continue
        aim = math.atan2(ey + ux * side * 175 - hy, ex - uy * side * 175 - hx)
        lined = abs(ang_delta(aim, facing)) < 0.85
        can_boost = length > 18 and 70 < edist < 180 and lined
        score = edist - (40 if tracked else 0)
        if attack is None or score < attack[0]:
            attack = (score, aim, can_boost, tracked, edist)
    field = body_field(hx, hy, others, local_ids)
    ahead = nose_hit(hx, hy, facing, others, local_ids, friends=rally_xy is not None)
    hold = sides.get("hold")
    boost = False
    pile = False
    dodging = ahead is not None or field is not None
    if ahead is not None:
        along, away = ahead
        desired = away
        boost = length > 12 and along < 95 and abs(ang_delta(away, facing)) < 1.15
    elif field is not None:
        dist, away = field
        desired = away
        boost = length > 10 and dist < 62
    elif threat is not None:
        desired = threat[2]
        boost = bool(threat[3])
    elif (feast := death_feast(foods, preys, others, hx, hy, length)) is not None:
        desired = math.atan2(feast[1], feast[0])
        pile = True
        boost = bool(feast[3]) and front_dist > 60
    elif shield_xy is not None:
        pdist = math.hypot(shield_xy[0] - hx, shield_xy[1] - hy)
        if pdist > 210:
            desired = math.atan2(shield_xy[1] - hy, shield_xy[0] - hx)
            boost = length > 14 and pdist > 320 and front_dist > 200
        elif attack is not None:
            desired = attack[1]
            boost = bool(attack[2])
        else:
            point = escort_xy or shield_xy
            desired = math.atan2(point[1] - hy, point[0] - hx)
    elif rally_xy is not None and not gathered:
        dx, dy = rally_xy[0] - hx, rally_xy[1] - hy
        dist = math.hypot(dx, dy) or 1.0
        desired = math.atan2(dy, dx)
        boost = length > 14 and dist > 280 and front_dist > 200
    elif role == "defend" and gathered and rally_xy is not None and attack is None:
        dx, dy = rally_xy[0] - hx, rally_xy[1] - hy
        desired = math.atan2(dy, dx)
    else:
        plan = meal_plan(foods, preys, others, hx, hy, length)
        clean_cut = attack is not None and attack[2] and role != "defend"
        if plan and plan[2] and not (clean_cut and attack[4] < 120):
            desired = math.atan2(plan[1], plan[0])
            pile = True
            boost = bool(plan[3]) and front_dist > 90
        elif clean_cut:
            desired = attack[1]
            boost = bool(attack[2])
        elif track_xy is not None:
            tx, ty = track_xy
            dx, dy = tx - hx, ty - hy
            dist = math.hypot(dx, dy) or 1.0
            side = sides.get("track", 1)
            if side not in (1, -1):
                side = 1
                sides["track"] = side
            desired = flank_angle(hx, hy, tx, ty, dx / dist, dy / dist, side, 160 if dist < 340 else 100)
        elif plan:
            desired = math.atan2(plan[1], plan[0])
        elif grd > 1000:
            desired = math.atan2(grd - hy, grd - hx)
        else:
            desired = facing
    if threat is not None and field is None:
        if hold and now < hold[0] and abs(ang_delta(hold[1], desired)) < 1.05:
            desired = hold[1]
        else:
            sides["hold"] = (now + 0.3, desired)
    if not dodging:
        cleared = clearest(desired, danger, 110)
        if abs(ang_delta(cleared, desired)) < 1.15:
            desired = cleared
    friend_limit = 46 if rally_xy is not None else 80
    if friend is not None and not dodging and not pile and friend[0] < friend_limit and (threat is None or friend[0] < threat[1]):
        desired = friend[1]
        boost = friend[0] < 50 and length > 12
    if grd > 1000 and math.hypot(hx - grd, hy - grd) > grd * 0.94 and threat is None:
        desired = math.atan2(grd - hy, grd - hx)
        pile = False
    if boost and not pile and danger[bin_of(desired)] < 36:
        boost = False
    if pile and front_dist < 48:
        boost = False
    blocked = sum(1 for dist in danger if dist < 110)
    if blocked >= 5:
        gap_angle = facing
        gap_room = -1.0
        for index in range(BINS):
            room = danger[index] - abs(ang_delta(index * ARC, facing)) * 30
            if room > gap_room:
                gap_room = room
                gap_angle = index * ARC + ARC * 0.5
        desired = gap_angle
        dodging = True
        if length > 8:
            boost = True
    for row in others:
        if row[0] in local_ids or row[0] == shield_sid or not row[1]:
            continue
        ex, ey = row[1][-1]
        edist = math.hypot(ex - hx, ey - hy)
        if edist > 190:
            continue
        ang_to = math.atan2(ey - hy, ex - hx)
        if abs(ang_delta(desired, ang_to)) < 0.42:
            desired = ang_to + (sides.get(row[0] + 100000, 1) or 1) * 1.45
            if edist < 80:
                boost = False
    return desired, boost

def team_plan(game, pilot):
    alive = [other for other in game.pilots if other.alive]
    if not alive:
        return None, None, False
    cx = sum(other.hx for other in alive) / len(alive)
    cy = sum(other.hy for other in alive) / len(alive)
    spread = max(math.hypot(other.hx - cx, other.hy - cy) for other in alive)
    gathered = spread < 170
    defender = max(alive, key=lambda other: (other.length, -other.slot))
    role = "defend" if pilot.slot == defender.slot else "attack"
    angle = pilot.slot * 2.513
    radius = 48 if gathered else 64
    return role, (cx + math.cos(angle) * radius, cy + math.sin(angle) * radius), gathered


def autoplay(game, pilot):
    if pilot.manual:
        return
    with game.lock:
        hx = pilot.hx
        hy = pilot.hy
        length = pilot.length
        msl = game.msl or 42
        grd = game.grd
        local_ids = {other.self_id for other in game.pilots if other.self_id is not None}
        tracking = bool(game.track and game.track_name.strip() and game.track_xy)
        track_xy = game.track_xy if tracking else None
        track_sid = game.track_sid if tracking else None
        if game.rally:
            role, rally_xy, gathered = team_plan(game, pilot)
        else:
            role, rally_xy, gathered = None, None, False
        shield_xy = escort_xy = None
        shield_sid = None
        if game.shield and game.player_xy and time.monotonic() - game.player_at < 1.5:
            sx, sy = game.player_xy
            shield_xy = (sx, sy)
            angle = pilot.slot * 2.513
            escort_xy = (sx + math.cos(angle) * 130, sy + math.sin(angle) * 130)
            nearest = None
            for sid, snake in game.snakes.items():
                if sid in local_ids or not snake.get("pts"):
                    continue
                x, y = snake["pts"][-1]
                dist = math.hypot(x - sx, y - sy)
                if dist < 100 and (nearest is None or dist < nearest[0]):
                    nearest = (dist, sid)
            if nearest:
                shield_sid = nearest[1]
    if pilot.self_id is None:
        return
    state = game.snapshot(hx, hy, pilot.self_id)
    pts = state["pts"]
    if not pts:
        return
    hx, hy = pts[-1]
    if len(pts) >= 2:
        facing = math.atan2(pts[-1][1] - pts[-2][1], pts[-1][0] - pts[-2][0])
    else:
        facing = 0.0
    desired, boost = choose_move(
        hx,
        hy,
        facing,
        pts,
        state["others"],
        state["foods"],
        state["preys"],
        length,
        msl,
        grd,
        local_ids,
        pilot.sides,
        track_xy,
        track_sid,
        rally_xy,
        role,
        gathered,
        shield_xy,
        escort_xy,
        shield_sid,
    )
    set_drive(game, pilot, desired, boost)


def steer(game, pilot, dx, dy):
    if dx * dx + dy * dy < 256:
        return
    ang = math.atan2(dy, dx)
    if ang < 0:
        ang += TAU
    sang = int(251 * ang / TAU) % 251
    if sang > 250:
        sang = 250
    with game.lock:
        if sang != pilot.sang:
            pilot.sang = sang
            pilot.dirty = True
            pilot.steered = True


def draw_switch(renderer, font, top, label, enabled):
    from pygame._sdl2.video import Texture

    renderer.draw_color = (255, 255, 255, 255) if enabled else (70, 74, 92, 255)
    renderer.fill_rect(pygame.Rect(16, top, 52, 28))
    renderer.draw_color = (20, 20, 28, 255) if enabled else (230, 230, 236, 255)
    knob = 42 if enabled else 20
    renderer.fill_rect(pygame.Rect(knob, top + 4, 20, 20))
    text = font.render(label, True, (255, 255, 255))
    tex = Texture.from_surface(renderer, text)
    renderer.blit(tex, pygame.Rect(80, top + 4, tex.width, tex.height))


def draw_box_window(renderer, font, boxes, tracers, auto):
    renderer.draw_color = (24, 24, 36, 255)
    renderer.clear()
    draw_switch(renderer, font, 16, "box", boxes)
    draw_switch(renderer, font, 58, "tracers", tracers)
    draw_switch(renderer, font, 100, "auto play", auto)
    renderer.present()


def draw_player_window(renderer, font, rows, count, track, name, editing, xy, rally, shield):
    from pygame._sdl2.video import Texture

    renderer.draw_color = (16, 16, 28, 255)
    renderer.clear()
    lines = [f"joueurs {count}", "pseudo            x        y      long"]
    for mine, nick, x, y, length, _sid in rows[:24]:
        mark = ">" if mine else " "
        xpos = f"{x:>7}" if x is not None else "      -"
        ypos = f"{y:>7}" if y is not None else "      -"
        lines.append(f"{mark}{nick[:16]:<16} {xpos} {ypos} {length:>6}")
    y = 8
    for line in lines:
        if y > 548:
            break
        img = font.render(line, True, (255, 255, 255) if not line.startswith(" ") else (210, 214, 230))
        tex = Texture.from_surface(renderer, img)
        renderer.blit(tex, pygame.Rect(8, y, tex.width, tex.height))
        y += tex.height + 2
    draw_switch(renderer, font, 588, "track", track)
    renderer.draw_color = (58, 64, 92, 255) if editing else (32, 34, 48, 255)
    renderer.fill_rect(pygame.Rect(200, 586, 304, 32))
    shown = (name + ("|" if editing else "")) or "pseudo"
    img = font.render(shown[:24], True, (255, 255, 255) if name else (150, 154, 170))
    tex = Texture.from_surface(renderer, img)
    renderer.blit(tex, pygame.Rect(208, 592, tex.width, tex.height))
    if xy:
        seen = font.render(f"vu {int(xy[0])} {int(xy[1])}", True, (184, 255, 154))
    else:
        seen = font.render("pas vu", True, (150, 154, 170))
    stex = Texture.from_surface(renderer, seen)
    renderer.blit(stex, pygame.Rect(16, 620, stex.width, stex.height))
    draw_switch(renderer, font, 656, "réunir", rally)
    draw_switch(renderer, font, 700, "shield", shield)
    renderer.present()


TRACER_PORT = 8765
TRACER_URL = "https://mehdi-slither-tracers.loca.lt/bots"


def bot_positions(game):
    with game.lock:
        bots = []
        for pilot in game.pilots:
            if not pilot.alive:
                continue
            bots.append(
                {
                    "slot": pilot.slot,
                    "name": pilot.name,
                    "x": pilot.hx,
                    "y": pilot.hy,
                }
            )
        return bots


def start_tracer_server(game):
    class Handler(BaseHTTPRequestHandler):
        def _cors(self):
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Private-Network", "true")
            self.send_header("Cache-Control", "no-store")

        def do_OPTIONS(self):
            self.send_response(204)
            self._cors()
            self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "*")
            self.end_headers()

        def do_POST(self):
            length = int(self.headers.get("Content-Length", "0") or 0)
            raw = self.rfile.read(max(0, min(length, 4000))) if length else b""
            try:
                data = json.loads(raw.decode("utf-8") or "{}")
                point = (float(data["x"]), float(data["y"]))
            except (KeyError, TypeError, ValueError, json.JSONDecodeError):
                self.send_response(400)
                self._cors()
                self.end_headers()
                return
            with game.lock:
                game.player_xy = point
                game.player_at = time.monotonic()
            self.send_response(204)
            self._cors()
            self.end_headers()

        def do_GET(self):
            body = json.dumps({"bots": bot_positions(game)}).encode()
            self.send_response(200)
            self._cors()
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, fmt, *args):
            return

    try:
        server = ThreadingHTTPServer(("127.0.0.1", TRACER_PORT), Handler)
    except OSError as exc:
        print(f"tracers indisponible: {exc}", flush=True)
        return
    threading.Thread(target=server.serve_forever, daemon=True).start()

    def tunnel():
        import re

        while True:
            try:
                proc = subprocess.Popen(
                    ["cmd", "/c", "npx", "--yes", "cloudflared", "tunnel", "--url", f"http://127.0.0.1:{TRACER_PORT}"],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                )
            except OSError as exc:
                print(f"tunnel indisponible: {exc}", flush=True)
                time.sleep(5)
                continue
            for line in proc.stdout:
                found = re.search(r"https://[a-z0-9-]+\.trycloudflare\.com", line)
                if not found:
                    continue
                public = found.group(0)
                path = r"C:\Users\mehdi\Downloads\slither-tracers.js"
                try:
                    script = open(path, encoding="utf-8").read()
                    script = re.sub(r'var url = "https://[^"]+";', f'var url = "{public}/bots";', script, count=1)
                    open(path, "w", encoding="utf-8").write(script)
                except OSError:
                    pass
                print(f"tracers {public}/bots", flush=True)
            time.sleep(3)

    threading.Thread(target=tunnel, daemon=True).start()


_runner = {"thread": None}


def bots_running():
    thread = _runner["thread"]
    return thread is not None and thread.is_alive()


def snapshot_state(game):
    with game.lock:
        pilots = list(game.pilots)
        server_id = game.server_id
        deaths = game.deaths
        status = game.status
        stats = {host: dict(row) for host, row in game.proxy_stats.items()}
        proxy_total = getattr(game, "proxy_total", 0)
    alive = sum(pilot.alive for pilot in pilots)
    linking = sum(pilot.status == "connexion" for pilot in pilots)
    dead_now = sum(pilot.status == "Mort" for pilot in pilots)
    hosts = []
    for pilot in pilots:
        host = pilot.proxy["host"] if pilot.proxy else "direct"
        if host not in hosts:
            hosts.append(host)
    rows = []
    for host in hosts:
        row = stats.get(host, {"ok": 0, "fail": 0})
        live = sum(
            pilot.alive and ((pilot.proxy and pilot.proxy["host"] == host) or (not pilot.proxy and host == "direct"))
            for pilot in pilots
        )
        if row["ok"] and not row["fail"]:
            state = "ok"
        elif row["ok"]:
            state = "melange"
        elif row["fail"]:
            state = "rejete"
        else:
            state = "attente"
        rows.append({"host": host, "ok": row["ok"], "fail": row["fail"], "live": live, "state": state})
    top_name, top_size = "", 0
    for pilot in pilots:
        if not pilot.alive or pilot.length <= top_size:
            continue
        top_name, top_size = f"#{pilot.slot + 1} {pilot.name}", pilot.length
    if top_size > 0:
        note_record(top_name, top_size)
    players = []
    for pilot in pilots:
        proxy = pilot.proxy or {}
        host = proxy.get("host", "")
        row = stats.get(host, {"ok": 0, "fail": 0})
        players.append(
            {
                "slot": pilot.slot,
                "name": pilot.name,
                "x": round(pilot.hx, 1),
                "y": round(pilot.hy, 1),
                "dead": pilot.status == "Mort" or not pilot.alive,
                "alive": pilot.alive,
                "status": pilot.status,
                "size": pilot.length,
                "proxyHost": host,
                "proxyPort": proxy.get("port", ""),
                "proxyUser": proxy.get("user", ""),
                "proxyPass": proxy.get("password", ""),
                "proxyOk": row["ok"],
                "proxyFail": row["fail"],
                "proxyState": "ok" if row["ok"] and not row["fail"] else "melange" if row["ok"] else "rejete" if row["fail"] else "attente",
            }
        )
    return {
        "running": bots_running(),
        "server": server_id,
        "count": len(pilots),
        "alive": alive,
        "connecting": linking,
        "dead": dead_now,
        "deaths": deaths,
        "status": status,
        "proxies": len(hosts),
        "proxyTotal": proxy_total,
        "proxyOk": sum(1 for row in rows if row["ok"]),
        "proxyBad": sum(1 for row in rows if row["fail"] and not row["ok"]),
        "connOk": sum(row["ok"] for row in rows),
        "connBad": sum(row["fail"] for row in rows),
        "rows": rows,
        "players": players,
        "topName": top_name,
        "topSize": top_size,
        "recordName": _record_name,
        "recordSize": _record_size,
    }


def thin_points(points, step=2):
    if len(points) <= 24:
        return [[round(x, 1), round(y, 1)] for x, y in points]
    slim = points[::step]
    if slim[-1] != points[-1]:
        slim.append(points[-1])
    return [[round(x, 1), round(y, 1)] for x, y in slim]


def view_state(game, slot):
    with game.lock:
        pilot = next((item for item in game.pilots if item.slot == slot), None)
    if pilot is None:
        return None
    state = game.snapshot(pilot.hx, pilot.hy, pilot.self_id)
    me = thin_points(state["pts"], 1)
    me_cv = 0
    me_fast = False
    grd = 0
    with game.lock:
        grd = int(game.grd or 0)
        snake = game.snakes.get(pilot.self_id) if pilot.self_id is not None else None
        if snake:
            me_cv = int(snake.get("cv") or 0)
            me_fast = bool(snake.get("fast"))
    others = []
    for _sid, body, cv, nick, fast in state["others"]:
        others.append({"cv": cv, "nick": nick, "fast": bool(fast), "pts": thin_points(body, 1)})
    foods = [[round(food[0], 1), round(food[1], 1), food[2], food[3]] for food in state["foods"][:700]]
    preys = [[round(prey[0], 1), round(prey[1], 1), prey[2], prey[3]] for prey in state["preys"][:120]]
    return {
        "slot": slot,
        "name": pilot.name,
        "alive": pilot.alive,
        "x": pilot.hx,
        "y": pilot.hy,
        "size": len(me),
        "cv": me_cv,
        "fast": me_fast,
        "grd": grd,
        "me": me,
        "others": others,
        "foods": foods,
        "preys": preys,
    }


def control_bot(game, slot, angle, boost, active):
    with game.lock:
        pilot = next((item for item in game.pilots if item.slot == slot), None)
        if pilot is None:
            return False
        pilot.manual = bool(active)
    if active and angle is not None:
        set_drive(game, pilot, float(angle), bool(boost))
    elif not active:
        set_drive(game, pilot, pilot.sang / 251 * TAU, False)
    return True


def launch_bots(game, name, count, server, skin):
    if bots_running():
        return False, "Des bots tournent deja. Arrete-les d'abord."
    if count < 1:
        return False, "Le count doit etre au moins 1."
    if skin is not None and not 0 <= skin <= 64:
        return False, "Skin entre 0 et 64."
    game.quit = False
    with game.lock:
        game.deaths = 0
        game.proxy_stats = {}
        game.pilots = []
        game.status = "connexion"
        game.server_id = server
    names = pilot_names(name, count)
    _runner["thread"] = threading.Thread(
        target=network, args=(game, names, server, skin), daemon=True
    )
    _runner["thread"].start()
    return True, "Bots lances."


def stop_bots(game):
    game.quit = True
    return True, "Arret demande."


def serve_dashboard(game):
    port = int(os.environ.get("PORT", "8080"))
    page_path = os.path.join(ROOT, "dashboard.html")

    class Handler(BaseHTTPRequestHandler):
        def _send(self, code, body, content_type):
            data = body if isinstance(body, bytes) else body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            path = self.path.split("?", 1)[0]
            if path.startswith("/s/"):
                name = os.path.basename(path)
                target = os.path.join(ROOT, "s", name)
                allowed = {"bg54.jpg": "image/jpeg", "gbg.jpg": "image/jpeg", "look.js": "application/javascript; charset=utf-8"}
                if name not in allowed or not os.path.isfile(target):
                    self._send(404, "introuvable", "text/plain; charset=utf-8")
                    return
                with open(target, "rb") as handle:
                    self._send(200, handle.read(), allowed[name])
                return
            if path == "/api/status":
                self._send(200, json.dumps(snapshot_state(game)), "application/json")
                return
            if path == "/api/view":
                query = self.path.split("?", 1)[1] if "?" in self.path else ""
                slot = 0
                for part in query.split("&"):
                    if part.startswith("slot="):
                        try:
                            slot = int(part.split("=", 1)[1])
                        except ValueError:
                            slot = 0
                view = view_state(game, slot)
                if view is None:
                    self._send(404, json.dumps({"ok": False}), "application/json")
                    return
                self._send(200, json.dumps(view), "application/json")
                return
            if path not in ("/", "/dashboard"):
                self._send(404, "introuvable", "text/plain; charset=utf-8")
                return
            try:
                html = open(page_path, encoding="utf-8").read()
            except OSError:
                html = "<p>dashboard manquant</p>"
            self._send(200, html, "text/html; charset=utf-8")

        def do_POST(self):
            path = self.path.split("?", 1)[0]
            length = int(self.headers.get("Content-Length", "0") or 0)
            raw = self.rfile.read(max(0, min(length, 8000))) if length else b"{}"
            try:
                data = json.loads(raw.decode("utf-8") or "{}")
            except json.JSONDecodeError:
                data = {}
            if path == "/api/control":
                try:
                    slot = int(data.get("slot") or 0)
                    angle = None if data.get("angle") is None else float(data.get("angle"))
                except (TypeError, ValueError):
                    self._send(400, json.dumps({"ok": False}), "application/json")
                    return
                ok = control_bot(game, slot, angle, bool(data.get("boost")), bool(data.get("on", True)))
                self._send(200, json.dumps({"ok": ok}), "application/json")
                return
            if path == "/api/stop":
                ok, message = stop_bots(game)
            elif path == "/api/start":
                try:
                    count = int(data.get("count") or 1)
                    server = int(data.get("server") or 0)
                    skin_raw = data.get("skin")
                    skin = None if skin_raw in (None, "", "random") else int(skin_raw)
                except (TypeError, ValueError):
                    self._send(400, json.dumps({"ok": False, "message": "Nombres invalides."}), "application/json")
                    return
                ok, message = launch_bots(game, str(data.get("name") or "jjj")[:23], count, server, skin)
            else:
                self._send(404, json.dumps({"ok": False, "message": "introuvable"}), "application/json")
                return
            self._send(200, json.dumps({"ok": ok, "message": message}), "application/json")

        def log_message(self, fmt, *args):
            return

    try:
        server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    except OSError as exc:
        print(f"dashboard indisponible: {exc}", flush=True)
        if not os.environ.get("PORT"):
            webbrowser.open(f"http://127.0.0.1:{port}/")
        return
    print(f"http://127.0.0.1:{port}", flush=True)
    if not os.environ.get("PORT"):
        threading.Timer(0.3, lambda: webbrowser.open(f"http://127.0.0.1:{port}/")).start()
    server.serve_forever()


def draw_board(game):
    with game.lock:
        pilots = list(game.pilots)
        server_id = game.server_id
        deaths = game.deaths
        stats = {host: dict(row) for host, row in game.proxy_stats.items()}
    alive = sum(pilot.alive for pilot in pilots)
    linking = sum(pilot.status == "connexion" for pilot in pilots)
    dead_now = sum(pilot.status == "Mort" for pilot in pilots)
    hosts = []
    for pilot in pilots:
        host = pilot.proxy["host"] if pilot.proxy else "direct"
        if host not in hosts:
            hosts.append(host)
    ok_n = sum(stats.get(host, {}).get("ok", 0) for host in hosts)
    fail_n = sum(stats.get(host, {}).get("fail", 0) for host in hosts)
    ip_ok = sum(1 for host in hosts if stats.get(host, {}).get("ok", 0))
    ip_bad = sum(1 for host in hosts if stats.get(host, {}).get("fail", 0) and not stats.get(host, {}).get("ok", 0))
    lines = [
        f"{'serveur':<22}{server_id or '-'}",
        f"{'count':<22}{len(pilots)}",
        f"{'en jeu':<22}{alive}",
        f"{'connexion':<22}{linking}",
        f"{'mort maintenant':<22}{dead_now}",
        f"{'morts total':<22}{deaths}",
        f"{'proxys utilises':<22}{len(hosts)}",
        f"{'proxys ok':<22}{ip_ok}",
        f"{'proxys rejetes':<22}{ip_bad}",
        f"{'connexions ok':<22}{ok_n}",
        f"{'connexions rejetees':<22}{fail_n}",
        "",
        f"{'proxy':<22}{'ok':>6}{'rejete':>8}{'en jeu':>8}  etat",
    ]
    for host in hosts:
        row = stats.get(host, {"ok": 0, "fail": 0})
        live = sum(pilot.alive and ((pilot.proxy and pilot.proxy["host"] == host) or (not pilot.proxy and host == "direct")) for pilot in pilots)
        if row["ok"] and not row["fail"]:
            state = "ok"
        elif row["ok"]:
            state = "melange"
        elif row["fail"]:
            state = "rejete"
        else:
            state = "attente"
        lines.append(f"{host:<22}{row['ok']:>6}{row['fail']:>8}{live:>8}  {state}")
    os.system("cls")
    print("\n".join(lines), flush=True)


def main():
    parser = argparse.ArgumentParser(description="Joue a slither.io dans une fenetre")
    parser.add_argument("--name", default="jjj")
    parser.add_argument("--count", type=int, default=1, help="nombre de serpents, tous avec le meme pseudo")
    parser.add_argument("--server", type=int, default=0, help="id du serveur, par exemple 3619")
    parser.add_argument("--skin", type=int, default=None, help="numero du skin, de 0 a 64")
    parser.add_argument("--skins", action="store_true", help="affiche la liste des skins et quitte")
    parser.add_argument("--board", action="store_true", help="tableau dans la console, sans fenetre")
    parser.add_argument("--web", action="store_true", help="dashboard web, sans fenetre")
    args = parser.parse_args()
    if args.skins:
        for number, name in SKINS:
            print(f"{number:2}  {name}")
        return
    if args.skin is not None and not 0 <= args.skin <= 64:
        parser.error("skin entre 0 et 64")
    game = Game()
    game.board_mode = args.board or args.web
    game.proxy_total = len(load_proxies(PROXY_FILE))
    if args.web or not os.environ.get("PORT"):
        if not args.web:
            threading.Thread(target=serve_dashboard, args=(game,), daemon=True).start()
        else:
            serve_dashboard(game)
            return
    if not args.board:
        start_tracer_server(game)
    names = pilot_names(args.name, args.count)
    thread = threading.Thread(target=network, args=(game, names, args.server, args.skin), daemon=True)
    thread.start()
    if args.board:
        try:
            while not game.quit:
                draw_board(game)
                time.sleep(0.4)
        except KeyboardInterrupt:
            game.quit = True
        return
    load_pygame()
    if sys.platform == "win32":
        ctypes.windll.winmm.timeBeginPeriod(1)
    from pygame._sdl2.video import Renderer, Window

    pygame.init()
    screen = pygame.display.set_mode((960, 540), pygame.SCALED | pygame.DOUBLEBUF, vsync=0)
    pygame.display.set_caption("slither")
    game_window = Window.from_display_module()
    box_window = Window("box", size=(260, 150))
    list_window = Window("joueurs", size=(520, 780))
    box_window.position = (40, 80)
    list_window.position = (280, 80)
    box_renderer = Renderer(box_window)
    list_renderer = Renderer(list_window)
    ui_font = pygame.font.SysFont("consolas", 16)
    pygame.key.set_repeat(350, 40)
    clock = pygame.time.Clock()
    view = View()
    pointer = [screen.get_width() // 2, screen.get_height() // 2]

    def on_game(event):
        win = getattr(event, "window", None)
        return win is None or win is game_window

    while not game.quit:
        width, height = screen.get_size()
        for event in pygame.event.get():
            if event.type in (pygame.QUIT, pygame.WINDOWCLOSE) and on_game(event):
                game.quit = True
            elif event.type == pygame.WINDOWCLOSE and event.window is box_window:
                box_window.destroy()
                box_window = None
            elif event.type == pygame.WINDOWCLOSE and event.window is list_window:
                list_window.destroy()
                list_window = None
            elif event.type == pygame.MOUSEMOTION and on_game(event):
                pointer[0], pointer[1] = event.pos
            elif event.type == pygame.MOUSEWHEEL and on_game(event):
                if event.y > 0:
                    view.zoom *= 1.12
                elif event.y < 0:
                    view.zoom /= 1.12
            elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                if box_window is not None and getattr(event, "window", None) is box_window:
                    if event.pos[1] < 50:
                        game.boxes = not game.boxes
                    elif event.pos[1] < 94:
                        game.tracers = not game.tracers
                    else:
                        game.autoplay = not game.autoplay
                elif list_window is not None and getattr(event, "window", None) is list_window:
                    if event.pos[1] >= 692:
                        game.shield = not game.shield
                    elif event.pos[1] >= 648:
                        game.rally = not game.rally
                    elif event.pos[1] >= 576:
                        if event.pos[0] < 190:
                            game.track = not game.track
                        else:
                            game.track_edit = True
                    else:
                        game.track_edit = False
                elif on_game(event) and game.pilots:
                    target = game.pilots[pane_at(event.pos, width, height, len(game.pilots))]
                    with game.lock:
                        target.boosting = True
                        target.boost = 253
            elif event.type == pygame.KEYDOWN and game.track_edit and list_window is not None and getattr(event, "window", None) is list_window:
                if event.key == pygame.K_BACKSPACE:
                    game.track_name = game.track_name[:-1]
                elif event.key in (pygame.K_RETURN, pygame.K_ESCAPE):
                    game.track_edit = False
                elif event.unicode and event.unicode.isprintable() and len(game.track_name) < 24:
                    game.track_name += event.unicode
            elif event.type == pygame.MOUSEBUTTONUP and event.button == 1 and on_game(event) and game.pilots:
                target = game.pilots[pane_at(event.pos, width, height, len(game.pilots))]
                with game.lock:
                    target.boosting = False
                    target.boost = 254
        cols, rows = pane_grid(max(1, len(game.pilots)), width, height)
        cell_w = width / cols
        cell_h = height / rows
        col = min(cols - 1, max(0, int(pointer[0] / cell_w))) if cell_w else 0
        row = min(rows - 1, max(0, int(pointer[1] / cell_h))) if cell_h else 0
        pane = min(len(game.pilots) - 1, row * cols + col) if game.pilots else 0
        center_x = (col + 0.5) * cell_w
        center_y = (row + 0.5) * cell_h
        refresh_track(game)
        hunting = bool(game.track and game.track_name.strip() and game.track_xy)
        if game.autoplay or hunting or game.rally or game.shield:
            for pilot in game.pilots:
                if pilot.alive:
                    autoplay(game, pilot)
        else:
            for index, pilot in enumerate(game.pilots):
                if not pilot.alive:
                    continue
                if index == pane:
                    steer(game, pilot, pointer[0] - center_x, pointer[1] - center_y)
                else:
                    autoplay(game, pilot)
        view.render(screen, game)
        pygame.display.flip()
        if box_window is not None:
            draw_box_window(box_renderer, ui_font, game.boxes, game.tracers, game.autoplay)
        if list_window is not None:
            draw_player_window(
                list_renderer,
                ui_font,
                game.players(),
                game.player_count,
                game.track,
                game.track_name,
                game.track_edit,
                game.track_xy if game.track else None,
                game.rally,
                game.shield,
            )
        clock.tick(120)
    if sys.platform == "win32":
        ctypes.windll.winmm.timeEndPeriod(1)
    pygame.quit()


if __name__ == "__main__":
    main()
