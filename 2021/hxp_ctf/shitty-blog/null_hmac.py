import requests
import urllib.parse
from tqdm import tqdm
import itertools

url = "http://localhost:8888"

mac_counter = set()

print("[*] Looking for null MAC")
for i in tqdm(itertools.count()):
    res = requests.get(f"{url}")
    id, mac = urllib.parse.unquote(res.cookies["session"]).split("|")
    id = int(id)
    if (mac in mac_counter):
        break

    mac_counter.add(mac)

print(f"[+] Null MAC {mac} {id}")