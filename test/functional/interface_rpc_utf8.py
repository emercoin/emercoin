#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Non-ASCII text in JSON-RPC requests and replies.

- Single and batch replies encode strings the same way, as UTF-8, with and without -legacyrpc.
- -legacyrpc only changes how requests are read: a \\u0000-\\u00FF escape is a single byte, as
  in json_spirit; without it the escape is the Unicode character (UTF-8).
"""

import base64
import http.client
import json
import urllib.parse

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal

TEXT = "Bücher ☼ 😀"


def post(node, body):
    """POST raw bytes to the node's JSON-RPC port; the raw reply body."""
    url = urllib.parse.urlparse(node.url)
    auth = base64.b64encode(("%s:%s" % (url.username, url.password)).encode()).decode()
    conn = http.client.HTTPConnection(url.hostname, url.port)
    try:
        conn.request("POST", "/", body, {"Authorization": "Basic " + auth, "Content-Type": "application/json"})
        return conn.getresponse().read()
    finally:
        conn.close()


def echo(arg, qid=1):
    return {"jsonrpc": "1.0", "id": qid, "method": "echo", "params": [arg]}


class RPCUTF8Test(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        self.extra_args = [["-legacyrpc=1"], ["-legacyrpc=0"]]

    def run_test(self):
        for node, legacy in zip(self.nodes, (True, False)):
            self.log.info("-legacyrpc=%d: single and batch replies are UTF-8" % legacy)
            raw = json.dumps(echo(TEXT), ensure_ascii=False).encode()
            single = post(node, raw)
            batch = post(node, b"[" + raw + b"," + json.dumps(echo(TEXT, 2), ensure_ascii=False).encode() + b"]")
            assert TEXT.encode() in single and TEXT.encode() in batch, (single, batch)
            assert b"\\u00" not in batch, batch
            assert_equal(json.loads(single)["result"], [TEXT])
            assert_equal([r["result"] for r in json.loads(batch)], [[TEXT], [TEXT]])

            self.log.info("-legacyrpc=%d: a \\u00E9 escape in a request is %s" % (legacy, "one byte" if legacy else "UTF-8"))
            reply = post(node, json.dumps(echo("é")).encode())  # ensure_ascii: sent as é
            assert_equal(reply.split(b'"result":[')[1][:3], b'"\xe9"' if legacy else '"é'.encode())


if __name__ == '__main__':
    RPCUTF8Test().main()
