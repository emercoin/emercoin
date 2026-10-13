#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""The built-in DNS server (emcdns) answers from "dns:" names and survives malformed packets.

- A and TXT queries for a registered dns: name return its records.
- An unknown name is NXDOMAIN.
- Empty UDP datagrams are ignored.
- Malformed UDP packets (truncated, bad label lengths, compression loops, oversized names,
  random bytes) do not crash or wedge the server: it still answers afterwards.
- -emcdnsbindip=127.0.0.1 listens on loopback only.
- Large records stored on chain (a value holds up to 20 KiB) are served within the reply
  buffer, and the server keeps answering.
"""

import os

import random
import socket
import struct

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, p2p_port

QTYPE_A = 1
QTYPE_TXT = 16


def encode_name(name):
    out = b""
    for label in name.split("."):
        out += bytes([len(label)]) + label.encode()
    return out + b"\x00"


def make_query(name, qtype, qid=0x1234):
    header = struct.pack(">HHHHHH", qid, 0x0100, 1, 0, 0, 0)  # recursion desired, one question
    return header + encode_name(name) + struct.pack(">HH", qtype, 1)


def skip_name(msg, pos):
    while True:
        length = msg[pos]
        if length == 0:
            return pos + 1
        if length & 0xc0 == 0xc0:
            return pos + 2
        pos += 1 + length


def parse_response(msg):
    """(rcode, [(type, rdata)]) of a DNS response."""
    qid, flags, qd, an, ns, ar = struct.unpack(">HHHHHH", msg[:12])
    pos = 12
    for _ in range(qd):
        pos = skip_name(msg, pos) + 4
    answers = []
    for _ in range(an):
        pos = skip_name(msg, pos)
        rtype, rclass, ttl, rdlen = struct.unpack(">HHIH", msg[pos:pos + 10])
        pos += 10
        answers.append((rtype, msg[pos:pos + rdlen]))
        pos += rdlen
    return flags & 0xf, answers


class EmcDnsTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1

    def setup_nodes(self):
        self.dns_port = p2p_port(1)  # free: there is no node 1
        self.extra_args = [['-emcdns=1', '-emcdnsbindip=127.0.0.1', '-emcdnsport=%d' % self.dns_port]]
        super().setup_nodes()

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def query(self, packet, expect_reply=True):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.settimeout(5 if expect_reply else 0.2)
        try:
            sock.sendto(packet, ("127.0.0.1", self.dns_port))
            return sock.recv(4096)
        except socket.timeout:
            assert not expect_reply, "no DNS reply"
            return None
        finally:
            sock.close()

    def resolve(self, name, qtype):
        return parse_response(self.query(make_query(name, qtype)))

    def run_test(self):
        node = self.nodes[0]
        node.name_new("dns:example.coin", "A=1.2.3.4|TXT=hello emercoin", 1)
        node.generate(1)

        self.log.info("A and TXT records of a dns: name")
        rcode, answers = self.resolve("example.coin", QTYPE_A)
        assert_equal(rcode, 0)
        assert_equal(answers, [(QTYPE_A, bytes([1, 2, 3, 4]))])
        rcode, answers = self.resolve("example.coin", QTYPE_TXT)
        assert_equal(rcode, 0)
        assert_equal(len(answers), 1)
        assert_equal(answers[0][0], QTYPE_TXT)
        assert b"hello emercoin" in answers[0][1]

        self.log.info("Unknown name: NXDOMAIN")
        rcode, answers = self.resolve("nosuchname.coin", QTYPE_A)
        assert_equal(rcode, 3)
        assert_equal(answers, [])

        self.log.info("-emcdnsbindip=127.0.0.1 binds the loopback address only")
        if os.path.exists("/proc/net/udp6"):
            port = "%04X" % self.dns_port
            with open("/proc/net/udp6", encoding="utf8") as f:
                local = [line.split()[1] for line in f.readlines()[1:] if line.split()[1].endswith(":" + port)]
            assert_equal(local, ["0000000000000000FFFF00000100007F:" + port])  # ::ffff:127.0.0.1

        self.log.info("Empty datagrams are ignored")
        assert_equal(self.query(b"", expect_reply=False), None)
        rcode, answers = self.resolve("example.coin", QTYPE_A)
        assert_equal((rcode, answers), (0, [(QTYPE_A, bytes([1, 2, 3, 4]))]))

        self.log.info("Large on-chain records")
        large_records = {
            "dns:bigtxt.coin": "TXT=" + "x" * 5000,
            "dns:manytxt.coin": "|".join(["TXT=" + "y" * 200] * 60),
            "dns:manya.coin": "|".join(["A=10.0.%d.%d" % (i // 250, i % 250) for i in range(800)]),
            "dns:manyaaaa.coin": "|".join(["AAAA=2001:db8::%x" % i for i in range(600)]),
            "dns:longmx.coin": "|".join(["MX=" + "m" * 250 + ".coin:%d" % i for i in range(60)]),
            "dns:longns.coin": "|".join(["NS=" + ".".join(["n" * 63] * 4) for _ in range(40)]),
            "dns:longcname.coin": "CNAME=" + ".".join(["c" * 63] * 30),
            "dns:garbage.coin": "A=999.1.2.3|AAAA=zz::1|MX=|TXT|=|||A=|NS=..|CNAME=.",
        }
        for name, value in large_records.items():
            node.name_new(name, value[:20 * 1024], 1)
        node.generate(1)
        for name in large_records:
            for qtype in (QTYPE_A, 28, 15, 2, 5, QTYPE_TXT, 255):  # A AAAA MX NS CNAME TXT ANY
                reply = self.query(make_query(name[len("dns:"):], qtype), expect_reply=False)
                if reply is not None:
                    assert len(reply) <= 4096
        assert_equal(node.getblockcount(), 202)
        rcode, answers = self.resolve("example.coin", QTYPE_A)
        assert_equal((rcode, answers), (0, [(QTYPE_A, bytes([1, 2, 3, 4]))]))

        self.log.info("Malformed packets do not break the server")
        valid = make_query("example.coin", QTYPE_A)
        header = valid[:12]
        malformed = [
            b"",
            b"\x00",
            header[:11],
            header,                                               # no question at all
            struct.pack(">HHHHHH", 1, 0x0100, 100, 0, 0, 0),      # 100 questions announced, none sent
            header + b"\x3f" + b"a" * 10,                         # label longer than the rest
            header + b"\xc0\x0c" + struct.pack(">HH", 1, 1),      # compression pointer to itself
            header + b"\xc0\xff",                                 # pointer past the end
            header + encode_name(".".join(["a" * 63] * 5)) + struct.pack(">HH", 1, 1),  # name > 255 bytes
            header + b"\x40" + b"a" * 64 + b"\x00" + struct.pack(">HH", 1, 1),          # 64-byte label
            header + encode_name("example.coin"),                 # no qtype/qclass
            valid[:-3],
            struct.pack(">HHHHHH", 1, 0x8100, 1, 0, 0, 0) + valid[12:],  # a response, not a query
            b"\xff" * 512,
            b"\x00" * 4096,
        ]
        rng = random.Random(20261013)
        malformed += [bytes(rng.getrandbits(8) for _ in range(rng.randrange(1, 600))) for _ in range(300)]
        malformed += [header + bytes(rng.getrandbits(8) for _ in range(rng.randrange(1, 300))) for _ in range(300)]
        for packet in malformed:
            self.query(packet, expect_reply=False)
        assert_equal(node.getblockcount(), 202)  # the node is alive
        rcode, answers = self.resolve("example.coin", QTYPE_A)
        assert_equal((rcode, answers), (0, [(QTYPE_A, bytes([1, 2, 3, 4]))]))


if __name__ == '__main__':
    EmcDnsTest().main()
