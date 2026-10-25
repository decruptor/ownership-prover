#!/usr/bin/env python3
"""
prover.py — Decruptor proof-of-ownership tool (offline, Python 3 stdlib only)

Lets the owner of a Bitcoin wallet prove control of an address WITHOUT
sharing any spendable material, entirely offline:

  challenge     generate an ownership challenge for an address
  verify        verify a wallet message-signature against a challenge
  derive-check  check whether a seed phrase derives a claimed address
                (BIP39 -> BIP32 -> address, everything local)
  selftest      run all internal test vectors; must pass before real use

Trust model: this tool runs locally, sends nothing anywhere, and never
asks for your seed words to be sent to anyone. See README.md.

Exit codes: 0 = verified / match / selftest pass
            1 = not verified / no match / selftest fail
            2 = usage or input error
"""

import argparse
import getpass
import hashlib
import hmac
import os
import re
import sys
import unicodedata

DOMAIN = "decruptor-ownership-v1"

# ---------------------------------------------------------------------------
# Hashes
# ---------------------------------------------------------------------------

def sha256(b):
    return hashlib.sha256(b).digest()


def sha256d(b):
    return sha256(sha256(b))


def ripemd160_pure(data):
    """Pure-Python RIPEMD-160 (fallback for OpenSSL builds without it)."""
    # Message-schedule orders and rotation amounts for the two parallel
    # lines, verified verbatim against Bitcoin Core src/crypto/ripemd160.cpp
    # (RIPEMD-160 spec, Dobbertin/Bosselaers/Preneel).
    RL = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
          7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
          3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
          1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
          4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
    RR = [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
          6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
          15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
          8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
          12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
    SL = [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
          7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
          11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
          11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
          9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
    SR = [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
          9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
          9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
          15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
          8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]
    KL = [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
    KR = [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

    def rol(x, n):
        x &= 0xFFFFFFFF
        return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF

    def f(j, x, y, z):
        if j < 16:
            return x ^ y ^ z
        if j < 32:
            return (x & y) | (~x & z)
        if j < 48:
            return (x | ~y) ^ z
        if j < 64:
            return (x & z) | (y & ~z)
        return x ^ (y | ~z)

    # padding (MD4-style, little-endian bit length)
    msg = bytearray(data)
    bitlen = len(data) * 8
    msg.append(0x80)
    while len(msg) % 64 != 56:
        msg.append(0)
    msg += bitlen.to_bytes(8, "little")

    h = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

    for off in range(0, len(msg), 64):
        X = [int.from_bytes(msg[off + 4 * i:off + 4 * i + 4], "little")
             for i in range(16)]
        al, bl, cl, dl, el = h
        ar, br, cr, dr, er = h
        for j in range(80):
            # left line:  B' = rol(A + f(j,B,C,D) + X[r] + K, s) + E,
            #              A' = E, C' = B, D' = rol(C,10), E' = D
            t = (rol((al + f(j, bl, cl, dl) + X[RL[j]] + KL[j // 16]) & 0xFFFFFFFF,
                     SL[j]) + el) & 0xFFFFFFFF
            al, bl, cl, dl, el = el, t, bl, rol(cl, 10), dl
            # right line (parallel, j reversed and its own tables)
            tr = (rol((ar + f(79 - j, br, cr, dr) + X[RR[j]] + KR[j // 16]) & 0xFFFFFFFF,
                     SR[j]) + er) & 0xFFFFFFFF
            ar, br, cr, dr, er = er, tr, br, rol(cr, 10), dr
        t = (h[1] + cl + dr) & 0xFFFFFFFF
        h[1] = (h[2] + dl + er) & 0xFFFFFFFF
        h[2] = (h[3] + el + ar) & 0xFFFFFFFF
        h[3] = (h[4] + al + br) & 0xFFFFFFFF
        h[4] = (h[0] + bl + cr) & 0xFFFFFFFF
        h[0] = t
    return b"".join(x.to_bytes(4, "little") for x in h)


def ripemd160(data):
    try:
        return hashlib.new("ripemd160", data).digest()
    except Exception:
        return ripemd160_pure(data)


def hash160(b):
    return ripemd160(sha256(b))


# ---------------------------------------------------------------------------
# Base58 / Base58Check
# ---------------------------------------------------------------------------

B58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58encode(data):
    n = int.from_bytes(data, "big")
    out = []
    while n > 0:
        n, r = divmod(n, 58)
        out.append(B58_ALPHABET[r])
    for byte in data:
        if byte == 0:
            out.append("1")
        else:
            break
    return "".join(reversed(out))


def b58decode(s):
    n = 0
    for ch in s:
        i = B58_ALPHABET.find(ch)
        if i < 0:
            raise ValueError("invalid base58 character %r" % ch)
        n = n * 58 + i
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    pad = 0
    for ch in s:
        if ch == "1":
            pad += 1
        else:
            break
    return b"\x00" * pad + body


def b58check_encode(version, payload):
    return b58encode(version + payload + sha256d(version + payload)[:4])


def b58check_decode(s):
    raw = b58decode(s)
    if len(raw) < 5:
        raise ValueError("base58check string too short")
    payload, checksum = raw[:-4], raw[-4:]
    if sha256d(payload)[:4] != checksum:
        raise ValueError("base58check checksum mismatch")
    return payload


# ---------------------------------------------------------------------------
# Bech32 / Bech32m (BIP173 / BIP350)
# ---------------------------------------------------------------------------

BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
BECH32_CONST = 1
BECH32M_CONST = 0x2BC830A3


def bech32_polymod(values):
    gen = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for v in values:
        top = chk >> 25
        chk = (chk & 0x1FFFFFF) << 5 ^ v
        for i in range(5):
            chk ^= gen[i] if ((top >> i) & 1) else 0
    return chk


def bech32_hrp_expand(hrp):
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]


def bech32_verify_checksum(hrp, data):
    """Return the checksum constant (BECH32_CONST or BECH32M_CONST) or None."""
    chk = bech32_polymod(bech32_hrp_expand(hrp) + data)
    if chk in (BECH32_CONST, BECH32M_CONST):
        return chk
    return None


def bech32_create_checksum(hrp, data, const):
    values = bech32_hrp_expand(hrp) + data
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ const
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]


def bech32_encode(hrp, data, const=BECH32_CONST):
    combined = data + bech32_create_checksum(hrp, data, const)
    return hrp + "1" + "".join(BECH32_CHARSET[d] for d in combined)


def bech32_decode(s):
    if s != s.lower() and s != s.upper():
        raise ValueError("mixed-case bech32 string")
    s = s.lower()
    pos = s.rfind("1")
    if pos < 1 or pos + 7 > len(s):
        raise ValueError("invalid bech32 separator position")
    hrp = s[:pos]
    if not all(33 <= ord(c) <= 126 for c in hrp):
        raise ValueError("invalid bech32 hrp character")
    data = []
    for ch in s[pos + 1:]:
        i = BECH32_CHARSET.find(ch)
        if i < 0:
            raise ValueError("invalid bech32 data character %r" % ch)
        data.append(i)
    const = bech32_verify_checksum(hrp, data)
    if const is None:
        raise ValueError("bech32 checksum failed")
    return hrp, data[:-6], const


def convertbits(data, frombits, tobits, pad=True):
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    max_acc = (1 << (frombits + tobits - 1)) - 1
    for value in data:
        if value < 0 or (value >> frombits):
            return None
        acc = ((acc << frombits) | value) & max_acc
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad:
        if bits:
            ret.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return ret


def segwit_encode(hrp, witver, witprog):
    const = BECH32_CONST if witver == 0 else BECH32M_CONST
    data = [witver] + convertbits(witprog, 8, 5)
    return bech32_encode(hrp, data, const)


def segwit_decode(s):
    """Return (hrp, witver, witprog) for a segwit address string."""
    hrp, data, const = bech32_decode(s)
    if not data:
        raise ValueError("empty segwit witness program")
    witver = data[0]
    if witver > 16:
        raise ValueError("invalid segwit version")
    if witver == 0 and const != BECH32_CONST:
        raise ValueError("witness version 0 must use bech32 (not bech32m)")
    if witver >= 1 and const != BECH32M_CONST:
        raise ValueError("witness version >=1 must use bech32m (not bech32)")
    prog = convertbits(data[1:], 5, 8, False)
    if prog is None:
        raise ValueError("invalid padding in segwit address")
    if len(prog) < 2 or len(prog) > 40:
        raise ValueError("invalid segwit program length")
    if witver == 0 and len(prog) not in (20, 32):
        raise ValueError("invalid v0 program length")
    return hrp, witver, bytes(prog)


# ---------------------------------------------------------------------------
# secp256k1
# ---------------------------------------------------------------------------

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

G = (GX, GY)


def point_add(p1, p2):
    """Affine point addition; None is the point at infinity."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2:
        if (y1 + y2) % P == 0:
            return None
        return point_double(p1)
    lam = ((y2 - y1) * pow(x2 - x1, -1, P)) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def point_double(pt):
    if pt is None or pt[1] % P == 0:
        return None
    x, y = pt
    lam = (3 * x * x * pow(2 * y, -1, P)) % P
    x3 = (lam * lam - 2 * x) % P
    y3 = (lam * (x - x3) - y) % P
    return (x3, y3)


def point_double_jac(X, Y, Z):
    """Double a Jacobian point (x = X/Z^2, y = Y/Z^3). (0,1,0) is infinity."""
    if Z == 0 or Y == 0:
        return (0, 1, 0)
    A = (X * X) % P
    B = (Y * Y) % P
    C = (B * B) % P
    t = (X + B) % P
    D = ((t * t - A - C) * 2) % P
    E = (3 * A) % P
    F = (E * E) % P
    X3 = (F - 2 * D) % P
    Y3 = (E * (D - X3) - 8 * C) % P
    Z3 = (2 * Y * Z) % P
    return (X3, Y3, Z3)


def scalar_mult(k, pt=G):
    """Double-and-add in Jacobian coordinates (no per-step inversion)."""
    if pt is None or k % N == 0:
        return None
    k %= N
    X, Y, Z = 0, 1, 0          # infinity
    QX, QY = pt
    for i in range(k.bit_length() - 1, -1, -1):
        X, Y, Z = point_double_jac(X, Y, Z)
        if (k >> i) & 1:
            if Z == 0:
                X, Y, Z = QX, QY, 1
                continue
            Z1Z1 = (Z * Z) % P
            U1 = (X * 1) % P          # U1 = X1 * Z2^2, Z2 = 1
            U2 = (QX * Z1Z1) % P
            S1 = (Y * 1 * 1) % P      # S1 = Y1 * Z2^3, Z2 = 1
            S2 = (QY * Z1Z1 * Z) % P
            if U1 == U2:
                if S1 != S2:
                    return None
                X, Y, Z = point_double_jac(X, Y, Z)
                continue
            H = (U2 - U1) % P
            R = (S2 - S1) % P
            H2 = (H * H) % P
            H3 = (H2 * H) % P
            U1H2 = (U1 * H2) % P
            X3 = (R * R - H3 - 2 * U1H2) % P
            Y3 = (R * (U1H2 - X3) - S1 * H3) % P
            Z3 = (Z * H) % P
            X, Y, Z = X3, Y3, Z3
    if Z == 0:
        return None
    Zi = pow(Z, -1, P)
    Zi2 = (Zi * Zi) % P
    return ((X * Zi2) % P, (Y * Zi2 * Zi) % P)


def on_curve(pt):
    if pt is None:
        return True
    x, y = pt
    return (y * y - (x * x * x + 7)) % P == 0


# ---------------------------------------------------------------------------
# ECDSA (deterministic RFC 6979) + recovery
# ---------------------------------------------------------------------------

def _rfc6979_k(z_int, x_int):
    x_b = x_int.to_bytes(32, "big")
    h1_b = (z_int % N).to_bytes(32, "big")
    V = b"\x01" * 32
    K = b"\x00" * 32
    K = hmac.new(K, V + b"\x00" + x_b + h1_b, hashlib.sha256).digest()
    V = hmac.new(K, V, hashlib.sha256).digest()
    K = hmac.new(K, V + b"\x01" + x_b + h1_b, hashlib.sha256).digest()
    V = hmac.new(K, V, hashlib.sha256).digest()
    while True:
        V = hmac.new(K, V, hashlib.sha256).digest()
        k = int.from_bytes(V, "big")
        if 1 <= k < N:
            return k
        K = hmac.new(K, V + b"\x00", hashlib.sha256).digest()
        V = hmac.new(K, V, hashlib.sha256).digest()


def ecdsa_sign(priv_int, digest32):
    """Deterministic (RFC 6979) ECDSA over a 32-byte digest.

    Returns (r, s, recid) where recid encodes the recovery information
    (bit0 = y-parity of R, bit1 = R.x >= n).  s is normalised to low-s,
    as Bitcoin Core does.
    """
    z = int.from_bytes(digest32, "big")
    while True:
        k = _rfc6979_k(z, priv_int)
        R = scalar_mult(k, G)
        r = R[0] % N
        if r == 0:
            z += 1  # re-step; practically unreachable
            continue
        s = (pow(k, -1, N) * (z + r * priv_int)) % N
        recid = (R[1] & 1) | (2 if R[0] >= N else 0)
        if s == 0:
            z += 1
            continue
        if s > N // 2:
            s = N - s
            recid ^= 1
        return r, s, recid


def ecdsa_verify(pub_pt, digest32, r, s):
    if not (1 <= r < N and 1 <= s < N):
        return False
    if pub_pt is None or not on_curve(pub_pt):
        return False
    z = int.from_bytes(digest32, "big")
    w = pow(s, -1, N)
    u1 = (z * w) % N
    u2 = (r * w) % N
    Xpt = point_add(scalar_mult(u1, G), scalar_mult(u2, pub_pt))
    if Xpt is None:
        return False
    return Xpt[0] % N == r


def recover_pubkey(digest32, r, s, recid):
    """Recover the public key point from a (r, s, recid) signature."""
    if not (0 <= recid <= 3):
        return None
    if not (1 <= r < N and 1 <= s < N):
        return None
    x = r + (N if recid & 2 else 0)
    if x >= P:
        return None
    y_sq = (pow(x, 3, P) + 7) % P
    y = pow(y_sq, (P + 1) // 4, P)
    if (y * y) % P != y_sq:
        return None
    if (y & 1) != (recid & 1):
        y = P - y
    R = (x, y)
    z = int.from_bytes(digest32, "big")
    r_inv = pow(r, -1, N)
    Q = point_add(scalar_mult((s * r_inv) % N, R),
                  scalar_mult((-z * r_inv) % N, G))
    if Q is None or not on_curve(Q):
        return None
    if not ecdsa_verify(Q, digest32, r, s):
        return None
    return Q


# ---------------------------------------------------------------------------
# Public-key serialisation, WIF, addresses
# ---------------------------------------------------------------------------

def compress_pub(pt):
    return bytes([2 + (pt[1] & 1)]) + pt[0].to_bytes(32, "big")


def decompress_pub(b):
    if len(b) != 33 or b[0] not in (2, 3):
        raise ValueError("invalid compressed pubkey")
    x = int.from_bytes(b[1:], "big")
    if x >= P:
        raise ValueError("pubkey x out of range")
    y_sq = (pow(x, 3, P) + 7) % P
    y = pow(y_sq, (P + 1) // 4, P)
    if (y * y) % P != y_sq:
        raise ValueError("pubkey not on curve")
    if (y & 1) != (b[0] & 1):
        y = P - y
    pt = (x, y)
    if not on_curve(pt):
        raise ValueError("pubkey not on curve")
    return pt


def uncompressed_pub(pt):
    return b"\x04" + pt[0].to_bytes(32, "big") + pt[1].to_bytes(32, "big")


def wif_decode(wif):
    payload = b58check_decode(wif)
    version, key = payload[0], payload[1:]
    compressed = False
    if len(key) == 33 and key[32] == 1:
        compressed = True
        key = key[:32]
    if len(key) != 32:
        raise ValueError("invalid WIF payload length")
    k = int.from_bytes(key, "big")
    if not (1 <= k < N):
        raise ValueError("WIF key out of range")
    return k, compressed, version


def wif_encode(k, compressed=True, version=0x80):
    payload = version + k.to_bytes(32, "big")
    if compressed:
        payload += b"\x01"
    return b58encode(payload + sha256d(payload)[:4])


# address version bytes
VER_P2PKH_MAIN, VER_P2SH_MAIN = 0x00, 0x05
VER_P2PKH_TEST, VER_P2SH_TEST = 0x6F, 0xC4


def p2pkh_address(pub_bytes, testnet=False):
    ver = VER_P2PKH_TEST if testnet else VER_P2PKH_MAIN
    return b58check_encode(bytes([ver]), hash160(pub_bytes))


def p2sh_p2wpkh_address(pub_bytes, testnet=False):
    redeem = b"\x00\x14" + hash160(pub_bytes)
    ver = VER_P2SH_TEST if testnet else VER_P2SH_MAIN
    return b58check_encode(bytes([ver]), hash160(redeem))


def p2wpkh_address(pub_bytes, testnet=False):
    return segwit_encode("tb" if testnet else "bc", 0, hash160(pub_bytes))


def all_addresses(pub_pt, testnet=False):
    comp = compress_pub(pub_pt)
    uncomp = uncompressed_pub(pub_pt)
    return {
        "p2pkh-compressed": p2pkh_address(comp, testnet),
        "p2pkh-uncompressed": p2pkh_address(uncomp, testnet),
        "p2sh-p2wpkh": p2sh_p2wpkh_address(comp, testnet),
        "p2wpkh": p2wpkh_address(comp, testnet),
    }


def classify_address(addr):
    """Return a description of an address string, or raise ValueError."""
    if addr.lower().startswith("bc1") or addr.lower().startswith("tb1"):
        hrp, witver, prog = segwit_decode(addr)
        if witver == 0 and len(prog) == 20:
            return {"type": "p2wpkh", "hrp": hrp, "program": prog}
        if witver == 0 and len(prog) == 32:
            return {"type": "p2wsh", "hrp": hrp, "program": prog}
        return {"type": "p2tr" if witver == 1 else "segwit-v%d" % witver,
                "hrp": hrp, "program": prog}
    payload = b58check_decode(addr)
    ver, prog = payload[0], payload[1:]
    if len(prog) != 20:
        raise ValueError("base58 address payload must be 20 bytes")
    if ver == VER_P2PKH_MAIN:
        return {"type": "p2pkh", "testnet": False, "program": prog}
    if ver == VER_P2PKH_TEST:
        return {"type": "p2pkh", "testnet": True, "program": prog}
    if ver == VER_P2SH_MAIN:
        return {"type": "p2sh", "testnet": False, "program": prog}
    if ver == VER_P2SH_TEST:
        return {"type": "p2sh", "testnet": True, "program": prog}
    raise ValueError("unknown base58 version byte 0x%02x" % ver)


# ---------------------------------------------------------------------------
# Bitcoin signed-message format
# ---------------------------------------------------------------------------

MSG_MAGIC = b"\x18Bitcoin Signed Message:\n"


def _varint(n):
    if n < 253:
        return bytes([n])
    if n <= 0xFFFF:
        return b"\xfd" + n.to_bytes(2, "little")
    if n <= 0xFFFFFFFF:
        return b"\xfe" + n.to_bytes(4, "little")
    return b"\xff" + n.to_bytes(8, "little")


def message_digest(message_bytes):
    return sha256d(MSG_MAGIC + _varint(len(message_bytes)) + message_bytes)


def sign_message(priv_int, message, compressed=True):
    """Return the 65-byte recoverable signature (header + r + s)."""
    digest = message_digest(message.encode("utf-8") if isinstance(message, str)
                            else message)
    r, s, recid = ecdsa_sign(priv_int, digest)
    header = 27 + recid + (4 if compressed else 0)
    return bytes([header]) + r.to_bytes(32, "big") + s.to_bytes(32, "big")


def decode_message_signature(sig_str):
    """Accept base64 (Bitcoin Core / Electrum) or base58 (legacy) 65-byte sig."""
    raw = None
    try:
        import base64
        raw = base64.b64decode(sig_str, validate=True)
    except Exception:
        raw = None
    if raw is None or len(raw) != 65:
        try:
            raw = b58decode(sig_str.strip())
        except Exception:
            raise ValueError("signature is neither valid base64 nor base58")
    if len(raw) != 65:
        raise ValueError("signature must decode to exactly 65 bytes")
    header = raw[0]
    if not (27 <= header <= 34):
        raise ValueError("invalid signature header byte %d" % header)
    return raw


def recover_from_message_signature(sig_str, message):
    """Returns (pubkey_point, compressed_flag, info_dict) or raises ValueError."""
    raw = decode_message_signature(sig_str)
    header = raw[0]
    compressed = header >= 31
    recid = (header - 27) & 3
    r = int.from_bytes(raw[1:33], "big")
    s = int.from_bytes(raw[33:65], "big")
    digest = message_digest(message.encode("utf-8") if isinstance(message, str)
                            else message)
    pt = recover_pubkey(digest, r, s, recid)
    if pt is None:
        raise ValueError("signature recovery failed (wrong message or "
                         "corrupt signature)")
    return pt, compressed


def verify_message(sig_str, message, address):
    """True iff the signature recovers to a key matching the address."""
    try:
        info = classify_address(address)
    except ValueError as e:
        raise ValueError("cannot use address %r: %s" % (address, e))
    try:
        pt, compressed = recover_from_message_signature(sig_str, message)
    except ValueError:
        return False  # recovery failed: wrong message or corrupt signature

    if info["type"] == "p2tr" or info["type"].startswith("segwit-v"):
        return False  # taproot/other: not verifiable with ECDSA message sigs
    if info["type"] == "p2wpkh":
        if not compressed:
            return False
        hrp = info["hrp"]
        if hrp not in ("bc", "tb"):
            return False
        return segwit_encode(hrp, 0, hash160(compress_pub(pt))) == address
    if info["type"] == "p2wsh":
        return False  # a bare script address is not a single-key proof
    testnet = info["testnet"]
    if info["type"] == "p2pkh":
        key = compress_pub(pt) if compressed else uncompressed_pub(pt)
        return p2pkh_address(key, testnet) == address
    if info["type"] == "p2sh":
        if not compressed:
            return False
        return p2sh_p2wpkh_address(compress_pub(pt), testnet) == address
    return False


# ---------------------------------------------------------------------------
# BIP39
# ---------------------------------------------------------------------------

# Official BIP39 English wordlist (2048 words), verbatim from
# bitcoin/bips bip-0039/english.txt (SHA-256 2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda).
WORDLIST = (
    "abandon", "ability", "able", "about", "above", "absent", "absorb", "abstract", "absurd", "abuse",
    "access", "accident", "account", "accuse", "achieve", "acid", "acoustic", "acquire", "across", "act",
    "action", "actor", "actress", "actual", "adapt", "add", "addict", "address", "adjust", "admit",
    "adult", "advance", "advice", "aerobic", "affair", "afford", "afraid", "again", "age", "agent",
    "agree", "ahead", "aim", "air", "airport", "aisle", "alarm", "album", "alcohol", "alert",
    "alien", "all", "alley", "allow", "almost", "alone", "alpha", "already", "also", "alter",
    "always", "amateur", "amazing", "among", "amount", "amused", "analyst", "anchor", "ancient", "anger",
    "angle", "angry", "animal", "ankle", "announce", "annual", "another", "answer", "antenna", "antique",
    "anxiety", "any", "apart", "apology", "appear", "apple", "approve", "april", "arch", "arctic",
    "area", "arena", "argue", "arm", "armed", "armor", "army", "around", "arrange", "arrest",
    "arrive", "arrow", "art", "artefact", "artist", "artwork", "ask", "aspect", "assault", "asset",
    "assist", "assume", "asthma", "athlete", "atom", "attack", "attend", "attitude", "attract", "auction",
    "audit", "august", "aunt", "author", "auto", "autumn", "average", "avocado", "avoid", "awake",
    "aware", "away", "awesome", "awful", "awkward", "axis", "baby", "bachelor", "bacon", "badge",
    "bag", "balance", "balcony", "ball", "bamboo", "banana", "banner", "bar", "barely", "bargain",
    "barrel", "base", "basic", "basket", "battle", "beach", "bean", "beauty", "because", "become",
    "beef", "before", "begin", "behave", "behind", "believe", "below", "belt", "bench", "benefit",
    "best", "betray", "better", "between", "beyond", "bicycle", "bid", "bike", "bind", "biology",
    "bird", "birth", "bitter", "black", "blade", "blame", "blanket", "blast", "bleak", "bless",
    "blind", "blood", "blossom", "blouse", "blue", "blur", "blush", "board", "boat", "body",
    "boil", "bomb", "bone", "bonus", "book", "boost", "border", "boring", "borrow", "boss",
    "bottom", "bounce", "box", "boy", "bracket", "brain", "brand", "brass", "brave", "bread",
    "breeze", "brick", "bridge", "brief", "bright", "bring", "brisk", "broccoli", "broken", "bronze",
    "broom", "brother", "brown", "brush", "bubble", "buddy", "budget", "buffalo", "build", "bulb",
    "bulk", "bullet", "bundle", "bunker", "burden", "burger", "burst", "bus", "business", "busy",
    "butter", "buyer", "buzz", "cabbage", "cabin", "cable", "cactus", "cage", "cake", "call",
    "calm", "camera", "camp", "can", "canal", "cancel", "candy", "cannon", "canoe", "canvas",
    "canyon", "capable", "capital", "captain", "car", "carbon", "card", "cargo", "carpet", "carry",
    "cart", "case", "cash", "casino", "castle", "casual", "cat", "catalog", "catch", "category",
    "cattle", "caught", "cause", "caution", "cave", "ceiling", "celery", "cement", "census", "century",
    "cereal", "certain", "chair", "chalk", "champion", "change", "chaos", "chapter", "charge", "chase",
    "chat", "cheap", "check", "cheese", "chef", "cherry", "chest", "chicken", "chief", "child",
    "chimney", "choice", "choose", "chronic", "chuckle", "chunk", "churn", "cigar", "cinnamon", "circle",
    "citizen", "city", "civil", "claim", "clap", "clarify", "claw", "clay", "clean", "clerk",
    "clever", "click", "client", "cliff", "climb", "clinic", "clip", "clock", "clog", "close",
    "cloth", "cloud", "clown", "club", "clump", "cluster", "clutch", "coach", "coast", "coconut",
    "code", "coffee", "coil", "coin", "collect", "color", "column", "combine", "come", "comfort",
    "comic", "common", "company", "concert", "conduct", "confirm", "congress", "connect", "consider", "control",
    "convince", "cook", "cool", "copper", "copy", "coral", "core", "corn", "correct", "cost",
    "cotton", "couch", "country", "couple", "course", "cousin", "cover", "coyote", "crack", "cradle",
    "craft", "cram", "crane", "crash", "crater", "crawl", "crazy", "cream", "credit", "creek",
    "crew", "cricket", "crime", "crisp", "critic", "crop", "cross", "crouch", "crowd", "crucial",
    "cruel", "cruise", "crumble", "crunch", "crush", "cry", "crystal", "cube", "culture", "cup",
    "cupboard", "curious", "current", "curtain", "curve", "cushion", "custom", "cute", "cycle", "dad",
    "damage", "damp", "dance", "danger", "daring", "dash", "daughter", "dawn", "day", "deal",
    "debate", "debris", "decade", "december", "decide", "decline", "decorate", "decrease", "deer", "defense",
    "define", "defy", "degree", "delay", "deliver", "demand", "demise", "denial", "dentist", "deny",
    "depart", "depend", "deposit", "depth", "deputy", "derive", "describe", "desert", "design", "desk",
    "despair", "destroy", "detail", "detect", "develop", "device", "devote", "diagram", "dial", "diamond",
    "diary", "dice", "diesel", "diet", "differ", "digital", "dignity", "dilemma", "dinner", "dinosaur",
    "direct", "dirt", "disagree", "discover", "disease", "dish", "dismiss", "disorder", "display", "distance",
    "divert", "divide", "divorce", "dizzy", "doctor", "document", "dog", "doll", "dolphin", "domain",
    "donate", "donkey", "donor", "door", "dose", "double", "dove", "draft", "dragon", "drama",
    "drastic", "draw", "dream", "dress", "drift", "drill", "drink", "drip", "drive", "drop",
    "drum", "dry", "duck", "dumb", "dune", "during", "dust", "dutch", "duty", "dwarf",
    "dynamic", "eager", "eagle", "early", "earn", "earth", "easily", "east", "easy", "echo",
    "ecology", "economy", "edge", "edit", "educate", "effort", "egg", "eight", "either", "elbow",
    "elder", "electric", "elegant", "element", "elephant", "elevator", "elite", "else", "embark", "embody",
    "embrace", "emerge", "emotion", "employ", "empower", "empty", "enable", "enact", "end", "endless",
    "endorse", "enemy", "energy", "enforce", "engage", "engine", "enhance", "enjoy", "enlist", "enough",
    "enrich", "enroll", "ensure", "enter", "entire", "entry", "envelope", "episode", "equal", "equip",
    "era", "erase", "erode", "erosion", "error", "erupt", "escape", "essay", "essence", "estate",
    "eternal", "ethics", "evidence", "evil", "evoke", "evolve", "exact", "example", "excess", "exchange",
    "excite", "exclude", "excuse", "execute", "exercise", "exhaust", "exhibit", "exile", "exist", "exit",
    "exotic", "expand", "expect", "expire", "explain", "expose", "express", "extend", "extra", "eye",
    "eyebrow", "fabric", "face", "faculty", "fade", "faint", "faith", "fall", "false", "fame",
    "family", "famous", "fan", "fancy", "fantasy", "farm", "fashion", "fat", "fatal", "father",
    "fatigue", "fault", "favorite", "feature", "february", "federal", "fee", "feed", "feel", "female",
    "fence", "festival", "fetch", "fever", "few", "fiber", "fiction", "field", "figure", "file",
    "film", "filter", "final", "find", "fine", "finger", "finish", "fire", "firm", "first",
    "fiscal", "fish", "fit", "fitness", "fix", "flag", "flame", "flash", "flat", "flavor",
    "flee", "flight", "flip", "float", "flock", "floor", "flower", "fluid", "flush", "fly",
    "foam", "focus", "fog", "foil", "fold", "follow", "food", "foot", "force", "forest",
    "forget", "fork", "fortune", "forum", "forward", "fossil", "foster", "found", "fox", "fragile",
    "frame", "frequent", "fresh", "friend", "fringe", "frog", "front", "frost", "frown", "frozen",
    "fruit", "fuel", "fun", "funny", "furnace", "fury", "future", "gadget", "gain", "galaxy",
    "gallery", "game", "gap", "garage", "garbage", "garden", "garlic", "garment", "gas", "gasp",
    "gate", "gather", "gauge", "gaze", "general", "genius", "genre", "gentle", "genuine", "gesture",
    "ghost", "giant", "gift", "giggle", "ginger", "giraffe", "girl", "give", "glad", "glance",
    "glare", "glass", "glide", "glimpse", "globe", "gloom", "glory", "glove", "glow", "glue",
    "goat", "goddess", "gold", "good", "goose", "gorilla", "gospel", "gossip", "govern", "gown",
    "grab", "grace", "grain", "grant", "grape", "grass", "gravity", "great", "green", "grid",
    "grief", "grit", "grocery", "group", "grow", "grunt", "guard", "guess", "guide", "guilt",
    "guitar", "gun", "gym", "habit", "hair", "half", "hammer", "hamster", "hand", "happy",
    "harbor", "hard", "harsh", "harvest", "hat", "have", "hawk", "hazard", "head", "health",
    "heart", "heavy", "hedgehog", "height", "hello", "helmet", "help", "hen", "hero", "hidden",
    "high", "hill", "hint", "hip", "hire", "history", "hobby", "hockey", "hold", "hole",
    "holiday", "hollow", "home", "honey", "hood", "hope", "horn", "horror", "horse", "hospital",
    "host", "hotel", "hour", "hover", "hub", "huge", "human", "humble", "humor", "hundred",
    "hungry", "hunt", "hurdle", "hurry", "hurt", "husband", "hybrid", "ice", "icon", "idea",
    "identify", "idle", "ignore", "ill", "illegal", "illness", "image", "imitate", "immense", "immune",
    "impact", "impose", "improve", "impulse", "inch", "include", "income", "increase", "index", "indicate",
    "indoor", "industry", "infant", "inflict", "inform", "inhale", "inherit", "initial", "inject", "injury",
    "inmate", "inner", "innocent", "input", "inquiry", "insane", "insect", "inside", "inspire", "install",
    "intact", "interest", "into", "invest", "invite", "involve", "iron", "island", "isolate", "issue",
    "item", "ivory", "jacket", "jaguar", "jar", "jazz", "jealous", "jeans", "jelly", "jewel",
    "job", "join", "joke", "journey", "joy", "judge", "juice", "jump", "jungle", "junior",
    "junk", "just", "kangaroo", "keen", "keep", "ketchup", "key", "kick", "kid", "kidney",
    "kind", "kingdom", "kiss", "kit", "kitchen", "kite", "kitten", "kiwi", "knee", "knife",
    "knock", "know", "lab", "label", "labor", "ladder", "lady", "lake", "lamp", "language",
    "laptop", "large", "later", "latin", "laugh", "laundry", "lava", "law", "lawn", "lawsuit",
    "layer", "lazy", "leader", "leaf", "learn", "leave", "lecture", "left", "leg", "legal",
    "legend", "leisure", "lemon", "lend", "length", "lens", "leopard", "lesson", "letter", "level",
    "liar", "liberty", "library", "license", "life", "lift", "light", "like", "limb", "limit",
    "link", "lion", "liquid", "list", "little", "live", "lizard", "load", "loan", "lobster",
    "local", "lock", "logic", "lonely", "long", "loop", "lottery", "loud", "lounge", "love",
    "loyal", "lucky", "luggage", "lumber", "lunar", "lunch", "luxury", "lyrics", "machine", "mad",
    "magic", "magnet", "maid", "mail", "main", "major", "make", "mammal", "man", "manage",
    "mandate", "mango", "mansion", "manual", "maple", "marble", "march", "margin", "marine", "market",
    "marriage", "mask", "mass", "master", "match", "material", "math", "matrix", "matter", "maximum",
    "maze", "meadow", "mean", "measure", "meat", "mechanic", "medal", "media", "melody", "melt",
    "member", "memory", "mention", "menu", "mercy", "merge", "merit", "merry", "mesh", "message",
    "metal", "method", "middle", "midnight", "milk", "million", "mimic", "mind", "minimum", "minor",
    "minute", "miracle", "mirror", "misery", "miss", "mistake", "mix", "mixed", "mixture", "mobile",
    "model", "modify", "mom", "moment", "monitor", "monkey", "monster", "month", "moon", "moral",
    "more", "morning", "mosquito", "mother", "motion", "motor", "mountain", "mouse", "move", "movie",
    "much", "muffin", "mule", "multiply", "muscle", "museum", "mushroom", "music", "must", "mutual",
    "myself", "mystery", "myth", "naive", "name", "napkin", "narrow", "nasty", "nation", "nature",
    "near", "neck", "need", "negative", "neglect", "neither", "nephew", "nerve", "nest", "net",
    "network", "neutral", "never", "news", "next", "nice", "night", "noble", "noise", "nominee",
    "noodle", "normal", "north", "nose", "notable", "note", "nothing", "notice", "novel", "now",
    "nuclear", "number", "nurse", "nut", "oak", "obey", "object", "oblige", "obscure", "observe",
    "obtain", "obvious", "occur", "ocean", "october", "odor", "off", "offer", "office", "often",
    "oil", "okay", "old", "olive", "olympic", "omit", "once", "one", "onion", "online",
    "only", "open", "opera", "opinion", "oppose", "option", "orange", "orbit", "orchard", "order",
    "ordinary", "organ", "orient", "original", "orphan", "ostrich", "other", "outdoor", "outer", "output",
    "outside", "oval", "oven", "over", "own", "owner", "oxygen", "oyster", "ozone", "pact",
    "paddle", "page", "pair", "palace", "palm", "panda", "panel", "panic", "panther", "paper",
    "parade", "parent", "park", "parrot", "party", "pass", "patch", "path", "patient", "patrol",
    "pattern", "pause", "pave", "payment", "peace", "peanut", "pear", "peasant", "pelican", "pen",
    "penalty", "pencil", "people", "pepper", "perfect", "permit", "person", "pet", "phone", "photo",
    "phrase", "physical", "piano", "picnic", "picture", "piece", "pig", "pigeon", "pill", "pilot",
    "pink", "pioneer", "pipe", "pistol", "pitch", "pizza", "place", "planet", "plastic", "plate",
    "play", "please", "pledge", "pluck", "plug", "plunge", "poem", "poet", "point", "polar",
    "pole", "police", "pond", "pony", "pool", "popular", "portion", "position", "possible", "post",
    "potato", "pottery", "poverty", "powder", "power", "practice", "praise", "predict", "prefer", "prepare",
    "present", "pretty", "prevent", "price", "pride", "primary", "print", "priority", "prison", "private",
    "prize", "problem", "process", "produce", "profit", "program", "project", "promote", "proof", "property",
    "prosper", "protect", "proud", "provide", "public", "pudding", "pull", "pulp", "pulse", "pumpkin",
    "punch", "pupil", "puppy", "purchase", "purity", "purpose", "purse", "push", "put", "puzzle",
    "pyramid", "quality", "quantum", "quarter", "question", "quick", "quit", "quiz", "quote", "rabbit",
    "raccoon", "race", "rack", "radar", "radio", "rail", "rain", "raise", "rally", "ramp",
    "ranch", "random", "range", "rapid", "rare", "rate", "rather", "raven", "raw", "razor",
    "ready", "real", "reason", "rebel", "rebuild", "recall", "receive", "recipe", "record", "recycle",
    "reduce", "reflect", "reform", "refuse", "region", "regret", "regular", "reject", "relax", "release",
    "relief", "rely", "remain", "remember", "remind", "remove", "render", "renew", "rent", "reopen",
    "repair", "repeat", "replace", "report", "require", "rescue", "resemble", "resist", "resource", "response",
    "result", "retire", "retreat", "return", "reunion", "reveal", "review", "reward", "rhythm", "rib",
    "ribbon", "rice", "rich", "ride", "ridge", "rifle", "right", "rigid", "ring", "riot",
    "ripple", "risk", "ritual", "rival", "river", "road", "roast", "robot", "robust", "rocket",
    "romance", "roof", "rookie", "room", "rose", "rotate", "rough", "round", "route", "royal",
    "rubber", "rude", "rug", "rule", "run", "runway", "rural", "sad", "saddle", "sadness",
    "safe", "sail", "salad", "salmon", "salon", "salt", "salute", "same", "sample", "sand",
    "satisfy", "satoshi", "sauce", "sausage", "save", "say", "scale", "scan", "scare", "scatter",
    "scene", "scheme", "school", "science", "scissors", "scorpion", "scout", "scrap", "screen", "script",
    "scrub", "sea", "search", "season", "seat", "second", "secret", "section", "security", "seed",
    "seek", "segment", "select", "sell", "seminar", "senior", "sense", "sentence", "series", "service",
    "session", "settle", "setup", "seven", "shadow", "shaft", "shallow", "share", "shed", "shell",
    "sheriff", "shield", "shift", "shine", "ship", "shiver", "shock", "shoe", "shoot", "shop",
    "short", "shoulder", "shove", "shrimp", "shrug", "shuffle", "shy", "sibling", "sick", "side",
    "siege", "sight", "sign", "silent", "silk", "silly", "silver", "similar", "simple", "since",
    "sing", "siren", "sister", "situate", "six", "size", "skate", "sketch", "ski", "skill",
    "skin", "skirt", "skull", "slab", "slam", "sleep", "slender", "slice", "slide", "slight",
    "slim", "slogan", "slot", "slow", "slush", "small", "smart", "smile", "smoke", "smooth",
    "snack", "snake", "snap", "sniff", "snow", "soap", "soccer", "social", "sock", "soda",
    "soft", "solar", "soldier", "solid", "solution", "solve", "someone", "song", "soon", "sorry",
    "sort", "soul", "sound", "soup", "source", "south", "space", "spare", "spatial", "spawn",
    "speak", "special", "speed", "spell", "spend", "sphere", "spice", "spider", "spike", "spin",
    "spirit", "split", "spoil", "sponsor", "spoon", "sport", "spot", "spray", "spread", "spring",
    "spy", "square", "squeeze", "squirrel", "stable", "stadium", "staff", "stage", "stairs", "stamp",
    "stand", "start", "state", "stay", "steak", "steel", "stem", "step", "stereo", "stick",
    "still", "sting", "stock", "stomach", "stone", "stool", "story", "stove", "strategy", "street",
    "strike", "strong", "struggle", "student", "stuff", "stumble", "style", "subject", "submit", "subway",
    "success", "such", "sudden", "suffer", "sugar", "suggest", "suit", "summer", "sun", "sunny",
    "sunset", "super", "supply", "supreme", "sure", "surface", "surge", "surprise", "surround", "survey",
    "suspect", "sustain", "swallow", "swamp", "swap", "swarm", "swear", "sweet", "swift", "swim",
    "swing", "switch", "sword", "symbol", "symptom", "syrup", "system", "table", "tackle", "tag",
    "tail", "talent", "talk", "tank", "tape", "target", "task", "taste", "tattoo", "taxi",
    "teach", "team", "tell", "ten", "tenant", "tennis", "tent", "term", "test", "text",
    "thank", "that", "theme", "then", "theory", "there", "they", "thing", "this", "thought",
    "three", "thrive", "throw", "thumb", "thunder", "ticket", "tide", "tiger", "tilt", "timber",
    "time", "tiny", "tip", "tired", "tissue", "title", "toast", "tobacco", "today", "toddler",
    "toe", "together", "toilet", "token", "tomato", "tomorrow", "tone", "tongue", "tonight", "tool",
    "tooth", "top", "topic", "topple", "torch", "tornado", "tortoise", "toss", "total", "tourist",
    "toward", "tower", "town", "toy", "track", "trade", "traffic", "tragic", "train", "transfer",
    "trap", "trash", "travel", "tray", "treat", "tree", "trend", "trial", "tribe", "trick",
    "trigger", "trim", "trip", "trophy", "trouble", "truck", "true", "truly", "trumpet", "trust",
    "truth", "try", "tube", "tuition", "tumble", "tuna", "tunnel", "turkey", "turn", "turtle",
    "twelve", "twenty", "twice", "twin", "twist", "two", "type", "typical", "ugly", "umbrella",
    "unable", "unaware", "uncle", "uncover", "under", "undo", "unfair", "unfold", "unhappy", "uniform",
    "unique", "unit", "universe", "unknown", "unlock", "until", "unusual", "unveil", "update", "upgrade",
    "uphold", "upon", "upper", "upset", "urban", "urge", "usage", "use", "used", "useful",
    "useless", "usual", "utility", "vacant", "vacuum", "vague", "valid", "valley", "valve", "van",
    "vanish", "vapor", "various", "vast", "vault", "vehicle", "velvet", "vendor", "venture", "venue",
    "verb", "verify", "version", "very", "vessel", "veteran", "viable", "vibrant", "vicious", "victory",
    "video", "view", "village", "vintage", "violin", "virtual", "virus", "visa", "visit", "visual",
    "vital", "vivid", "vocal", "voice", "void", "volcano", "volume", "vote", "voyage", "wage",
    "wagon", "wait", "walk", "wall", "walnut", "want", "warfare", "warm", "warrior", "wash",
    "wasp", "waste", "water", "wave", "way", "wealth", "weapon", "wear", "weasel", "weather",
    "web", "wedding", "weekend", "weird", "welcome", "west", "wet", "whale", "what", "wheat",
    "wheel", "when", "where", "whip", "whisper", "wide", "width", "wife", "wild", "will",
    "win", "window", "wine", "wing", "wink", "winner", "winter", "wire", "wisdom", "wise",
    "wish", "witness", "wolf", "woman", "wonder", "wood", "wool", "word", "work", "world",
    "worry", "worth", "wrap", "wreck", "wrestle", "wrist", "write", "wrong", "yard", "year",
    "yellow", "you", "young", "youth", "zebra", "zero", "zone", "zoo",
)

# Official BIP39 test vectors (English wordlist, passphrase 'TREZOR'),
# from trezor/python-mnemonic vectors.json (linked from the BIP39 spec):
# (mnemonic, seed hex, master xprv)
BIP39_VECTORS = (
    ('abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about', 'c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04', 'xprv9s21ZrQH143K3h3fDYiay8mocZ3afhfULfb5GX8kCBdno77K4HiA15Tg23wpbeF1pLfs1c5SPmYHrEpTuuRhxMwvKDwqdKiGJS9XFKzUsAF'),
    ('legal winner thank year wave sausage worth useful legal winner thank yellow', '2e8905819b8723fe2c1d161860e5ee1830318dbf49a83bd451cfb8440c28bd6fa457fe1296106559a3c80937a1c1069be3a3a5bd381ee6260e8d9739fce1f607', 'xprv9s21ZrQH143K2gA81bYFHqU68xz1cX2APaSq5tt6MFSLeXnCKV1RVUJt9FWNTbrrryem4ZckN8k4Ls1H6nwdvDTvnV7zEXs2HgPezuVccsq'),
    ('letter advice cage absurd amount doctor acoustic avoid letter advice cage above', 'd71de856f81a8acc65e6fc851a38d4d7ec216fd0796d0a6827a3ad6ed5511a30fa280f12eb2e47ed2ac03b5c462a0358d18d69fe4f985ec81778c1b370b652a8', 'xprv9s21ZrQH143K2shfP28KM3nr5Ap1SXjz8gc2rAqqMEynmjt6o1qboCDpxckqXavCwdnYds6yBHZGKHv7ef2eTXy461PXUjBFQg6PrwY4Gzq'),
    ('zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong', 'ac27495480225222079d7be181583751e86f571027b0497b5b5d11218e0a8a13332572917f0f8e5a589620c6f15b11c61dee327651a14c34e18231052e48c069', 'xprv9s21ZrQH143K2V4oox4M8Zmhi2Fjx5XK4Lf7GKRvPSgydU3mjZuKGCTg7UPiBUD7ydVPvSLtg9hjp7MQTYsW67rZHAXeccqYqrsx8LcXnyd'),
    ('abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon agent', '035895f2f481b1b0f01fcf8c289c794660b289981a78f8106447707fdd9666ca06da5a9a565181599b79f53b844d8a71dd9f439c52a3d7b3e8a79c906ac845fa', 'xprv9s21ZrQH143K3mEDrypcZ2usWqFgzKB6jBBx9B6GfC7fu26X6hPRzVjzkqkPvDqp6g5eypdk6cyhGnBngbjeHTe4LsuLG1cCmKJka5SMkmU'),
    ('legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth useful legal will', 'f2b94508732bcbacbcc020faefecfc89feafa6649a5491b8c952cede496c214a0c7b3c392d168748f2d4a612bada0753b52a1c7ac53c1e93abd5c6320b9e95dd', 'xprv9s21ZrQH143K3Lv9MZLj16np5GzLe7tDKQfVusBni7toqJGcnKRtHSxUwbKUyUWiwpK55g1DUSsw76TF1T93VT4gz4wt5RM23pkaQLnvBh7'),
    ('letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic avoid letter always', '107d7c02a5aa6f38c58083ff74f04c607c2d2c0ecc55501dadd72d025b751bc27fe913ffb796f841c49b1d33b610cf0e91d3aa239027f5e99fe4ce9e5088cd65', 'xprv9s21ZrQH143K3VPCbxbUtpkh9pRG371UCLDz3BjceqP1jz7XZsQ5EnNkYAEkfeZp62cDNj13ZTEVG1TEro9sZ9grfRmcYWLBhCocViKEJae'),
    ('zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo when', '0cd6e5d827bb62eb8fc1e262254223817fd068a74b5b449cc2f667c3f1f985a76379b43348d952e2265b4cd129090758b3e3c2c49103b5051aac2eaeb890a528', 'xprv9s21ZrQH143K36Ao5jHRVhFGDbLP6FCx8BEEmpru77ef3bmA928BxsqvVM27WnvvyfWywiFN8K6yToqMaGYfzS6Db1EHAXT5TuyCLBXUfdm'),
    ('abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art', 'bda85446c68413707090a52022edd26a1c9462295029f2e60cd7c4f2bbd3097170af7a4d73245cafa9c3cca8d561a7c3de6f5d4a10be8ed2a5e608d68f92fcc8', 'xprv9s21ZrQH143K32qBagUJAMU2LsHg3ka7jqMcV98Y7gVeVyNStwYS3U7yVVoDZ4btbRNf4h6ibWpY22iRmXq35qgLs79f312g2kj5539ebPM'),
    ('legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth title', 'bc09fca1804f7e69da93c2f2028eb238c227f2e9dda30cd63699232578480a4021b146ad717fbb7e451ce9eb835f43620bf5c514db0f8add49f5d121449d3e87', 'xprv9s21ZrQH143K3Y1sd2XVu9wtqxJRvybCfAetjUrMMco6r3v9qZTBeXiBZkS8JxWbcGJZyio8TrZtm6pkbzG8SYt1sxwNLh3Wx7to5pgiVFU'),
    ('letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic bless', 'c0c519bd0e91a2ed54357d9d1ebef6f5af218a153624cf4f2da911a0ed8f7a09e2ef61af0aca007096df430022f7a2b6fb91661a9589097069720d015e4e982f', 'xprv9s21ZrQH143K3CSnQNYC3MqAAqHwxeTLhDbhF43A4ss4ciWNmCY9zQGvAKUSqVUf2vPHBTSE1rB2pg4avopqSiLVzXEU8KziNnVPauTqLRo'),
    ('zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo vote', 'dd48c104698c30cfe2b6142103248622fb7bb0ff692eebb00089b32d22484e1613912f0a5b694407be899ffd31ed3992c456cdf60f5d4564b8ba3f05a69890ad', 'xprv9s21ZrQH143K2WFF16X85T2QCpndrGwx6GueB72Zf3AHwHJaknRXNF37ZmDrtHrrLSHvbuRejXcnYxoZKvRquTPyp2JiNG3XcjQyzSEgqCB'),
    ('ozone drill grab fiber curtain grace pudding thank cruise elder eight picnic', '274ddc525802f7c828d8ef7ddbcdc5304e87ac3535913611fbbfa986d0c9e5476c91689f9c8a54fd55bd38606aa6a8595ad213d4c9c9f9aca3fb217069a41028', 'xprv9s21ZrQH143K2oZ9stBYpoaZ2ktHj7jLz7iMqpgg1En8kKFTXJHsjxry1JbKH19YrDTicVwKPehFKTbmaxgVEc5TpHdS1aYhB2s9aFJBeJH'),
    ('gravity machine north sort system female filter attitude volume fold club stay feature office ecology stable narrow fog', '628c3827a8823298ee685db84f55caa34b5cc195a778e52d45f59bcf75aba68e4d7590e101dc414bc1bbd5737666fbbef35d1f1903953b66624f910feef245ac', 'xprv9s21ZrQH143K3uT8eQowUjsxrmsA9YUuQQK1RLqFufzybxD6DH6gPY7NjJ5G3EPHjsWDrs9iivSbmvjc9DQJbJGatfa9pv4MZ3wjr8qWPAK'),
    ('hamster diagram private dutch cause delay private meat slide toddler razor book happy fancy gospel tennis maple dilemma loan word shrug inflict delay length', '64c87cde7e12ecf6704ab95bb1408bef047c22db4cc7491c4271d170a1b213d20b385bc1588d9c7b38f1b39d415665b8a9030c9ec653d75e65f847d8fc1fc440', 'xprv9s21ZrQH143K2XTAhys3pMNcGn261Fi5Ta2Pw8PwaVPhg3D8DWkzWQwjTJfskj8ofb81i9NP2cUNKxwjueJHHMQAnxtivTA75uUFqPFeWzk'),
    ('scheme spot photo card baby mountain device kick cradle pact join borrow', 'ea725895aaae8d4c1cf682c1bfd2d358d52ed9f0f0591131b559e2724bb234fca05aa9c02c57407e04ee9dc3b454aa63fbff483a8b11de949624b9f1831a9612', 'xprv9s21ZrQH143K3FperxDp8vFsFycKCRcJGAFmcV7umQmcnMZaLtZRt13QJDsoS5F6oYT6BB4sS6zmTmyQAEkJKxJ7yByDNtRe5asP2jFGhT6'),
    ('horn tenant knee talent sponsor spell gate clip pulse soap slush warm silver nephew swap uncle crack brave', 'fd579828af3da1d32544ce4db5c73d53fc8acc4ddb1e3b251a31179cdb71e853c56d2fcb11aed39898ce6c34b10b5382772db8796e52837b54468aeb312cfc3d', 'xprv9s21ZrQH143K3R1SfVZZLtVbXEB9ryVxmVtVMsMwmEyEvgXN6Q84LKkLRmf4ST6QrLeBm3jQsb9gx1uo23TS7vo3vAkZGZz71uuLCcywUkt'),
    ('panda eyebrow bullet gorilla call smoke muffin taste mesh discover soft ostrich alcohol speed nation flash devote level hobby quick inner drive ghost inside', '72be8e052fc4919d2adf28d5306b5474b0069df35b02303de8c1729c9538dbb6fc2d731d5f832193cd9fb6aeecbc469594a70e3dd50811b5067f3b88b28c3e8d', 'xprv9s21ZrQH143K2WNnKmssvZYM96VAr47iHUQUTUyUXH3sAGNjhJANddnhw3i3y3pBbRAVk5M5qUGFr4rHbEWwXgX4qrvrceifCYQJbbFDems'),
    ('cat swing flag economy stadium alone churn speed unique patch report train', 'deb5f45449e615feff5640f2e49f933ff51895de3b4381832b3139941c57b59205a42480c52175b6efcffaa58a2503887c1e8b363a707256bdd2b587b46541f5', 'xprv9s21ZrQH143K4G28omGMogEoYgDQuigBo8AFHAGDaJdqQ99QKMQ5J6fYTMfANTJy6xBmhvsNZ1CJzRZ64PWbnTFUn6CDV2FxoMDLXdk95DQ'),
    ('light rule cinnamon wrap drastic word pride squirrel upgrade then income fatal apart sustain crack supply proud access', '4cbdff1ca2db800fd61cae72a57475fdc6bab03e441fd63f96dabd1f183ef5b782925f00105f318309a7e9c3ea6967c7801e46c8a58082674c860a37b93eda02', 'xprv9s21ZrQH143K3wtsvY8L2aZyxkiWULZH4vyQE5XkHTXkmx8gHo6RUEfH3Jyr6NwkJhvano7Xb2o6UqFKWHVo5scE31SGDCAUsgVhiUuUDyh'),
    ('all hour make first leader extend hole alien behind guard gospel lava path output census museum junior mass reopen famous sing advance salt reform', '26e975ec644423f4a4c4f4215ef09b4bd7ef924e85d1d17c4cf3f136c2863cf6df0a475045652c57eb5fb41513ca2a2d67722b77e954b4b3fc11f7590449191d', 'xprv9s21ZrQH143K3rEfqSM4QZRVmiMuSWY9wugscmaCjYja3SbUD3KPEB1a7QXJoajyR2T1SiXU7rFVRXMV9XdYVSZe7JoUXdP4SRHTxsT1nzm'),
    ('vessel ladder alter error federal sibling chat ability sun glass valve picture', '2aaa9242daafcee6aa9d7269f17d4efe271e1b9a529178d7dc139cd18747090bf9d60295d0ce74309a78852a9caadf0af48aae1c6253839624076224374bc63f', 'xprv9s21ZrQH143K2QWV9Wn8Vvs6jbqfF1YbTCdURQW9dLFKDovpKaKrqS3SEWsXCu6ZNky9PSAENg6c9AQYHcg4PjopRGGKmdD313ZHszymnps'),
    ('scissors invite lock maple supreme raw rapid void congress muscle digital elegant little brisk hair mango congress clump', '7b4a10be9d98e6cba265566db7f136718e1398c71cb581e1b2f464cac1ceedf4f3e274dc270003c670ad8d02c4558b2f8e39edea2775c9e232c7cb798b069e88', 'xprv9s21ZrQH143K4aERa2bq7559eMCCEs2QmmqVjUuzfy5eAeDX4mqZffkYwpzGQRE2YEEeLVRoH4CSHxianrFaVnMN2RYaPUZJhJx8S5j6puX'),
    ('void come effort suffer camp survey warrior heavy shoot primary clutch crush open amazing screen patrol group space point ten exist slush involve unfold', '01f5bced59dec48e362f2c45b5de68b9fd6c92c6634f44d6d40aab69056506f0e35524a518034ddc1192e1dacd32c1ed3eaa3c3b131c88ed8e7e54c49a5d0998', 'xprv9s21ZrQH143K39rnQJknpH1WEPFJrzmAqqasiDcVrNuk926oizzJDDQkdiTvNPr2FYDYzWgiMiC63YmfPAa2oPyNB23r2g7d1yiK6WpqaQS'),
)


def mnemonic_normalize(mnemonic):
    return unicodedata.normalize("NFKD", " ".join(mnemonic.split()))


def mnemonic_validate(mnemonic):
    words = mnemonic_normalize(mnemonic).split(" ")
    n = len(words)
    if n not in (12, 15, 18, 21, 24):
        raise ValueError("mnemonic must have 12/15/18/21/24 words, got %d" % n)
    index = {}
    for i, w in enumerate(WORDLIST):
        index[w] = i
    for w in words:
        if w not in index:
            raise ValueError("word %r is not in the BIP39 English wordlist" % w)
    bits = []
    for w in words:
        i = index[w]
        bits.extend((i >> shift) & 1 for shift in range(10, -1, -1))
    cs_bits = (n * 11) // 33
    ent_bits = n * 11 - cs_bits
    ent = bytearray((n * 11 - cs_bits + 7) // 8)
    for i in range(ent_bits):
        if bits[i]:
            ent[i // 8] |= 0x80 >> (i % 8)
    checksum = 0
    h = sha256(bytes(ent))
    for i in range(cs_bits):
        checksum = (checksum << 1) | ((h[i // 8] >> (7 - i % 8)) & 1)
    if checksum != int("".join(map(str, bits[ent_bits:])), 2):
        raise ValueError("mnemonic checksum INVALID — check for typos or "
                         "missing/extra words")
    return bytes(ent), words


def mnemonic_from_entropy(entropy):
    """Entropy bytes -> mnemonic string (English wordlist)."""
    ent_bits = len(entropy) * 8
    cs_bits = ent_bits // 32
    h = sha256(entropy)
    bits = []
    for byte in entropy:
        bits.extend((byte >> shift) & 1 for shift in range(7, -1, -1))
    for i in range(cs_bits):
        bits.append((h[i // 8] >> (7 - i % 8)) & 1)
    words = []
    for i in range(0, len(bits), 11):
        idx = 0
        for b in bits[i:i + 11]:
            idx = (idx << 1) | b
        words.append(WORDLIST[idx])
    return " ".join(words)


def mnemonic_to_seed(mnemonic, passphrase=""):
    mnemonic = mnemonic_normalize(mnemonic)
    passphrase = unicodedata.normalize("NFKD", passphrase)
    return hashlib.pbkdf2_hmac("sha512", mnemonic.encode("utf-8"),
                               ("mnemonic" + passphrase).encode("utf-8"),
                               2048)


# ---------------------------------------------------------------------------
# BIP32
# ---------------------------------------------------------------------------

class ExtKey:
    __slots__ = ("depth", "parent_fp", "child_num", "chain", "key", "pub_pt",
                 "pub_bytes")

    def __init__(self, depth, parent_fp, child_num, chain, key=None,
                 pub_pt=None):
        self.depth = depth
        self.parent_fp = parent_fp
        self.child_num = child_num
        self.chain = chain
        self.key = key
        if key is not None:
            self.pub_pt = scalar_mult(key, G)
            if self.pub_pt is None:
                raise ValueError("invalid private key (zero)")
            self.pub_bytes = compress_pub(self.pub_pt)
        else:
            self.pub_pt = pub_pt
            self.pub_bytes = compress_pub(pub_pt)

    def ckd_priv(self, index):
        if index < 0 or index >= 1 << 32:
            raise ValueError("child index out of range")
        if index >= 1 << 31:
            if self.key is None:
                raise ValueError("cannot derive hardened child from xpub")
            data = b"\x00" + self.key.to_bytes(32, "big") + index.to_bytes(4, "big")
        else:
            data = self.pub_bytes + index.to_bytes(4, "big")
        I = hmac.new(self.chain, data, hashlib.sha512).digest()
        IL = int.from_bytes(I[:32], "big")
        if IL >= N:
            raise ValueError("derived key out of range (retry with another "
                             "index per BIP32)")
        if self.key is None:
            raise ValueError("private derivation requires the private key")
        child_key = (IL + self.key) % N
        if child_key == 0:
            raise ValueError("derived key is zero (retry with another index)")
        fp = hash160(self.pub_bytes)[:4]
        return ExtKey(self.depth + 1, fp, index, I[32:], key=child_key)

    def xprv(self):
        if self.key is None:
            raise ValueError("not a private extended key")
        return self._ser(0x0488ADE4, b"\x00" + self.key.to_bytes(32, "big"))

    def xpub(self, version=0x0488B21E):
        return self._ser(version, self.pub_bytes)

    def _ser(self, version, key_data):
        data = (version.to_bytes(4, "big") + bytes([self.depth]) +
                self.parent_fp + self.child_num.to_bytes(4, "big") +
                self.chain + key_data)
        return b58encode(data + sha256d(data)[:4])


def extkey_from_seed(seed):
    if not (16 <= len(seed) <= 64):
        raise ValueError("BIP32 seed must be 16..64 bytes")
    I = hmac.new(b"Bitcoin seed", seed, hashlib.sha512).digest()
    k = int.from_bytes(I[:32], "big")
    if not (1 <= k < N):
        raise ValueError("invalid master key from seed")
    return ExtKey(0, b"\x00\x00\x00\x00", 0, I[32:], key=k)


PATH_RE = re.compile(r"^[mM](/[0-9]+[hH']?)*(/\*)?$")


def parse_path(path):
    """'m/84h/0h/0h/0/*' -> list of steps; trailing '*' means index range."""
    path = path.strip()
    if not PATH_RE.match(path):
        raise ValueError("invalid derivation path %r (example: "
                         "m/84'/0'/0'/0/*)" % path)
    steps = []
    for part in path.split("/")[1:]:
        hardened = part[-1] in "hH'"
        num = part[:-1] if hardened else part
        if num == "*":
            steps.append("*")
            continue
        i = int(num)
        if i >= 1 << 31:
            raise ValueError("index too large: %d" % i)
        steps.append(i + (1 << 31) if hardened else i)
    if steps and steps[-1] != "*" and any(s == "*" for s in steps):
        raise ValueError("'*' is only allowed as the final path element")
    return steps


def derive_addresses(master, path, count):
    """Yield (path_str, address_dict) for an exact path or an index range."""
    steps = parse_path(path)
    if not steps:
        raise ValueError("derivation path must have at least one element "
                         "(or use m/0/* to enumerate account keys)")
    if steps[-1] == "*":
        base = steps[:-1]
        cur = master
        prefix = "m"
        for step in base:
            cur = cur.ckd_priv(step)
            prefix += "/%d%s" % (step & 0x7FFFFFFF,
                                 "'" if step >= (1 << 31) else "")
        for i in range(count):
            ek = cur.ckd_priv(i)
            yield ("%s/%d" % (prefix, i), all_addresses(ek.pub_pt))
    else:
        cur = master
        prefix = "m"
        for step in steps:
            cur = cur.ckd_priv(step)
            prefix += "/%d%s" % (step & 0x7FFFFFFF,
                                 "'" if step >= (1 << 31) else "")
        yield (prefix, all_addresses(cur.pub_pt))


# ---------------------------------------------------------------------------
# Challenge format
# ---------------------------------------------------------------------------

CHALLENGE_TEMPLATE = """{domain}
nonce: {nonce}
address: {address}
created: {created}{note}"""

NONCE_RE = re.compile(r"^[0-9a-f]{64}$")


def new_nonce():
    return os.urandom(32)


def make_challenge(address, note=None, nonce=None, created=None):
    if nonce is None:
        nonce = new_nonce()
    if created is None:
        import datetime
        created = datetime.datetime.now(datetime.timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
    lines = CHALLENGE_TEMPLATE.format(
        domain=DOMAIN,
        nonce=nonce.hex(),
        address=address,
        created=created,
        note="" if not note else "\nnote: " + note.replace("\n", " "))
    return lines


def parse_challenge(text):
    lines = text.rstrip("\n").split("\n")
    if not lines or lines[0] != DOMAIN:
        raise ValueError("challenge must start with the domain separator "
                         "line %r" % DOMAIN)
    fields = {"domain": DOMAIN}
    for line in lines[1:]:
        if ":" not in line:
            raise ValueError("malformed challenge line %r" % line)
        key, _, value = line.partition(":")
        value = value.strip()
        if key.strip() in fields and key.strip() != "note":
            raise ValueError("duplicate challenge field %r" % key)
        fields[key.strip()] = value
    if "nonce" not in fields or not NONCE_RE.match(fields["nonce"]):
        raise ValueError("challenge nonce must be 64 hex characters")
    if "address" not in fields or not fields["address"]:
        raise ValueError("challenge is missing the address field")
    if "created" not in fields:
        raise ValueError("challenge is missing the created field")
    return fields


def verify_challenge(challenge_text, signature, address=None):
    fields = parse_challenge(challenge_text)
    claimed = address or fields["address"]
    if address and address != fields["address"]:
        print("warning: --address %s differs from challenge address %s"
              % (address, fields["address"]), file=sys.stderr)
    if "<address>" in fields["address"] or "ADDRESS" in fields["address"]:
        print("warning: challenge still contains the address placeholder — "
              "the signed message must contain the real address",
              file=sys.stderr)
    candidates = [challenge_text, challenge_text.rstrip("\n"),
                  challenge_text.rstrip()]
    seen = []
    last_err = None
    for msg in candidates:
        if msg in seen:
            continue
        seen.append(msg)
        try:
            if verify_message(signature, msg, claimed):
                return True, fields
        except ValueError as e:
            last_err = e
    if last_err:
        raise last_err
    return False, fields


# ---------------------------------------------------------------------------
# Selftest
# ---------------------------------------------------------------------------

# Official BIP32 test vectors 1-4 (seed -> [(kind, key), ...]);
# parsed verbatim from bip-0032.mediawiki in bitcoin/bips.
BIP32_VECTORS = (
    # test vector 1
    ('000102030405060708090a0b0c0d0e0f', [
        ('pub', 'xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8'),
        ('prv', 'xprv9s21ZrQH143K3QTDL4LXw2F7HEK3wJUD2nW2nRk4stbPy6cq3jPPqjiChkVvvNKmPGJxWUtg6LnF5kejMRNNU3TGtRBeJgk33yuGBxrMPHi'),
        ('pub', 'xpub68Gmy5EdvgibQVfPdqkBBCHxA5htiqg55crXYuXoQRKfDBFA1WEjWgP6LHhwBZeNK1VTsfTFUHCdrfp1bgwQ9xv5ski8PX9rL2dZXvgGDnw'),
        ('prv', 'xprv9uHRZZhk6KAJC1avXpDAp4MDc3sQKNxDiPvvkX8Br5ngLNv1TxvUxt4cV1rGL5hj6KCesnDYUhd7oWgT11eZG7XnxHrnYeSvkzY7d2bhkJ7'),
        ('pub', 'xpub6ASuArnXKPbfEwhqN6e3mwBcDTgzisQN1wXN9BJcM47sSikHjJf3UFHKkNAWbWMiGj7Wf5uMash7SyYq527Hqck2AxYysAA7xmALppuCkwQ'),
        ('prv', 'xprv9wTYmMFdV23N2TdNG573QoEsfRrWKQgWeibmLntzniatZvR9BmLnvSxqu53Kw1UmYPxLgboyZQaXwTCg8MSY3H2EU4pWcQDnRnrVA1xe8fs'),
        ('pub', 'xpub6D4BDPcP2GT577Vvch3R8wDkScZWzQzMMUm3PWbmWvVJrZwQY4VUNgqFJPMM3No2dFDFGTsxxpG5uJh7n7epu4trkrX7x7DogT5Uv6fcLW5'),
        ('prv', 'xprv9z4pot5VBttmtdRTWfWQmoH1taj2axGVzFqSb8C9xaxKymcFzXBDptWmT7FwuEzG3ryjH4ktypQSAewRiNMjANTtpgP4mLTj34bhnZX7UiM'),
        ('pub', 'xpub6FHa3pjLCk84BayeJxFW2SP4XRrFd1JYnxeLeU8EqN3vDfZmbqBqaGJAyiLjTAwm6ZLRQUMv1ZACTj37sR62cfN7fe5JnJ7dh8zL4fiyLHV'),
        ('prv', 'xprvA2JDeKCSNNZky6uBCviVfJSKyQ1mDYahRjijr5idH2WwLsEd4Hsb2Tyh8RfQMuPh7f7RtyzTtdrbdqqsunu5Mm3wDvUAKRHSC34sJ7in334'),
        ('pub', 'xpub6H1LXWLaKsWFhvm6RVpEL9P4KfRZSW7abD2ttkWP3SSQvnyA8FSVqNTEcYFgJS2UaFcxupHiYkro49S8yGasTvXEYBVPamhGW6cFJodrTHy'),
        ('prv', 'xprvA41z7zogVVwxVSgdKUHDy1SKmdb533PjDz7J6N6mV6uS3ze1ai8FHa8kmHScGpWmj4WggLyQjgPie1rFSruoUihUZREPSL39UNdE3BBDu76'),
    ]),
    # test vector 2
    ('fffcf9f6f3f0edeae7e4e1dedbd8d5d2cfccc9c6c3c0bdbab7b4b1aeaba8a5a29f9c999693908d8a8784817e7b7875726f6c696663605d5a5754514e4b484542', [
        ('pub', 'xpub661MyMwAqRbcFW31YEwpkMuc5THy2PSt5bDMsktWQcFF8syAmRUapSCGu8ED9W6oDMSgv6Zz8idoc4a6mr8BDzTJY47LJhkJ8UB7WEGuduB'),
        ('prv', 'xprv9s21ZrQH143K31xYSDQpPDxsXRTUcvj2iNHm5NUtrGiGG5e2DtALGdso3pGz6ssrdK4PFmM8NSpSBHNqPqm55Qn3LqFtT2emdEXVYsCzC2U'),
        ('pub', 'xpub69H7F5d8KSRgmmdJg2KhpAK8SR3DjMwAdkxj3ZuxV27CprR9LgpeyGmXUbC6wb7ERfvrnKZjXoUmmDznezpbZb7ap6r1D3tgFxHmwMkQTPH'),
        ('prv', 'xprv9vHkqa6EV4sPZHYqZznhT2NPtPCjKuDKGY38FBWLvgaDx45zo9WQRUT3dKYnjwih2yJD9mkrocEZXo1ex8G81dwSM1fwqWpWkeS3v86pgKt'),
        ('pub', 'xpub6ASAVgeehLbnwdqV6UKMHVzgqAG8Gr6riv3Fxxpj8ksbH9ebxaEyBLZ85ySDhKiLDBrQSARLq1uNRts8RuJiHjaDMBU4Zn9h8LZNnBC5y4a'),
        ('prv', 'xprv9wSp6B7kry3Vj9m1zSnLvN3xH8RdsPP1Mh7fAaR7aRLcQMKTR2vidYEeEg2mUCTAwCd6vnxVrcjfy2kRgVsFawNzmjuHc2YmYRmagcEPdU9'),
        ('pub', 'xpub6DF8uhdarytz3FWdA8TvFSvvAh8dP3283MY7p2V4SeE2wyWmG5mg5EwVvmdMVCQcoNJxGoWaU9DCWh89LojfZ537wTfunKau47EL2dhHKon'),
        ('prv', 'xprv9zFnWC6h2cLgpmSA46vutJzBcfJ8yaJGg8cX1e5StJh45BBciYTRXSd25UEPVuesF9yog62tGAQtHjXajPPdbRCHuWS6T8XA2ECKADdw4Ef'),
        ('pub', 'xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL'),
        ('prv', 'xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc'),
        ('pub', 'xpub6FnCn6nSzZAw5Tw7cgR9bi15UV96gLZhjDstkXXxvCLsUXBGXPdSnLFbdpq8p9HmGsApME5hQTZ3emM2rnY5agb9rXpVGyy3bdW6EEgAtqt'),
        ('prv', 'xprvA2nrNbFZABcdryreWet9Ea4LvTJcGsqrMzxHx98MMrotbir7yrKCEXw7nadnHM8Dq38EGfSh6dqA9QWTyefMLEcBYJUuekgW4BYPJcr9E7j'),
    ]),
    # test vector 3
    ('4b381541583be4423346c643850da4b320e46a87ae3d2a4e6da11eba819cd4acba45d239319ac14f863b8d5ab5a0d0c64d2e8a1e7d1457df2e5a3c51c73235be', [
        ('pub', 'xpub661MyMwAqRbcEZVB4dScxMAdx6d4nFc9nvyvH3v4gJL378CSRZiYmhRoP7mBy6gSPSCYk6SzXPTf3ND1cZAceL7SfJ1Z3GC8vBgp2epUt13'),
        ('prv', 'xprv9s21ZrQH143K25QhxbucbDDuQ4naNntJRi4KUfWT7xo4EKsHt2QJDu7KXp1A3u7Bi1j8ph3EGsZ9Xvz9dGuVrtHHs7pXeTzjuxBrCmmhgC6'),
        ('pub', 'xpub68NZiKmJWnxxS6aaHmn81bvJeTESw724CRDs6HbuccFQN9Ku14VQrADWgqbhhTHBaohPX4CjNLf9fq9MYo6oDaPPLPxSb7gwQN3ih19Zm4Y'),
        ('prv', 'xprv9uPDJpEQgRQfDcW7BkF7eTya6RPxXeJCqCJGHuCJ4GiRVLzkTXBAJMu2qaMWPrS7AANYqdq6vcBcBUdJCVVFceUvJFjaPdGZ2y9WACViL4L'),
    ]),
    # test vector 4
    ('3ddd5602285899a946114506157c7997e5444528f3003f6134712147db19b678', [
        ('pub', 'xpub661MyMwAqRbcGczjuMoRm6dXaLDEhW1u34gKenbeYqAix21mdUKJyuyu5F1rzYGVxyL6tmgBUAEPrEz92mBXjByMRiJdba9wpnN37RLLAXa'),
        ('prv', 'xprv9s21ZrQH143K48vGoLGRPxgo2JNkJ3J3fqkirQC2zVdk5Dgd5w14S7fRDyHH4dWNHUgkvsvNDCkvAwcSHNAQwhwgNMgZhLtQC63zxwhQmRv'),
        ('pub', 'xpub69AUMk3qDBi3uW1sXgjCmVjJ2G6WQoYSnNHyzkmdCHEhSZ4tBok37xfFEqHd2AddP56Tqp4o56AePAgCjYdvpW2PU2jbUPFKsav5ut6Ch1m'),
        ('prv', 'xprv9vB7xEWwNp9kh1wQRfCCQMnZUEG21LpbR9NPCNN1dwhiZkjjeGRnaALmPXCX7SgjFTiCTT6bXes17boXtjq3xLpcDjzEuGLQBM5ohqkao9G'),
        ('pub', 'xpub6BJA1jSqiukeaesWfxe6sNK9CCGaujFFSJLomWHprUL9DePQ4JDkM5d88n49sMGJxrhpjazuXYWdMf17C9T5XnxkopaeS7jGk1GyyVziaMt'),
        ('prv', 'xprv9xJocDuwtYCMNAo3Zw76WENQeAS6WGXQ55RCy7tDJ8oALr4FWkuVoHJeHVAcAqiZLE7Je3vZJHxspZdFHfnBEjHqU5hG1Jaj32dVoS6XLT1'),
    ]),
)

# Official BIP32 'invalid extended keys' vectors (bip-0032.mediawiki, test vector 5)
BIP32_INVALID_KEYS = (
    'xpub661MyMwAqRbcEYS8w7XLSVeEsBXy79zSzH1J8vCdxAZningWLdN3zgtU6LBpB85b3D2yc8sfvZU521AAwdZafEz7mnzBBsz4wKY5fTtTQBm',
    'xprv9s21ZrQH143K24Mfq5zL5MhWK9hUhhGbd45hLXo2Pq2oqzMMo63oStZzFGTQQD3dC4H2D5GBj7vWvSQaaBv5cxi9gafk7NF3pnBju6dwKvH',
    'xpub661MyMwAqRbcEYS8w7XLSVeEsBXy79zSzH1J8vCdxAZningWLdN3zgtU6Txnt3siSujt9RCVYsx4qHZGc62TG4McvMGcAUjeuwZdduYEvFn',
    'xprv9s21ZrQH143K24Mfq5zL5MhWK9hUhhGbd45hLXo2Pq2oqzMMo63oStZzFGpWnsj83BHtEy5Zt8CcDr1UiRXuWCmTQLxEK9vbz5gPstX92JQ',
    'xpub661MyMwAqRbcEYS8w7XLSVeEsBXy79zSzH1J8vCdxAZningWLdN3zgtU6N8ZMMXctdiCjxTNq964yKkwrkBJJwpzZS4HS2fxvyYUA4q2Xe4',
    'xprv9s21ZrQH143K24Mfq5zL5MhWK9hUhhGbd45hLXo2Pq2oqzMMo63oStZzFAzHGBP2UuGCqWLTAPLcMtD9y5gkZ6Eq3Rjuahrv17fEQ3Qen6J',
    'xprv9s2SPatNQ9Vc6GTbVMFPFo7jsaZySyzk7L8n2uqKXJen3KUmvQNTuLh3fhZMBoG3G4ZW1N2kZuHEPY53qmbZzCHshoQnNf4GvELZfqTUrcv',
    'xpub661no6RGEX3uJkY4bNnPcw4URcQTrSibUZ4NqJEw5eBkv7ovTwgiT91XX27VbEXGENhYRCf7hyEbWrR3FewATdCEebj6znwMfQkhRYHRLpJ',
    'xprv9s21ZrQH4r4TsiLvyLXqM9P7k1K3EYhA1kkD6xuquB5i39AU8KF42acDyL3qsDbU9NmZn6MsGSUYZEsuoePmjzsB3eFKSUEh3Gu1N3cqVUN',
    'xpub661MyMwAuDcm6CRQ5N4qiHKrJ39Xe1R1NyfouMKTTWcguwVcfrZJaNvhpebzGerh7gucBvzEQWRugZDuDXjNDRmXzSZe4c7mnTK97pTvGS8',
    'xprv9s21ZrQH143K24Mfq5zL5MhWK9hUhhGbd45hLXo2Pq2oqzMMo63oStZzF93Y5wvzdUayhgkkFoicQZcP3y52uPPxFnfoLZB21Teqt1VvEHx',
    'xprv9s21ZrQH143K24Mfq5zL5MhWK9hUhhGbd45hLXo2Pq2oqzMMo63oStZzFAzHGBP2UuGCqWLTAPLcMtD5SDKr24z3aiUvKr9bJpdrcLg1y3G',
    'xpub661MyMwAqRbcEYS8w7XLSVeEsBXy79zSzH1J8vCdxAZningWLdN3zgtU6Q5JXayek4PRsn35jii4veMimro1xefsM58PgBMrvdYre8QyULY',
    'xprv9s21ZrQH143K3QTDL4LXw2F7HEK3wJUD2nW2nRk4stbPy6cq3jPPqjiChkVvvNKmPGJxWUtg6LnF5kejMRNNU3TGtRBeJgk33yuGBxrMPHL',
)

BIP173_VECTORS = (
    # (address, hrp, witver, program-hex) from bip-0173.mediawiki
    ("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4", "bc", 0,
     "751e76e8199196d454941c45d1b3a323f1433bd6"),
    ("tb1qw508d6qejxtdg4y5r3zarvary0c5xw7kxpjzsx", "tb", 0,
     "751e76e8199196d454941c45d1b3a323f1433bd6"),
    ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7", "tb", 0,
     "1863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262"),
    # v1 program under BIP350 (bech32m checksum; the BIP173-era bech32
    # spelling of this same program is no longer valid)
    ("bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y", "bc", 1,
     "751e76e8199196d454941c45d1b3a323f1433bd6751e76e8199196d454941c45d1b3a323f1433bd6"),
)

BIP173_INVALID = (
    "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5",    # invalid checksum
    "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3sL5k7",  # mixed case
    "bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du",          # zero padding
    "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv",  # non-zero padding
)

# Bitcoin Core known-answer vector, from
# bitcoin/bitcoin test/functional/rpc_signmessagewithprivkey.py (fetched 2026-10-25)
CORE_WIF = "cUeKHd5orzT3mz8P9pxyREHfsWtVfgsfDjiZZBcjUBAaGk1BTj7N"
CORE_MESSAGE = "This is just a test message"
CORE_SIG = ("INbVnW4e6PeRmsv2Qgu8NuopvrVjkcxob+sX8OcZG0SALhWybUjzMLPdAsXI46"
            "YZGb0KQTRii+wWIQzRpG/U+S0=")
CORE_ADDR_P2PKH = "mpLQjfK79b7CCV4VMJWEWAj5Mpx8Up5zxB"

# Public constants for private key = 1 (universally known; the compressed
# address is also confirmed funded/spent on-chain since 2011)
KEY1_COMPRESSED_ADDR = "1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH"
KEY1_UNCOMPRESSED_ADDR = "1EHNa6Q4Jz2uvNExL497mE43ikXhwF6kZm"


def selftest():
    failures = []
    counter = [0]

    def check(name, cond, detail=""):
        counter[0] += 1
        status = "PASS" if cond else "FAIL"
        print("  [%s] %s%s" % (status, name,
                               (" — " + detail) if detail and not cond else ""))
        if not cond:
            failures.append(name)

    print("prover selftest")

    # --- hashes
    check("sha256('abc')", sha256(b"abc").hex() ==
          "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    check("ripemd160_pure('abc')", ripemd160_pure(b"abc").hex() ==
          "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc")
    try:
        h = hashlib.new("ripemd160", b"abc").digest()
        check("ripemd160_pure == hashlib.ripemd160",
              h == ripemd160_pure(b"abc") and
              ripemd160_pure(b"x" * 1000) == hashlib.new("ripemd160", b"x" * 1000).digest())
    except Exception:
        print("  [SKIP] hashlib ripemd160 not available on this build")

    # --- base58 / addresses for private key 1
    pt1 = scalar_mult(1, G)
    check("key=1 compressed p2pkh", p2pkh_address(compress_pub(pt1)) ==
          KEY1_COMPRESSED_ADDR)
    check("key=1 uncompressed p2pkh", p2pkh_address(uncompressed_pub(pt1)) ==
          KEY1_UNCOMPRESSED_ADDR)
    check("base58check roundtrip",
          b58check_decode(KEY1_COMPRESSED_ADDR)[0] == 0x00 and
          b58check_encode(b"\x00", b58check_decode(KEY1_COMPRESSED_ADDR)[1:])
          == KEY1_COMPRESSED_ADDR)
    try:
        b58check_decode(KEY1_COMPRESSED_ADDR[:-1] + ("2" if KEY1_COMPRESSED_ADDR[-1] != "2" else "3"))
        check("base58check bad checksum rejected", False)
    except ValueError:
        check("base58check bad checksum rejected", True)

    # --- bech32 (BIP173)
    for addr, hrp, witver, prog in BIP173_VECTORS:
        got = segwit_encode(hrp, witver, bytes.fromhex(prog))
        check("bech32 encode %s..." % addr[:12], got == addr, "got %s" % got)
        dhrp, dver, dprog = segwit_decode(addr)
        check("bech32 decode %s..." % addr[:12],
              dhrp == hrp and dver == witver and dprog == bytes.fromhex(prog))
    for addr in BIP173_INVALID:
        try:
            segwit_decode(addr)
            check("bech32 reject %s..." % addr[:12], False)
        except ValueError:
            check("bech32 reject %s..." % addr[:12], True)

    # --- BIP39 official vectors
    check("BIP39 wordlist size", len(WORDLIST) == 2048)
    for mn, seed_hex, _xprv in BIP39_VECTORS:
        ent, words = mnemonic_validate(mn)
        ok = mnemonic_to_seed(mn, "TREZOR").hex() == seed_hex
        check("BIP39 seed %s..." % mn.split()[0], ok)
        check("BIP39 entropy->mnemonic %s..." % mn.split()[0],
              mnemonic_from_entropy(ent) == mn)
    try:
        bad = BIP39_VECTORS[0][0].split()
        bad[0] = "zoo" if bad[0] != "zoo" else "abandon"
        mnemonic_validate(" ".join(bad))
        check("BIP39 bad checksum rejected", False)
    except ValueError:
        check("BIP39 bad checksum rejected", True)

    # --- BIP39 -> BIP32 master keys (vectors.json carries the master xprv)
    for mn, seed_hex, xprv in BIP39_VECTORS:
        seed = mnemonic_to_seed(mn, "TREZOR")
        check("BIP39->BIP32 master %s..." % mn.split()[0],
              extkey_from_seed(seed).xprv() == xprv)

    # --- BIP32 official vectors
    # Each vector lists, per chain node, (xpub, xprv) in order from the root.
    # Walk the chain: derive to the next node using the child number parsed
    # from the NEXT node's xprv, and compare both serialisations.
    for seed_hex, items in BIP32_VECTORS:
        master = extkey_from_seed(bytes.fromhex(seed_hex))
        chains = [(items[i][1], items[i + 1][1]) for i in range(0, len(items), 2)]
        cur = master
        ok = True
        for j, (xpub_exp, xprv_exp) in enumerate(chains):
            if cur.xpub() != xpub_exp or cur.xprv() != xprv_exp:
                ok = False
                break
            if j + 1 < len(chains):
                nxt = b58check_decode(chains[j + 1][1])
                child_num = int.from_bytes(nxt[9:13], "big")
                cur = cur.ckd_priv(child_num)
        check("BIP32 vector %s (seed %s..., %d chains)" %
              (BIP32_VECTORS.index((seed_hex, items)) + 1, seed_hex[:8],
               len(chains)), ok,
              "mismatch at depth %d" % cur.depth if not ok else "")

    # --- BIP32 negative vectors
    try:
        extkey_from_seed(b"\x00" * 15)
        check("BIP32 short seed rejected", False)
    except ValueError:
        check("BIP32 short seed rejected", True)
    try:
        extkey_from_seed(b"\x00" * 65)
        check("BIP32 long seed rejected", False)
    except ValueError:
        check("BIP32 long seed rejected", True)
    for bad in BIP32_INVALID_KEYS:
        try:
            parse_xkey(bad)
            check("BIP32 invalid key rejected %s..." % bad[:12], False)
        except ValueError:
            check("BIP32 invalid key rejected %s..." % bad[:12], True)

    # --- BIP84 documented example (empty passphrase)
    # from bip-0084.mediawiki: account zpub and first native-segwit address
    bip84_mn = ("abandon abandon abandon abandon abandon abandon "
                "abandon abandon abandon abandon abandon about")
    bip84_root = extkey_from_seed(mnemonic_to_seed(bip84_mn, ""))
    acct = bip84_root
    for idx in (84 + (1 << 31), 1 << 31, 1 << 31):
        acct = acct.ckd_priv(idx)
    check("BIP84 account zpub",
          acct.xpub(0x04B24746) ==
          "zpub6rFR7y4Q2AijBEqTUquhVz398htDFrtymD9xYYfG1m4wAcvPhXNfE3Ef"
          "H1r1ADqtfSdVCToUG868RvUUkgDKf31mGDtKsAYz2oz2AGutZYs")
    first = list(derive_addresses(acct, "m/0/0", 1))[0][1]
    check("BIP84 first address",
          first["p2wpkh"] == "bc1qcr8te4kr609gcawutmrza0j4xv80jy8z306fyu")

    # --- Bitcoin Core signed-message known answer
    key, compressed, version = wif_decode(CORE_WIF)
    check("Core WIF decode", compressed and version == 0xEF)
    sig = sign_message(key, CORE_MESSAGE, compressed=True)
    import base64
    got_sig = base64.b64encode(sig).decode()
    check("Core deterministic signature", got_sig == CORE_SIG,
          "got %s" % got_sig)
    check("Core verify against address", verify_message(CORE_SIG, CORE_MESSAGE,
                                                        CORE_ADDR_P2PKH))
    pt = scalar_mult(key, G)
    rec_pt, comp = recover_from_message_signature(CORE_SIG, CORE_MESSAGE)
    check("Core recovery == pubkey", comp and rec_pt == pt)
    check("Core address derivation", p2pkh_address(compress_pub(pt), True) ==
          CORE_ADDR_P2PKH)

    # --- negative signature tests
    bad_msg = CORE_MESSAGE + "x"
    check("reject wrong message", not verify_message(CORE_SIG, bad_msg,
                                                     CORE_ADDR_P2PKH))
    check("reject wrong address", not verify_message(CORE_SIG, CORE_MESSAGE,
                                                     KEY1_COMPRESSED_ADDR))
    raw = bytearray(base64.b64decode(CORE_SIG))
    raw[10] ^= 0x01
    check("reject corrupted signature",
          not verify_message(base64.b64encode(bytes(raw)).decode(),
                             CORE_MESSAGE, CORE_ADDR_P2PKH))

    # uncompressed sign/verify round trip (no external vector; math is
    # anchored by the BIP32 xpub vectors and the Core vector above)
    sig2 = sign_message(key, CORE_MESSAGE, compressed=False)
    ok = verify_message(base64.b64encode(sig2).decode(), CORE_MESSAGE,
                        p2pkh_address(uncompressed_pub(pt), True))
    check("uncompressed sign/verify roundtrip", ok)

    # --- challenge roundtrip
    ch = make_challenge(KEY1_COMPRESSED_ADDR, note="selftest")
    fields = parse_challenge(ch)
    check("challenge roundtrip",
          fields["address"] == KEY1_COMPRESSED_ADDR and
          NONCE_RE.match(fields["nonce"]) is not None and
          fields["note"] == "selftest")
    try:
        parse_challenge(ch.replace("nonce: ", "nonce: 0", 1))
        check("challenge bad nonce rejected", False)
    except ValueError:
        check("challenge bad nonce rejected", True)

    print()
    if failures:
        print("SELFTEST FAILED: %d/%d checks failed: %s"
              % (len(failures), counter[0], ", ".join(failures)))
        return 1
    print("ALL SELFTESTS PASSED (%d checks)" % counter[0])
    print("It is safe to use this tool for real proofs.")
    return 0


# ---------------------------------------------------------------------------
# BIP32 xkey parsing (used by selftest negative vectors)
# ---------------------------------------------------------------------------

XPRV_VERSION = 0x0488ADE4
XPUB_VERSION = 0x0488B21E


def parse_xkey(s):
    payload = b58check_decode(s)
    if len(payload) != 78:
        raise ValueError("extended key must encode 78 bytes")
    version = int.from_bytes(payload[0:4], "big")
    depth = payload[4]
    parent_fp = payload[5:9]
    child_num = int.from_bytes(payload[9:13], "big")
    chain = payload[13:45]
    key_data = payload[45:78]
    if depth == 0 and (parent_fp != b"\x00\x00\x00\x00" or child_num != 0):
        raise ValueError("depth-0 extended key must have zero parent "
                         "fingerprint and child number")
    if version == XPRV_VERSION:
        if key_data[0] != 0:
            raise ValueError("xprv key data must start with 0x00")
        key = int.from_bytes(key_data[1:], "big")
        if not (1 <= key < N):
            raise ValueError("xprv key out of range")
        return ExtKey(depth, parent_fp, child_num, chain, key=key)
    if version == XPUB_VERSION:
        if key_data[0] not in (2, 3):
            raise ValueError("xpub key data must be a compressed pubkey")
        return ExtKey(depth, parent_fp, child_num, chain,
                      pub_pt=decompress_pub(key_data))
    raise ValueError("unknown extended-key version 0x%08x" % version)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def cmd_challenge(args):
    address = args.address or "<address>"
    text = make_challenge(address, note=args.note, nonce=args.nonce_bytes)
    print(text)
    print("# --- everything below this line is guidance, NOT part of the "
          "challenge ---", file=sys.stderr)
    if not args.address:
        print("# NOTE: replace <address> with the real address BEFORE "
              "signing — the", file=sys.stderr)
        print("# signature covers the address line.", file=sys.stderr)
    print("# Next step: sign this exact text with the wallet that controls "
          "the address", file=sys.stderr)
    print("# (Electrum: Wallet message signing; Bitcoin Core: signmessage). "
          "Then run:", file=sys.stderr)
    print("#   prover.py verify --address %s --signature <sig>" % address,
          file=sys.stderr)
    return 0


def cmd_verify(args):
    if args.challenge_file:
        with open(args.challenge_file, "r") as f:
            challenge_text = f.read()
    elif args.challenge:
        challenge_text = args.challenge.replace("\\n", "\n")
    elif args.message:
        challenge_text = None
    else:
        print("error: need --challenge, --challenge-file or --message",
              file=sys.stderr)
        return 2

    if challenge_text is None:
        msg = args.message
        try:
            ok = verify_message(args.signature, msg, args.address)
            fields = None
        except ValueError as e:
            print("NOT VERIFIED: %s" % e)
            return 1
    else:
        try:
            ok, fields = verify_challenge(challenge_text, args.signature,
                                          args.address)
        except ValueError as e:
            print("NOT VERIFIED: %s" % e)
            return 1
        msg = None

    if ok:
        print("VERIFIED: signature for address %s is valid" % args.address)
        if fields:
            print("challenge nonce: %s" % fields["nonce"])
        return 0
    print("NOT VERIFIED: signature does not match address %s for this "
          "message" % args.address)
    return 1


def _read_secret(prompt, flag_value, flag_name):
    if flag_value is not None:
        print("warning: %s passed on the command line is visible in shell "
              "history; prefer the interactive prompt" % flag_name,
              file=sys.stderr)
        return flag_value
    if not sys.stdin.isatty():
        # scripted/piped input: getpass would fail, read a line from stdin
        line = sys.stdin.readline()
        return line.rstrip("\r\n")
    return getpass.getpass(prompt)


def cmd_derive_check(args):
    mnemonic = _read_secret("Enter mnemonic (input hidden): ", args.mnemonic,
                            "--mnemonic")
    passphrase = _read_secret("Enter passphrase (leave empty if none): ",
                              args.passphrase, "--passphrase")
    try:
        mnemonic_validate(mnemonic)
    except ValueError as e:
        print("NO MATCH (mnemonic rejected: %s)" % e)
        return 1
    seed = mnemonic_to_seed(mnemonic, passphrase)
    master = extkey_from_seed(seed)
    try:
        found = None
        candidates = {a.strip() for a in args.address}
        checked = 0
        for path, addrs in derive_addresses(master, args.path, args.count):
            checked += 1
            for label, addr in addrs.items():
                if addr in candidates:
                    found = (path, label, addr)
            if args.show_derived:
                for label, addr in addrs.items():
                    print("  %s (%s)" % (addr, label), file=sys.stderr)
            if found:
                break
    except ValueError as e:
        print("NO MATCH (error: %s)" % e)
        return 1
    if found:
        print("MATCH at %s (%s)" % (found[0], found[1]))
        return 0
    print("NO MATCH (%d derivation%s checked; try other paths or more "
          "indices)" % (checked, "s" if checked != 1 else ""))
    return 1


def main(argv):
    ap = argparse.ArgumentParser(
        prog="prover.py",
        description="Decruptor proof-of-ownership tool (offline)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("challenge", help="generate an ownership challenge")
    p.add_argument("--address", help="the Bitcoin address to prove "
                                     "ownership of (omit for placeholder)")
    p.add_argument("--note", help="optional single-line note")
    p.add_argument("--nonce-bytes", type=lambda x: bytes.fromhex(x),
                   help="explicit 32-byte nonce (hex; testing only)")
    p.set_defaults(func=cmd_challenge)

    p = sub.add_parser("verify", help="verify a signed challenge")
    p.add_argument("--address", required=True,
                   help="the Bitcoin address the signature must match")
    p.add_argument("--signature", required=True,
                   help="the signature (base64 or base58)")
    p.add_argument("--challenge", help="the challenge text (use \\n for "
                                       "newlines)")
    p.add_argument("--challenge-file", help="file containing the challenge")
    p.add_argument("--message", help="plain message instead of a challenge")
    p.set_defaults(func=cmd_verify)

    p = sub.add_parser("derive-check",
                       help="check whether a seed derives a claimed address")
    p.add_argument("--path", default="m/84'/0'/0'/0/*",
                   help="derivation path; '*' at the end enumerates indices "
                        "(default: m/84'/0'/0'/0/*)")
    p.add_argument("--address", action="append", required=True,
                   help="claimed address (repeatable)")
    p.add_argument("--count", type=int, default=20,
                   help="number of indices to check for '*' paths")
    p.add_argument("--mnemonic", help="mnemonic (avoid: use the prompt)")
    p.add_argument("--passphrase", help="BIP39 passphrase (avoid: prompt)")
    p.add_argument("--show-derived", action="store_true",
                   help="print derived addresses to stderr (local only)")
    p.set_defaults(func=cmd_derive_check)

    sub.add_parser("selftest", help="run all internal test vectors").set_defaults(
        func=lambda a: sys.exit(selftest()))

    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
