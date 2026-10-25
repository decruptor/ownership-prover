# ownership-prover — offline proof of wallet ownership

A small, offline-first tool for the owner of a Bitcoin wallet to prove they
control an address **without sharing anything spendable**. Two independent
proof routes:

1. **Message signature** — the owner signs a challenge with the wallet that
   controls the address; anyone can verify the signature recovers to that
   address. No private key ever leaves the wallet.
2. **Derivation check** — for seed-phrase owners: the tool derives addresses
   from the mnemonic **locally** and prints only match / no-match against the
   claimed address. Nothing is written, sent, or stored.

It exists because a legitimate recovery process must never require a client to
hand over spendable material. Decruptor never asks for seed words over any
channel — this tool is how ownership is demonstrated instead.

Python 3 standard library only. No third-party dependencies. No network use.

## Run the selftest first

```
python3 prover.py selftest
```

This must print `ALL SELFTESTS PASSED` before any real use, on the machine you
will use. It runs every internal test vector and exits non-zero on any failure:

- all 24 official BIP39 English test vectors (mnemonic→seed and master xprv,
  from trezor/python-mnemonic `vectors.json`, linked in the BIP39 spec);
- the official BIP32 test vectors 1–4 (every xprv and xpub string, from the
  BIP32 spec) and all 14 "invalid extended keys" vectors (rejection);
- the BIP84 documented example (account zpub and first address, from the
  BIP84 spec);
- a signed-message known answer from Bitcoin Core's own test suite
  (`test/functional/rpc_signmessagewithprivkey.py`): the deterministic
  signature must match byte-for-byte;
- BIP173/350 bech32 and bech32m vectors, including invalid ones;
- RIPEMD-160 against the reference vector, cross-checked against the system
  implementation where available;
- negative controls: wrong message, wrong address, corrupted signature,
  bad checksums, bad mnemonics.

If any check fails on your machine, do not use the tool. Please open an issue.

## What it proves, and what it doesn't

Proves: at some point, the holder of the private key(s) for an address (or of
a seed that derives that address) produced a signature over a challenge you
specified. If you generated the nonce yourself, this is proof of control at
that time.

Does not prove:

- exclusive control in the past or future (a key can be copied; a seed can be
  shared or cracked by others);
- that the address holds funds today — check the chain yourself;
- anything for taproot (`bc1p…`) addresses — standard message signatures are
  ECDSA and cannot bind a taproot key. The tool rejects such addresses
  explicitly rather than pretending.

For a seed-phrase owner, a derivation match proves the mnemonic derives the
claimed address. It is not a signature and carries no timestamp; if a
challenge-response proof is needed, sign from the wallet or sweep key instead.

## Trust model

- Runs offline. It contains no networking code. You can run it on an
  air-gapped machine; the challenge and signature move on paper or USB.
- The tool never receives, stores, or transmits keys or seed words. Nothing is
  written to disk.
- Everything is in one file, `prover.py` (standard library only), so you can
  read the whole thing before running it. We encourage exactly that.
- The cryptographic primitives are checked at every startup-capable point
  against published test vectors (see `selftest` above). Where our code could
  silently disagree with the ecosystem — key derivation, address encoding,
  message signing — the selftest anchors it to vectors from the Bitcoin BIP
  specifications and Bitcoin Core's test suite, not to our own outputs.

You should still verify for yourself: read `prover.py`, run `selftest`, and if
you want, cross-check a derived address or a signature against independent
wallet software.

## Usage

### Route 1 — sign a challenge (wallet owners)

```
python3 prover.py challenge --address <the address>          > challenge.txt
# sign the exact text of challenge.txt in your own wallet software
python3 prover.py verify --address <the address> \
        --challenge-file challenge.txt --signature <the signature>
```

Exit code 0 and `VERIFIED` means the signature matches. The signature may be
base64 (Bitcoin Core, Electrum) or base58-encoded; both are accepted.

The challenge format is fixed and documented in `prover.py`
(`CHALLENGE_TEMPLATE`): domain separator `decruptor-ownership-v1`, a 256-bit
random nonce, the address, a UTC timestamp, and an optional note. The nonce
must come from a source the verifier trusts (this tool uses the operating
system's `os.urandom`).

### Route 2 — derivation check (seed owners)

```
python3 prover.py derive-check \
        --path "m/84'/0'/0'/0/*" \
        --address <claimed address>
```

You will be prompted for the mnemonic and BIP39 passphrase; input is not
echoed. Default path checks the first 20 indices of a standard native-segwit
account; adjust `--path`/`--count` for legacy (`m/44'/…`), nested segwit
(`m/49'/…`), or other layouts. The output is `MATCH at <path>` or
`NO MATCH` — nothing else. `--show-derived` prints derived addresses to
stderr, for local debugging only.

### Verify a plain signed message

```
python3 prover.py verify --address <addr> --message "any text" --signature <sig>
```

## What we can and cannot verify

Verified against external, published vectors (class [V] in the selftest):
BIP39 seed derivation and checksums, BIP32 key derivation and xprv/xpub
serialization, BIP84 account addresses, deterministic message signing
(byte-exact against Bitcoin Core), bech32/bech32m, base58check, RIPEMD-160.

Not covered: taproot addresses, bare P2WSH addresses as ownership targets,
multisig, Lightning nodes, ETH/Solana-style `personal_sign` chains (planned
as a separate, equally small module).

## License

MIT. See `LICENSE`.
