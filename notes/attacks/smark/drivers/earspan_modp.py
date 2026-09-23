#!/usr/bin/env python3
"""earspan_modp.py -- do the ear-span certificates of S16(iii)(c)/S17(v) survive
reduction to characteristic p?  (Review 3, 2026-09-23; workbook S18(ii); O11.)

Re-draws exactly the cells of `earspan.py` (same seeds, same rng sequence, same
`s`), clears denominators from each Pluecker vector (projectively harmless), and
takes the rank of the m+1 integer vectors over F_p for each listed prime, next to
the exact Q-rank.  A draw at rank 6 over F_p is a certificate for the generic ear
at the *reduced* flag pair over any infinite field of characteristic p; the
reduced flags may lie in a more degenerate PGL_4-orbit than the cell's name, and a
certificate at a more degenerate orbit covers every orbit whose closure contains
it (S17(v)) -- equal flags cover all seven.  A Q-certificate proves the spanning
in characteristic 0 and at every p not dividing its 6x6 minor, nothing more.

Run from the repository root:
    timeout 300 python3 notes/attacks/smark/drivers/earspan_modp.py
"""
import argparse
import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import earspan as E  # noqa: E402


def primitive(v):
    """Clear denominators and common factors: an integer vector, same projective point."""
    den = 1
    for x in v:
        den = den * x.denominator // math.gcd(den, x.denominator)
    w = [int(x * den) for x in v]
    g = 0
    for x in w:
        g = math.gcd(g, abs(x))
    return [x // g for x in w]


def rank_mod(rows, p):
    M = [[x % p for x in r] for r in rows]
    r = 0
    for c in range(len(M[0])):
        piv = next((i for i in range(r, len(M)) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], -1, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r


def run(seed, ms, regimes, primes, draws, s):
    rng = random.Random(seed)
    for m in ms:
        for regime in regimes:
            made, q6 = 0, 0
            cert = {p: 0 for p in primes}
            while made < draws:
                flags = E.draw_flags(rng, s, regime)
                if flags is None:
                    continue
                L = E.ear_lines(rng, s, m, flags)
                if L is None:
                    continue
                made += 1
                if E.rank(L) == 6:
                    q6 += 1
                Lint = [primitive(l) for l in L]
                for p in primes:
                    if rank_mod(Lint, p) == 6:
                        cert[p] += 1
            print(f'  seed={seed} m={m} lines={m + 1} regime={regime:10s} Q-rank6 {q6}/{made}  '
                  + '  '.join(f'F{p}:{cert[p]}/{made}' for p in primes))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--draws', type=int, default=20)
    ap.add_argument('--s', type=int, default=20)
    ap.add_argument('--primes', default='2,3,5,7,11,13')
    a = ap.parse_args()
    primes = [int(t) for t in a.primes.split(',')]
    print(f'earspan_modp.py draws={a.draws} s={a.s} primes={primes}')
    # The two S16(iii)(c) regimes at their seed, then the three S17(v) regimes at theirs.
    run(20260922, [5, 6], ['generic', 'incident'], primes, a.draws, a.s)
    run(20260923, [5, 6, 7], ['coinc-pt', 'coinc-pl', 'coinc-both'], primes, a.draws, a.s)


if __name__ == '__main__':
    main()
