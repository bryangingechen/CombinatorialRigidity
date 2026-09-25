#!/usr/bin/env python3
"""treegrep.py (§(K-main) Step MC20's second reading, 2026-09-25; ported from the reader's scratch): for each claim on (MC-89)'s proof path, extract its owning passage (claim block
+ proof, up to the next claim or heading) from K-main.md at HEAD and list every sentence that
names a driver or a computation word.  Deterministic; no randomness."""
import re, sys
TXT = open(sys.argv[1], encoding='utf-8').read().split('\n')
TREE = [2,3,4,5,13,14,16,17,18,19,20,21,22,24,25,26,28,29,30,31,34,35,36,37,38,39,
        45,46,48,52,53,54,55,56,59,62,63,67,68,69,71,75,76,77,78,79,80,87,89]
starts = {}
for i, l in enumerate(TXT):
    m = re.match(r'^> \*\*\(MC-(\d+)\)', l)
    if m and int(m.group(1)) not in starts:
        starts[int(m.group(1))] = i
heads = [i for i, l in enumerate(TXT) if l.startswith('#')]
allstarts = sorted(starts.values())
PAT = re.compile(r'(\w+\.py|\.m2|certif|exhibit|asserted|measured|MEASURED|CONSTRUCTED|'
                 r'computed|by computer|checked|random|draw)', re.I)
for n in TREE:
    s = starts.get(n)
    if s is None:
        print(f'(MC-{n}): no claim block found'); continue
    nxt = min([j for j in allstarts if j > s] + [j for j in heads if j > s] + [len(TXT)])
    hits = [(i + 1, TXT[i].strip()) for i in range(s, nxt) if PAT.search(TXT[i])]
    print(f'(MC-{n}) lines {s+1}-{nxt}: {len(hits)} hit lines')
    for ln, t in hits:
        print(f'    {ln}: {t[:160]}')
