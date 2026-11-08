"""Phase 43a premise check (READS, D3 (1)): `\\uses` closures in the blueprint (banked).

Parses the chapters with `scripts/blueprint-deps.py`'s `parse_tex`, statement and proof
`\\uses` both, and walks closures. Written by the premise-check reader of 2026-11-07
(`notes/Phase43a.md`); banked with this docstring and a repo-relative root, otherwise as run.
Its reading is `notes/Phase43a.md`, the premise check's item. Modes, from the repo root:

  python3 notes/pencil-natural/premise_closure.py sec pencil-d.tex 5143 6764
      the labelled nodes of sec:pencil-d-lift and sec:pencil-d-generic (C's roots)
  python3 notes/pencil-natural/premise_closure.py cut ROOTS B EXCL
      |closure(ROOTS)| with the edges EXCL (`src>tgt`, comma-separated) removed, its
      intersection with closure(B), and a path to each common node
  node / closure / inter / rdeps / path: the single-node, closure, intersection, reverse-
      dependency and path queries the reader ran by hand

The cycle simulation of the reader's report is not reproduced by these modes.
"""
import sys, importlib.util
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("bd", ROOT / "scripts" / "blueprint-deps.py")
bd = importlib.util.module_from_spec(spec); spec.loader.exec_module(bd)
envs, notes = bd.parse_tex(ROOT / "blueprint" / "src")
nodes = {e["label"]: e for e in envs if e["label"]}
def deps(l, which="both"):
    e = nodes.get(l)
    if not e: return []
    if which == "stmt": return e["stmt_uses"]
    if which == "proof": return e["proof_uses"]
    return e["stmt_uses"] + e["proof_uses"]
def closure(roots):
    seen, stack = set(), list(roots)
    parent = {r: None for r in roots}
    while stack:
        x = stack.pop()
        if x in seen: continue
        seen.add(x)
        for y in deps(x):
            if y not in seen:
                parent.setdefault(y, x); stack.append(y)
    return seen, parent
def path(parent, x):
    p = []
    while x is not None:
        p.append(x); x = parent[x]
    return " <- ".join(p)
mode = sys.argv[1]
if mode == "sec":
    f, lo, hi = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    for e in envs:
        if e["file"].endswith(f) and lo <= e["line"] <= hi:
            print(e["line"], e["env"], e["label"], "S:", e["stmt_uses"], "P:", e["proof_uses"])
elif mode == "node":
    for l in sys.argv[2:]:
        e = nodes[l]; print(l, e["file"], e["line"], e["env"], "pins:", e["pins"], "S:", e["stmt_uses"], "P:", e["proof_uses"])
elif mode == "closure":
    roots = sys.argv[2].split(",")
    cl, parent = closure(roots)
    for l in sorted(cl, key=lambda l: (nodes[l]["file"], nodes[l]["line"]) if l in nodes else ("?",0)):
        e = nodes.get(l)
        print(e["file"] if e else "?", e["line"] if e else "?", l)
elif mode == "inter":
    # closure of A intersected with closure of B, with paths
    A = sys.argv[2].split(","); B = sys.argv[3].split(",")
    ca, pa = closure(A); cb, pb = closure(B)
    for l in sorted(ca & cb, key=lambda l: (nodes[l]["file"], nodes[l]["line"]) if l in nodes else ("?",0)):
        e = nodes.get(l)
        print(f"{e['file'] if e else '?'}:{e['line'] if e else '?'} {l}\n    via C: {path(pa,l)}")
elif mode == "rdeps":
    # nodes that directly use X
    for x in sys.argv[2:]:
        print(x, "used by:")
        for e in envs:
            if not e["label"]: continue
            s = x in e["stmt_uses"]; p = x in e["proof_uses"]
            if s or p: print("   ", e["file"], e["line"], e["label"], "stmt" if s else "", "proof" if p else "")
elif mode == "path":
    A = sys.argv[2].split(","); tgt = sys.argv[3]
    ca, pa = closure(A)
    print(tgt in ca, path(pa, tgt) if tgt in ca else "")
if mode == "cut":
    # closure of roots A, with edges in EXCL (src>tgt) removed; intersect with closure of B; print paths
    A = sys.argv[2].split(","); B = sys.argv[3].split(","); excl = set(tuple(x.split(">")) for x in sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()
    def deps2(l):
        return [y for y in deps(l) if (l, y) not in excl]
    def closure2(roots):
        seen, stack = set(), list(roots); parent = {r: None for r in roots}
        while stack:
            x = stack.pop()
            if x in seen: continue
            seen.add(x)
            for y in deps2(x):
                if y not in seen: parent.setdefault(y, x); stack.append(y)
        return seen, parent
    ca, pa = closure2(A); cb, pb = closure(B)
    print(f"|closure(C)|={len(ca)}  |closure(B)|={len(cb)}  |inter|={len(ca & cb)}")
    for l in sorted(ca & cb, key=lambda l: (nodes[l]["file"], nodes[l]["line"]) if l in nodes else ("?",0)):
        e = nodes.get(l)
        print(f"{e['file'] if e else '?'}:{e['line'] if e else '?'} {l}\n    via C: {path(pa,l)}")
