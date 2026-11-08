"""Phase 43b (LIFT3) open: the blueprint dependency graph after each Lean slice (banked).

Parses the chapters with `scripts/blueprint-deps.py`'s `parse_tex` (statement and proof `\\uses`
both, as `premise_closure.py` does), applies the node deletions and `\\uses` edits that
`notes/Phase43b.md` plans for its slices 1-3, cumulatively, and prints after each: the number of
cycles, the nodes that had a user at the start and have none, and which of the `d = 3` statement
nodes the closure of `thm:pencil-d-generic` (the lift, C) reaches. Reads the tree at the
working directory, so its figures are for that commit (written at f5100f28, the open); an edit
already landed is skipped, not an error. From the repo root:

  python3 notes/pencil-natural/n1c_graph.py
"""
import sys, importlib.util
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("bd", ROOT / "scripts" / "blueprint-deps.py")
bd = importlib.util.module_from_spec(spec); spec.loader.exec_module(bd)
envs, _notes = bd.parse_tex(ROOT / "blueprint" / "src")
G = {e["label"]: set(e["stmt_uses"]) | set(e["proof_uses"]) for e in envs if e["label"]}
START = {k: set(v) for k, v in G.items()}

def cycles():
    sys.setrecursionlimit(100000)
    color, found = {}, []
    def dfs(u, stack):
        color[u] = 1; stack.append(u)
        for v in sorted(G.get(u, ())):
            if v not in G: continue
            if color.get(v) == 1: found.append(stack[stack.index(v):] + [v])
            elif v not in color: dfs(v, stack)
        stack.pop(); color[u] = 2
    for u in sorted(G):
        if u not in color: dfs(u, [])
    return found

def closure(root):
    seen, stack = set(), [root]
    while stack:
        x = stack.pop()
        if x in seen: continue
        seen.add(x); stack.extend(G.get(x, ()))
    return seen

def delete(*labels):
    for d in labels:
        G.pop(d, None)
    for k in G:
        G[k] -= set(labels)

def setuses(label, remove=(), add=()):
    if label in G:
        G[label] -= set(remove); G[label] |= set(add)

D3 = ["thm:pencil-x0-generic-attains", "thm:pencil-conditioned-pair-nonempty",
      "thm:pencil-realization-theorem", "cor:pencil-d-conditioned-pair",
      "thm:pencil-conditional-realization-main-component", "thm:pencil-conditional-realization-pair",
      "lem:pencil-pair-loop-base-cut", "lem:pencil-nonsimple-case"]

def report(name):
    users = {}
    for k, vs in G.items():
        for v in vs: users.setdefault(v, set()).add(k)
    had = {v for vs in START.values() for v in vs}
    orphaned = sorted(l for l in G if l in had and not users.get(l))
    cl = closure("thm:pencil-d-generic")
    print(f"{name}: {len(G)} labelled nodes, {len(cycles())} cycles; orphaned {orphaned}; "
          f"|closure(thm:pencil-d-generic)| = {len(cl)}, reaching {[l for l in D3 if l in cl]}")

report("start")
# Slice 1 (N1a): x0Gen from the lift.
delete("thm:pencil-x0-base-generic", "lem:pencil-generic-one-ear",
       "lem:pencil-generic-pendant-triangle", "thm:pencil-generic-step")
setuses("thm:pencil-d-generic", remove=["thm:pencil-conditioned-pair-nonempty"])
setuses("thm:pencil-x0-generic-attains", remove=["thm:pencil-conditioned-pair-nonempty"],
        add=["thm:pencil-d-generic", "lem:pencil-d-nondegenerate-three"])
setuses("thm:pencil-conditioned-pair-nonempty",
        remove=["lem:pencil-x0-distinct-statement", "lem:pencil-pair-loop-base-cut",
                "lem:pencil-nonsimple-case"],
        add=["thm:pencil-conditional-realization-main-component", "thm:pencil-x0-generic-attains"])
setuses("lem:pencil-rigid-good-ear", remove=["lem:deficiency-tight-rigid",
        "lem:deficiency-merge-rigid", "lem:deficiency-ear-merge"])
report("slice 1")
# Slice 2: pencilPair_of_nonempty as the m = 1 case; N1b's deletions.
delete("lem:pencil-pair-loop-base-cut", "thm:pencil-conditional-realization-pair",
       "thm:pencil-conditional-realization-main-component")
setuses("cor:pencil-d-conditioned-pair", remove=["thm:pencil-conditioned-pair-nonempty"])
setuses("thm:pencil-conditioned-pair-nonempty",
        remove=["thm:pencil-x0-generic-attains"],
        add=["cor:pencil-d-conditioned-pair", "lem:pencil-d-rank-agrees-three",
             "lem:pencil-d-nondegenerate-three"])
report("slice 2")
# Slice 3: the rest of N1c's deletions.
delete("lem:pencil-loop-case", "lem:pencil-cut-case", "lem:pencil-base-case",
       "lem:pencil-nonsimple-case", "lem:extensor-pair-through-point",
       "lem:pencil-projective-transport")
report("slice 3")
