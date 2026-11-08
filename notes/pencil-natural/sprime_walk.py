"""Phase 43c (SPRIME) pin: the blueprint and docstring side of the liveness walk (banked).

Reads the report of `notes/pencil-natural/SprimeSpike.lean` on stdin (its `SPRIME ...` lines: the
kernel walk's DEAD, ORPHAN, UNREACHED, MAPPED and RECHECKED constants, and the members of slices B
and C), the blueprint with `scripts/blueprint-deps.py`'s `parse_tex` (statement and proof `\\uses`
both, as `n1c_graph.py` does), and the tracked files of the tree. Prints:

1. every node with a pin the slices delete or a pin no root reaches, and its verdict: deleted in
   a slice (every pin gone, once slice A's two successor pins are added), or restated (some pins
   dropped);
2. the blueprint graph after slices A, B and C, with the node deletions of (1) and the `\\uses`
   edits the restatements make (`EDITS` below, transcribed from `notes/Phase43c.md` items 3-5):
   the edges into a deleted node that survive (each must be an edit), the nodes orphaned (had a
   user at the start, have none), and the cycles;
3. the sweep: every occurrence, in a tracked file of any kind, of a deleted declaration's name or
   distinctive stem, or of a deleted label, outside the declarations and files the slices delete.

Reads the working tree, so its figures are for that commit (written at 2b010699, 43c's slice 1).
Once a slice lands, its names are absent from the report and its nodes from the blueprint: the
edits on an absent node are skipped, and that slice's sweep in (3) is empty, so the landing commit
runs its own sweep (slice B's, 2026-11-08, also swept the `d = 3` core bound the PI added to it).
From the repo root (about a minute, nearly all of it `lake lean`):

  lake lean notes/pencil-natural/SprimeSpike.lean 2>&1 | python3 notes/pencil-natural/sprime_walk.py
"""
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("bd", ROOT / "scripts" / "blueprint-deps.py")
bd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bd)

# ---- the Lean report ------------------------------------------------------------------------
tag_of, slice_of, where = {}, {}, {}
for line in sys.stdin:
    p = line.split()
    if len(p) < 6 or p[0] != "SPRIME" or p[1] in ("WALK:", "SLICE"):
        continue
    tag, mod, a, b, name = p[1], p[2], int(p[3]), int(p[4]), p[5]
    where[name] = (mod, a, b)
    if tag.startswith("SLICE-"):
        slice_of[name] = tag[len("SLICE-"):]
    else:
        tag_of.setdefault(name, set()).add(tag)
if not slice_of:
    sys.exit("no SPRIME report on stdin: pipe `lake lean notes/pencil-natural/SprimeSpike.lean`")

# Slice A's new declarations (NEW-1, NEW-2), pinned as successors.
NEW1 = "Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt"
NEW2 = "Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero"
ADD_PINS = {"A": {"lem:deficiency-two-body-chain": [NEW1], "lem:pencil-d-chain-core": [NEW2]}}

# ---- (1) the nodes and their pins -----------------------------------------------------------
envs, _ = bd.parse_tex(ROOT / "blueprint" / "src")
nodes = {e["label"]: e for e in envs if e["label"]}
ORDER = ["A", "B", "C"]
print("== (1) nodes with a deleted or unreached pin")
node_del, node_restate = {}, {}
for lab, e in nodes.items():
    pins = list(e["pins"])
    for s in ORDER:
        pins += ADD_PINS.get(s, {}).get(lab, [])
    gone = {q: slice_of[q] for q in pins if q in slice_of}
    unreached = [q for q in pins if "UNREACHED" in tag_of.get(q, ())]
    if not gone and not unreached:
        continue
    live = [q for q in pins if q not in gone]
    if gone and not live:
        node_del[lab] = max(gone.values(), key=ORDER.index)
        verdict = f"DELETE in slice {node_del[lab]}"
    elif gone:
        node_restate[lab] = sorted(set(gone.values()))
        verdict = f"RESTATE in slice(s) {','.join(node_restate[lab])}: drop {sorted(gone)}"
    else:
        verdict = "kept (its pin is reached by no root: held by the pin alone)"
    print(f"{lab}  [{e['file']}:{e['line']}]  {verdict}")
    for q in pins:
        st = gone.get(q) and f"slice {gone[q]}" or "/".join(sorted(tag_of.get(q, {"live"})))
        print(f"    {q}: {st}")
pinned = {q for e in envs for q in e["pins"]}
loose = sorted(n for n, t in tag_of.items() if "UNREACHED" in t and n not in pinned)
print(f"unreached at HEAD and pinned by no node (before SPRIME; not its business): {loose}")

# ---- (2) the blueprint graph per slice ------------------------------------------------------
G = {lab: set(e["stmt_uses"]) | set(e["proof_uses"]) for lab, e in nodes.items()}
START = {k: set(v) for k, v in G.items()}
# The `\uses` edits of the restatements, per slice: (label, removed, added).
EDITS = {
    "A": [("lem:deficiency-two-body-chain", ["lem:deficiency-two-body-chain-d"], []),
          ("lem:deficiency-two-body-chain-d",
           ["lem:deficiency-singleton-bound", "lem:deficiency-add-body",
            "lem:deficiency-tight-rigid"], ["lem:deficiency-two-body-chain"])],
    "B": [("lem:deficiency-one-body-chain",
           ["lem:separated-partition-value", "lem:deficiency-one-body-chain-d"], []),
          ("lem:deficiency-two-body-chain", ["lem:deficiency-merge-rigid"], []),
          # S′'s proof as the Lean runs it (the PI, after the pin): every core from
          # `lem:pencil-d-maximal-rigid-core`, so the `d = 3` core bound and the two lemmas the
          # old core argument cited leave its `\uses`
          ("thm:pencil-x0-theorem-s",
           ["lem:deficiency-one-body-chain", "def:pencil-d-usable-chain",
            "thm:pencil-d-theorem-s", "lem:deficiency-core-bound", "lem:deficiency-add-body",
            "lem:deficiency-additive-core"],
           ["lem:pencil-d-chain-core", "lem:pencil-d-core-positive-deficiency",
            "lem:pencil-d-maximal-rigid-core"]),
          ("thm:pencil-x0-reduction-attains",
           ["thm:pencil-x0-open-ear-two", "thm:pencil-x0-splitoff"], [])],
    "C": [],
}


def cycles():
    sys.setrecursionlimit(100000)
    color, found = {}, []

    def dfs(u, stack):
        color[u] = 1
        stack.append(u)
        for v in sorted(G.get(u, ())):
            if v not in G:
                continue
            if color.get(v) == 1:
                found.append(stack[stack.index(v):] + [v])
            elif v not in color:
                dfs(v, stack)
        stack.pop()
        color[u] = 2

    for u in sorted(G):
        if u not in color:
            dfs(u, [])
    return found


print("\n== (2) the blueprint graph")
had = {v for vs in START.values() for v in vs}
deleted_labels = {}
for s in ORDER:
    for lab, rem, add in EDITS[s]:
        if lab not in G:  # a node a landed slice deleted (the walk reads the working tree)
            print(f"  slice {s}: edit of {lab}: the node is absent")
            continue
        missing = [r for r in rem if r not in G.get(lab, set())]
        if missing:
            print(f"  slice {s}: edit of {lab} removes {missing}, not among its uses")
        G[lab] = (G[lab] - set(rem)) | set(add)
    dels = sorted(lab for lab, t in node_del.items() if t == s)
    for d in dels:
        deleted_labels[d] = s
        G.pop(d, None)
    dangling = sorted(f"{k} -> {v}" for k, vs in G.items() for v in vs if v in deleted_labels)
    users = {}
    for k, vs in G.items():
        for v in vs:
            users.setdefault(v, set()).add(k)
    orphans = sorted(lab for lab in G if lab in had and not users.get(lab))
    print(f"slice {s}: {len(dels)} nodes deleted {dels}; {len(G)} nodes; "
          f"{len(cycles())} cycles\n  edges into a deleted node that survive: {dangling}\n"
          f"  orphaned (a user at the start, none now): {orphans}")

# ---- (3) the sweep --------------------------------------------------------------------------
print("\n== (3) the sweep: occurrences outside the deleted declarations, nodes and files")
# what a slice deletes whole: files, and blueprint sections
DELETED_FILES = {
    "C": ["CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/SplitOff.lean",
          "CombinatorialRigidity/Mathlib/Data/Matrix/Mul.lean",
          "CombinatorialRigidity/Mathlib/Algebra/MvPolynomial/Polynomial.lean"]}
DELETED_SECTIONS = {"C": ["sec:main-component-splitoff"]}

raw = {}


def lines_of(f):
    if f not in raw:
        raw[f] = (ROOT / f).read_text().split("\n")
    return raw[f]


def env_range(e):
    """The lines of a node: its environment, then its proof and a formalization note after it."""
    path = "blueprint/src/" + e["file"]
    ls = lines_of(path)
    i, env = e["line"], e["env"]
    j = next(k for k in range(i, len(ls) + 1) if f"\\end{{{env}}}" in ls[k - 1])
    for follow in ("proof", "fmlnote"):
        k = j + 1
        while k <= len(ls) and not ls[k - 1].strip():
            k += 1
        if k <= len(ls) and ls[k - 1].lstrip().startswith(f"\\begin{{{follow}}}"):
            j = next(m for m in range(k, len(ls) + 1) if f"\\end{{{follow}}}" in ls[m - 1])
    return path, i, j


def section_range(label):
    for f in sorted((ROOT / "blueprint/src/chapter").glob("*.tex")):
        path = str(f.relative_to(ROOT))
        ls = lines_of(path)
        for k, ln in enumerate(ls, 1):
            if f"\\label{{{label}}}" in ln:
                start = k - 1  # the sectioning command is on the line before its label
                end = next((m - 1 for m in range(k + 1, len(ls) + 1)
                            if re.match(r"\\(sub)*section\b", ls[m - 1].lstrip())), len(ls))
                return path, start, end
    raise SystemExit(f"no section {label}")


def mod_file(mod):
    return mod.replace(".", "/") + ".lean"


def dead_upto(s):
    """The files and line ranges the slices up to `s` delete."""
    upto = ORDER[:ORDER.index(s) + 1]
    files = {f for t in upto for f in DELETED_FILES.get(t, [])}
    ranges = {}
    for n, t in slice_of.items():
        if t in upto:
            mod, a, b = where[n]
            ranges.setdefault(mod_file(mod), []).append((a, b))
    for lab, t in deleted_labels.items():
        if t in upto:
            f, a, b = env_range(nodes[lab])
            ranges.setdefault(f, []).append((a, b))
    for t in upto:
        for sec in DELETED_SECTIONS.get(t, []):
            f, a, b = section_range(sec)
            ranges.setdefault(f, []).append((a, b))
    return files, ranges


# patterns per deleted declaration: the full name, the name less `CombinatorialRigidity.Molecular.`,
# and the distinctive stem (its last component, or the forms a constructor needs)
STEMS = {
    "Graph.X0Reduces.openEarTwo": [r"\.openEarTwo"],
    "Graph.X0Reduces.splitOff": [r"\.splitOff hear"],
    "Graph.X0Attains.of_openEar_two": [r"\bof_openEar_two"],
    "Graph.X0Attains.of_splitOff": [r"\bof_splitOff"],
}
END = r"(?![\w'])"


def patterns(n):
    short = n.replace("CombinatorialRigidity.Molecular.", "")
    last = n.split(".")[-1]
    pats = [re.escape(n), r"(?<![\w])" + re.escape(short)]
    if n in STEMS:
        pats += STEMS[n]
    elif "_" in last and len(last) >= 12:
        pats.append(r"\b" + re.escape(last))
    return re.compile("|".join(f"(?:{q}){END}" for q in pats))


def label_pattern(lab):
    return re.compile(r"(?<![\w:-])" + re.escape(lab) + r"(?![\w-])")


files = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True,
                       check=True).stdout.split()
files = [f for f in files if f.endswith((".lean", ".tex", ".md", ".py", ".yaml", ".yml", ".toml",
                                         ".sh", ".txt", ".bib"))
         and not f.startswith("notes/pencil-natural/")]
texts = {}
for f in files:
    try:
        texts[f] = (ROOT / f).read_text().split("\n")
    except (UnicodeDecodeError, FileNotFoundError):
        pass

# notes read on load are listed in full; closed records get a count per file
ACTIVE_NOTES = {"notes/Phase43c.md", "notes/Phase43-design.md", "notes/PencilNatural.md",
                "notes/FRICTION.md", "notes/BlueprintExposition.md"}

for s in ["B", "C"]:
    dfiles, dranges = dead_upto(s)
    print(f"-- slice {s} (excluded: the files, declarations, nodes and sections of slices up to "
          f"{s})")
    items = [(n, patterns(n)) for n, t in sorted(slice_of.items()) if t == s]
    items += [(lab, label_pattern(lab)) for lab, t in sorted(deleted_labels.items()) if t == s]
    items += [(sec, label_pattern(sec)) for sec in DELETED_SECTIONS.get(s, [])]
    for name, pat in items:
        live, closed = [], {}
        for f, ls in texts.items():
            if f in dfiles:
                continue
            for i, ln in enumerate(ls, 1):
                if not pat.search(ln) or any(a <= i <= b for a, b in dranges.get(f, ())):
                    continue
                if f.startswith("notes/") and f not in ACTIVE_NOTES:
                    closed[f] = closed.get(f, 0) + 1
                else:
                    live.append((f, i, ln.strip()))
        print(f"{name}: {len(live)} live hit(s)"
              + (f"; closed records {dict(sorted(closed.items()))}" if closed else ""))
        for f, i, ln in live:
            print(f"    {f}:{i}: {ln[:110]}")

# ---- (4) the step's name, and the sizes ------------------------------------------------------
print("\n== (4) the split-off step and the deleted files by name, outside notes/ (prose to restate"
      " in slice C, or B where it describes the coverage); excluded as in (3)")
STEP = re.compile(r"SplitOff\.lean|split-off|thirteen constructors|Data/Matrix/Mul\.lean|"
                  r"Data\.Matrix\.Mul\b|Algebra/MvPolynomial/Polynomial\.lean|"
                  r"Algebra\.MvPolynomial\.Polynomial\b")
dfiles, dranges = dead_upto("C")
for f, ls in sorted(texts.items()):
    if f in dfiles or f.startswith("notes/"):
        continue
    for i, ln in enumerate(ls, 1):
        if STEP.search(ln) and not any(a <= i <= b for a, b in dranges.get(f, ())):
            print(f"    {f}:{i}: {ln.strip()[:110]}")

print("\n== (5) sizes: the lines each slice deletes outright (declarations, nodes, sections)")


def covered(ranges):
    return sum(len(set().union(*(range(a, b + 1) for a, b in rs))) for rs in ranges.values())


for s in ["B", "C"]:
    lean, tex = {}, {}
    for n, t in slice_of.items():
        if t == s:
            mod, a, b = where[n]
            lean.setdefault(mod_file(mod), []).append((a, b))
    for lab, t in deleted_labels.items():
        if t == s:
            f, a, b = env_range(nodes[lab])
            tex.setdefault(f, []).append((a, b))
    for sec in DELETED_SECTIONS.get(s, []):
        f, a, b = section_range(sec)
        tex.setdefault(f, []).append((a, b))
    whole = {f: len(lines_of(f)) for f in DELETED_FILES.get(s, [])}
    print(f"slice {s}: Lean {covered(lean)} declaration lines; whole files {whole}; "
          f"TeX {covered(tex)} lines of deleted nodes and sections")
