#!/usr/bin/env python3
"""Audit the blueprint's dependency graph against what each node's Lean pins reach.

Written for PROSE round 1, task 2 (`notes/Prose.md` §5; `notes/Prose-laman-cleanup.md`
*Lemma checklist*). Usage, from anywhere (paths resolve against the repository root):

    python3 scripts/blueprint-deps.py                 # the full report: (1)-(3), with the summary
    python3 scripts/blueprint-deps.py --summary       # the per-chapter counts only
    python3 scripts/blueprint-deps.py --label LABEL   # one node in full, reach chains included
    python3 scripts/blueprint-deps.py --chapter NAME  # one chapter's nodes (`sparsity`, `case-i`)
    python3 scripts/blueprint-deps.py --dump          # report (4); runs no Lean

`--label` and `--chapter` repeat and combine. `--tex-root DIR` reads the chapters from `DIR`
(a scratch copy of `blueprint/src`) instead; `--no-cache` forces a fresh Lean run.

**Inputs.** From the TeX: every node, i.e. every `definition`, `lemma`, `theorem`, `corollary` and
`proposition` environment (plastexdepgraph's default node types), with its `\\label`, `\\lean{…}`
pins, `\\leanok`, and statement-level `\\uses`; and each `proof` with its `\\uses` and `\\leanok`.
The files are read in document order, following `\\input` from `chapter/main.tex`, with TeX
comments stripped. A proof belongs to the nearest preceding theorem-like environment (any
`\\newtheorem` environment of `preamble/common.tex`) in the same sectioning unit, as
plastexdepgraph's `find_proved_thm` attaches it; a proof with `\\uses` that lands on a remark, an
example or a formalization note, or on nothing, is listed under *parse notes*. From
`formalization.yaml`: the `declaration:` of every entry of `status.main_results`.

**The Lean half** is `scripts/BlueprintDeps.lean`, run with `lake lean` (never `lake env lean`,
which drops the lakefile's options). For every constant declared in a project module (the
`CombinatorialRigidity` modules, the `Mathlib/` and `Matroid/` mirrors, private declarations and
the auxiliary `match_`, `proof_` and `_simp_` declarations included) it lists the project or
pinned constants in the constant's type and in its value; an inductive type's value is its
constructors. **It is a non-`module` file**, because only a non-`module` importer sees the theorem
bodies and the private declarations of the project's `module` files; its docstring records the
measurement. A witness that it does: `thm:isSparse-exists-typeI-or-typeII-reverse`'s pin reaches
`lem:isSparse-typeII-reverse-blocker`'s through the private `IsSparse.typeII_pair_dispatch_aux`,
in the proof of a theorem of the `module` file `Sparsity.lean` (`--label` prints the chain).
Its output is cached under `.lake/blueprint-deps/` (gitignored), keyed by the pins and by the
content of the Lean sources, the lake files and the metaprogram (their git objects at `HEAD`, any
uncommitted diff, and untracked files); `--no-cache` runs Lean afresh. A fresh run takes about two
minutes, nearly all of it `lake lean` checking the library's build jobs; a cached run, under a
second.

**Reach.** A pin's *type reach* is the set of pins met by following the constants of its type
through unpinned project constants (their types and values both), stopping at pinned constants and
at constants from outside the project; its *value reach* starts from the constants of its value
instead. For a definition the value is its body, so a definition node's reach "through the
proof" is its defining content. A node reaches the nodes whose pins its own pins reach (a pin on
several nodes reaches all of them; a pin's own nodes are skipped). Only node pins stop the reach:
a pin on another environment (one `example` today) is followed through, and listed as a parse
note.

**Reports.**

1. Per node, its reach against its `\\uses` (statement and proof together):
   - *missing*: a node the pins reach that `\\uses` does not name, and that is not already an
     ancestor of the node in the `\\uses` graph: the built graph does not show the dependency.
     One that would close a cycle (the target already depends on the node) is marked: it needs a
     change of node shape, not an edge;
   - *implied*: such a node that is already an ancestor. plastexdepgraph draws the transitive
     reduction (graphviz `tred`), so adding the edge would change nothing that is drawn;
   - *unbacked* (for a check, not defects): a `\\uses` target no pin reaches. It is *transitive*
     when the Lean reaches it only through another pinned node, and has *no Lean basis* when the
     Lean does not reach it at all;
   - a node with no pin is *unchecked*: its `\\uses` are counted, not compared; and a node
     without `\\leanok`, which the graph draws unfilled, is listed.
   Each missing or implied edge is tagged *statement* (type reach) or *proof* (value reach only),
   with the pin that reaches and the pin reached; `--label` prints the chain of constants between.
2. Pins outside the closure of every main result: the closure follows all project constants,
   pinned or not, through types and values (`CLEANUP.md` §B's liveness, read from the Lean).
3. Pins per node, with four or more flagged (`blueprint/AUTHORING.md` principle D).
4. `--dump`: the built graph `blueprint/web/dep_graph_document.html`, parsed exactly as the PROSE
   rounds' invariance check (`CLEANUP.md` §A) parses it, so its first line is that check's first
   line (`<edges> edges <fingerprint>`) and its second is the check's `lean_decls` hash. Then
   every sorted graph statement (edges, nodes and graph attributes, the list the fingerprint
   hashes), then the label→pins map read from the TeX, sorted by label, then the label→`\\uses`
   map read from the TeX: per node, its statement's targets and its proof's apart, each sorted,
   a target that is not a node included (a labelled environment that is not a node gets a line
   when it has a `\\uses`). The drawn graph is a transitive reduction, so removing an edge,
   adding an implied one or moving one between statement and proof can leave every drawn edge as
   it was; the `\\uses` section shows each. Round 5's expected-diff gate diffs two dumps
   (`notes/Prose-graph-cleanup.md`, whose task 2 added the `\\uses` section).

**Consistency checks**, run with the default `--tex-root` when the built graph and
`blueprint/lean_decls` exist and are not older than the TeX: the TeX's `\\uses` edges between
nodes, transitively reduced, must equal the built graph's edges, and the TeX's pins must equal
`lean_decls` as a multiset. A mismatch means the TeX parse is wrong and the report is not to be
trusted; it is printed first, and the exit code is 1.

The output does not depend on `PYTHONHASHSEED`. Exit codes: 0 for a report (findings are not
failures), 1 for a failed consistency check, 2 when an input is missing or the Lean half fails.
The acceptance tests and the first report are recorded in `notes/Prose-laman-cleanup.md` (task 2)
and `notes/Prose-findings.md`.
"""
import argparse
import collections
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILE = "scripts/BlueprintDeps.lean"
CACHE_DIR = ROOT / ".lake" / "blueprint-deps"
HTML = ROOT / "blueprint" / "web" / "dep_graph_document.html"
LEAN_DECLS = ROOT / "blueprint" / "lean_decls"
YAML = ROOT / "formalization.yaml"
# plastexdepgraph's DEFAULT_TYPES; `web.tex` loads the blueprint package without `thms=`.
NODE_ENVS = ("definition", "lemma", "proposition", "theorem", "corollary")
# The git paths whose objects key the Lean cache.
LEAN_INPUTS = ("CombinatorialRigidity", "CombinatorialRigidity.lean", "lakefile.toml",
               "lake-manifest.json", "lean-toolchain", LEAN_FILE)
# plasTeX makes each sectioning unit a container, and a proof looks for its statement only
# inside its own container.
TOKEN = re.compile(r"\\input\{([^}]*)\}|\\begin\{([A-Za-z*]+)\}|\\(?:part|chapter|section|"
                   r"subsection|subsubsection|paragraph|subparagraph)\*?(?![A-Za-z])")
LEANOK = re.compile(r"\\leanok(?![A-Za-z])")


def die(msg, code=2):
    print(f"blueprint-deps: {msg}", file=sys.stderr)
    sys.exit(code)


def args_of(cmd, body):
    """The comma-separated arguments of every `\\cmd{…}` in `body`, in order."""
    out = []
    for m in re.finditer(r"\\" + cmd + r"(?![A-Za-z])\s*\{([^}]*)\}", body):
        out += [a.strip() for a in m.group(1).split(",") if a.strip()]
    return out


# ---------------------------------------------------------------------------------------------
# The TeX


def strip_comments(text):
    return re.sub(r"(?<!\\)%.*", "", text)


def parse_tex(tex_root):
    """Return (envs, notes): every theorem-like environment in document order, and parse notes."""
    common = (tex_root / "preamble" / "common.tex").read_text()
    thm_envs = set(re.findall(r"\\newtheorem\{(\w+)\}", strip_comments(common)))
    if not set(NODE_ENVS) <= thm_envs:
        die(f"{tex_root}/preamble/common.tex does not declare every node environment")
    envs, notes = [], []
    state = {"last": None}

    def scan(rel):
        path = tex_root / rel
        if not path.exists():
            die(f"\\input{{{rel}}}: {path} does not exist")
        text = strip_comments(path.read_text())
        line = lambda pos: text.count("\n", 0, pos) + 1  # noqa: E731
        pos = 0
        while True:
            m = TOKEN.search(text, pos)
            if not m:
                return
            if m.group(1) is not None:
                inc = m.group(1).strip()
                scan(inc if inc.endswith(".tex") else inc + ".tex")
                pos = m.end()
            elif m.group(2) is not None:
                env = m.group(2)
                if env not in thm_envs and env != "proof":
                    pos = m.end()
                    continue
                end = text.find("\\end{" + env + "}", m.end())
                if end < 0:
                    die(f"{rel}:{line(m.start())}: \\begin{{{env}}} is never closed")
                body = text[m.end():end]
                pos = end
                if env == "proof":
                    owner = state["last"]
                    uses = args_of("uses", body)
                    if owner is None or owner["env"] not in NODE_ENVS:
                        if uses:
                            what = "nothing" if owner is None else f"a {owner['env']}"
                            notes.append(f"{rel}:{line(m.start())}: a proof with \\uses attaches "
                                         f"to {what}; its edges are not in the graph")
                        continue
                    if owner["has_proof"]:
                        notes.append(f"{rel}:{line(m.start())}: a second proof for "
                                     f"{owner['label']}; plastexdepgraph keeps one")
                    owner.update(has_proof=True, proof_uses=uses,
                                 proof_leanok=bool(LEANOK.search(body)))
                    continue
                labels = args_of("label", body)
                rec = {"env": env, "label": labels[0] if labels else None, "file": rel,
                       "chapter": Path(rel).stem, "line": line(m.start()),
                       "pins": args_of("lean", body), "stmt_uses": args_of("uses", body),
                       "stmt_leanok": bool(LEANOK.search(body)), "has_proof": False,
                       "proof_uses": [], "proof_leanok": False}
                if len(labels) > 1 and env in NODE_ENVS:
                    notes.append(f"{rel}:{rec['line']}: {len(labels)} labels; the first, "
                                 f"{labels[0]}, is taken as the node's")
                state["last"] = rec
                envs.append(rec)
            else:  # a sectioning command closes the container a proof looks back through
                state["last"] = None
                pos = m.end()

    scan("chapter/main.tex")
    return envs, notes


def main_results():
    text = YAML.read_text()
    block = text[text.index("main_results:"):]
    block = block[:re.search(r"\n\S", block).start()]  # up to the next top-level key
    return re.findall(r'^\s*- declaration:\s*"([^"]+)"', block, re.M)


# ---------------------------------------------------------------------------------------------
# The built graph, parsed as the invariance check parses it


def gate3_statements():
    """The invariance check's sorted statement list, verbatim (`CLEANUP.md` §A)."""
    g = open(HTML).read()
    g = g[g.find('digraph'):]
    g = g[g.find('{') + 1:g.find('}')]
    return sorted(filter(None, (re.sub(r'\s+', ' ', x).strip() for x in g.split(';'))))


def gate3_line(s):
    return (f"{sum(' -> ' in x for x in s)} edges "
            f"{hashlib.sha256(chr(10).join(s).encode()).hexdigest()[:16]}")


def lean_decls_hash():
    r = subprocess.run("sort blueprint/lean_decls | shasum -a 256 | cut -c1-16", shell=True,
                       cwd=ROOT, capture_output=True, text=True, check=True)
    return r.stdout.strip()


def graph_edges(s):
    out = set()
    for x in s:
        m = re.match(r'"([^"]+)" -> "([^"]+)"', x)
        if m:
            out.add((m.group(1), m.group(2)))
    return out


# ---------------------------------------------------------------------------------------------
# The `\uses` graph


def ancestors_map(nodes, uses):
    """label -> every node reachable by following `\\uses` (its ancestors in the drawn graph)."""
    memo, active, cycles = {}, set(), []

    def anc(x):
        if x in memo:
            return memo[x]
        if x in active:
            cycles.append(x)
            return set()
        active.add(x)
        out = set()
        for u in uses[x]:
            out.add(u)
            out |= anc(u)
        active.discard(x)
        memo[x] = out
        return out

    for x in nodes:
        anc(x)
    return memo, cycles


def transitive_reduction(edges, anc):
    """Drop (dep, user) when dep is an ancestor of another direct dependency of user."""
    deps = collections.defaultdict(set)
    for d, u in edges:
        deps[u].add(d)
    return {(d, u) for d, u in edges if not any(d in anc[c] for c in deps[u] if c != d)}


# ---------------------------------------------------------------------------------------------
# The Lean half


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout


def lean_key(pin_text):
    """A digest of everything the Lean half's output depends on: the pins, the committed objects
    of `LEAN_INPUTS`, and any uncommitted change to them (the diff, and untracked files)."""
    h = hashlib.sha256(pin_text.encode())
    for p in LEAN_INPUTS:
        h.update(f"{p} {git('rev-parse', '--verify', '--quiet', f'HEAD:{p}').strip()}\n".encode())
    h.update(git("diff", "HEAD", "--", *LEAN_INPUTS).encode())
    for f in sorted(git("ls-files", "--others", "--exclude-standard", "--",
                        *LEAN_INPUTS).split()):
        h.update(f.encode() + hashlib.sha256((ROOT / f).read_bytes()).digest())
    return h.hexdigest()[:16]


def run_lean(pins, use_cache):
    pin_text = "".join(p + "\n" for p in sorted(set(pins)))
    cache = CACHE_DIR / f"{lean_key(pin_text)}.jsonl"
    if use_cache and cache.exists():
        return cache.read_text().splitlines(), f"the cache {cache.relative_to(ROOT)}"
    with tempfile.TemporaryDirectory() as d:
        pins_path, out_path = Path(d) / "pins.txt", Path(d) / "lean.jsonl"
        pins_path.write_text(pin_text)
        env = dict(os.environ, BLUEPRINT_DEPS_PINS=str(pins_path),
                   BLUEPRINT_DEPS_OUT=str(out_path))
        r = subprocess.run(["lake", "lean", LEAN_FILE], cwd=ROOT, env=env, capture_output=True,
                           text=True)
        log = r.stdout + r.stderr
        if r.returncode != 0 or not out_path.exists():
            die(f"`lake lean {LEAN_FILE}` failed (exit {r.returncode}):\n" + log[-4000:])
        own = [ln for ln in log.splitlines() if LEAN_FILE in ln]
        if own:
            print("blueprint-deps: the Lean half reported:\n  " + "\n  ".join(own),
                  file=sys.stderr)
        lines = out_path.read_text().splitlines()
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cache.write_text("\n".join(lines) + "\n")
    return lines, f"a fresh `lake lean` run, cached in {cache.relative_to(ROOT)}"


class Lean:
    def __init__(self, lines):
        self.header = json.loads(lines[0])
        self.t, self.v, self.kind, self.module, self.missing = {}, {}, {}, {}, []
        for ln in lines[1:]:
            r = json.loads(ln)
            if "missing" in r:
                self.missing.append(r["missing"])
                continue
            self.t[r["n"]], self.v[r["n"]] = r["t"], r["v"]
            self.kind[r["n"]], self.module[r["n"]] = r["k"], r["m"]

    def reach(self, start, pinned, skip):
        """BFS from `start` through unpinned constants: (the pins met, in BFS order; the parent
        map, from which `chain` rebuilds a path)."""
        parent, found, queue = {}, [], []
        for c in start:
            if c not in parent:
                parent[c] = None
                queue.append(c)
        i = 0
        while i < len(queue):
            c = queue[i]
            i += 1
            if c in pinned:
                if c not in skip:
                    found.append(c)
                continue
            for n in self.t.get(c, ()) + self.v.get(c, ()):
                if n not in parent:
                    parent[n] = c
                    queue.append(n)
        return found, parent

    def closure(self, start):
        seen, stack = set(start), list(start)
        while stack:
            c = stack.pop()
            for n in self.t.get(c, ()) + self.v.get(c, ()):
                if n not in seen:
                    seen.add(n)
                    stack.append(n)
        return seen


def pretty(name):
    m = re.match(r"_private\.(?:[^.]+\.)*?0\.(.*)$", name)
    return f"{m.group(1)} (private)" if m else name


def chain(parent, start_pin, target):
    path = [target]
    while parent.get(path[-1]) is not None:
        path.append(parent[path[-1]])
    return " -> ".join([start_pin] + [pretty(c) for c in reversed(path)])


# ---------------------------------------------------------------------------------------------
# The analysis


def analyse(nodes, lean, mains):
    labels_of = collections.defaultdict(list)
    for x, n in nodes.items():
        for p in n["pins"]:
            if x not in labels_of[p]:
                labels_of[p].append(x)
    pinned = set(labels_of)
    uses = {x: [u for u in n["stmt_uses"] + n["proof_uses"] if u in nodes]
            for x, n in nodes.items()}
    anc, cycles = ancestors_map(nodes, uses)

    # pin level: direct reach through the type and through the value
    direct = {}
    for p in pinned:
        t, tpar = lean.reach(lean.t.get(p, []), pinned, {p})
        v, vpar = lean.reach(lean.v.get(p, []), pinned, {p})
        direct[p] = {"type": t, "value": v, "tpar": tpar, "vpar": vpar}
    trans = {}
    for p in pinned:
        seen, stack = set(), [p]
        while stack:
            q = stack.pop()
            for r in direct[q]["type"] + direct[q]["value"]:
                if r not in seen:
                    seen.add(r)
                    stack.append(r)
        trans[p] = seen

    live = lean.closure([m for m in mains if m in lean.t])
    out = {}
    for x, n in nodes.items():
        own = set(n["pins"])
        reached = {}  # target label -> (via, from pin, to pin); statement wins over proof
        for p in n["pins"]:
            for via in ("type", "value"):
                for q in direct[p][via]:
                    if q in own:
                        continue
                    for y in labels_of[q]:
                        if y != x and (y not in reached or (via == "type" and
                                                            reached[y][0] == "value")):
                            reached[y] = (via, p, q)
        trans_labels = {y for p in n["pins"] for q in trans[p] if q not in own
                        for y in labels_of[q]} - {x}
        used = set(uses[x])
        missing, implied = {}, {}
        for y, info in sorted(reached.items()):
            group = set(labels_of[info[2]]) - {x}
            if group & used:
                continue  # for a pin on several nodes, one used node backs them all
            (implied if group & anc[x] else missing)[y] = info
        unbacked = {}
        if n["pins"]:
            for y in uses[x]:
                if y not in reached:
                    unbacked[y] = "transitive" if y in trans_labels else "no Lean basis"
        out[x] = {"reached": reached, "missing": missing, "implied": implied,
                  "unbacked": unbacked, "dead": [p for p in n["pins"] if p not in live],
                  "cycle": sorted(y for y in missing if x in anc[y])}
    return {"nodes": out, "direct": direct, "labels_of": labels_of, "uses": uses, "anc": anc,
            "cycles": cycles, "live": live}


# ---------------------------------------------------------------------------------------------
# Output


def summary(nodes, order, res, chapters):
    rows = collections.OrderedDict()
    for x in order:
        n, r = nodes[x], res["nodes"][x]
        c = rows.setdefault(n["chapter"], collections.Counter())
        c["nodes"] += 1
        c["pinned"] += bool(n["pins"])
        c["pins"] += len(n["pins"])
        c["4+"] += len(n["pins"]) >= 4
        c["missing"] += len(r["missing"])
        c["implied"] += len(r["implied"])
        c["unb-trans"] += sum(v == "transitive" for v in r["unbacked"].values())
        c["unb-none"] += sum(v == "no Lean basis" for v in r["unbacked"].values())
        c["unchecked"] += 0 if n["pins"] else len(res["uses"][x])
        c["dead"] += len(r["dead"])
    cols = ["nodes", "pinned", "pins", "4+", "missing", "implied", "unb-trans", "unb-none",
            "unchecked", "dead"]
    print("| chapter | " + " | ".join(cols) + " |")
    print("|---" * (len(cols) + 1) + "|")
    total = collections.Counter()
    for ch, c in rows.items():
        if chapters and ch not in chapters:
            continue
        total.update(c)
        print(f"| `{ch}` | " + " | ".join(str(c[k]) for k in cols) + " |")
    print("| **total** | " + " | ".join(str(total[k]) for k in cols) + " |")


def print_node(x, n, r, res, lean, full):
    print(f"{x}  ({n['file']}:{n['line']}, {n['env']}; {len(n['pins'])} pin"
          f"{'' if len(n['pins']) == 1 else 's'})")
    if full:
        for p in n["pins"]:
            print(f"  pin       {p}  [{lean.kind.get(p, '?')}, {lean.module.get(p, '?')}]")
        print(f"  uses      statement: {', '.join(n['stmt_uses']) or '-'}")
        print(f"            proof: {', '.join(n['proof_uses']) or '-'}")
    if not n["stmt_leanok"]:
        print("  no \\leanok (the graph draws the node unfilled)")
    if not n["pins"]:
        print(f"  unchecked {len(res['uses'][x])} \\uses (no pin)")
        return
    for kind in ("missing", "implied"):
        for y, (via, p, q) in sorted(r[kind].items()):
            tag = "statement" if via == "type" else "proof"
            cyc = "  (would close a cycle)" if y in r["cycle"] else ""
            print(f"  {kind:9} {y}  {tag}: {p} -> {q}{cyc}")
            if full:
                par = res["direct"][p]["tpar" if via == "type" else "vpar"]
                print(f"            chain: {chain(par, p, q)}")
    for y, why in sorted(r["unbacked"].items()):
        print(f"  unbacked  {y}  ({why})")
    for p in r["dead"]:
        print(f"  dead pin  {p}  (outside every main result's closure)")
    if full:
        for y, (via, p, q) in sorted(r["reached"].items()):
            tag = "statement" if via == "type" else "proof"
            print(f"  reaches   {y}  {tag}: {p} -> {q}")
            par = res["direct"][p]["tpar" if via == "type" else "vpar"]
            print(f"            chain: {chain(par, p, q)}")
        for z, rz in sorted(res["nodes"].items()):
            if x in rz["reached"]:
                print(f"  reached by {z}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--label", action="append", default=[])
    ap.add_argument("--chapter", action="append", default=[])
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--dump", action="store_true")
    ap.add_argument("--tex-root", default=str(ROOT / "blueprint" / "src"))
    ap.add_argument("--no-cache", action="store_true")
    a = ap.parse_args()
    tex_root = Path(a.tex_root).resolve()
    default_root = tex_root == (ROOT / "blueprint" / "src").resolve()

    envs, notes = parse_tex(tex_root)
    nodes = collections.OrderedDict()
    for e in envs:
        if e["env"] not in NODE_ENVS:
            if e["pins"]:
                notes.append(f"{e['file']}:{e['line']}: the {e['env']} {e['label']} pins "
                             f"{', '.join(e['pins'])}; it is not a node, so the reach "
                             f"follows through it")
            continue
        if e["label"] is None:
            notes.append(f"{e['file']}:{e['line']}: a {e['env']} with no \\label")
            continue
        if e["label"] in nodes:
            die(f"duplicate label {e['label']}")
        nodes[e["label"]] = e
    order = list(nodes)
    for x, n in nodes.items():
        for u in n["stmt_uses"] + n["proof_uses"]:
            if u not in nodes:
                notes.append(f"{n['file']}:{n['line']}: {x} \\uses {u}, which is not a node")

    if a.dump:
        if not HTML.exists():
            die(f"{HTML.relative_to(ROOT)} is missing: run blueprint/verify.sh first")
        s = gate3_statements()
        print(gate3_line(s))
        print(lean_decls_hash() if LEAN_DECLS.exists() else "(no blueprint/lean_decls)")
        print(f"## graph: {len(s)} statements, sorted as the invariance check sorts them")
        print("\n".join(s))
        print("## pins: label -> pins, from the TeX, sorted by label (every node, and every "
              "other labelled environment with a pin)")
        pinned = {e["label"]: e["pins"] for e in envs if e["label"] and e["pins"]}
        for x in sorted(set(nodes) | set(pinned)):
            print(f"{x}: {', '.join(pinned.get(x, []))}")
        print("## uses: label -> \\uses targets, from the TeX, statement and proof apart, each "
              "sorted, sorted by label (every node, and every other labelled environment with a "
              "\\uses; a target that is not a node included)")
        using = {e["label"]: e for e in envs
                 if e["label"] and (e["stmt_uses"] or e["proof_uses"])}
        for x in sorted(set(nodes) | set(using)):
            e = nodes[x] if x in nodes else using[x]
            print(f"{x}: statement {', '.join(sorted(e['stmt_uses'])) or '-'}; "
                  f"proof {', '.join(sorted(e['proof_uses'])) or '-'}")
        return 0

    for x in a.label:
        if x not in nodes:
            die(f"no node labelled {x}")
    chapters = set(a.chapter)
    known = {n["chapter"] for n in nodes.values()}
    for c in chapters:
        if c not in known:
            die(f"no chapter {c}; chapters: {', '.join(sorted(known))}")

    status = 0
    checks = []
    tex_files = list(tex_root.rglob("*.tex"))
    if default_root and HTML.exists() and LEAN_DECLS.exists():
        newest = max(f.stat().st_mtime for f in tex_files)
        if min(HTML.stat().st_mtime, LEAN_DECLS.stat().st_mtime) < newest:
            checks.append("skipped: the built graph or lean_decls is older than the TeX "
                          "(run blueprint/verify.sh)")
        else:
            uses = {x: [u for u in n["stmt_uses"] + n["proof_uses"] if u in nodes]
                    for x, n in nodes.items()}
            anc, cycles = ancestors_map(nodes, uses)
            built = graph_edges(gate3_statements())
            if cycles:
                checks.append(f"FAILED: the \\uses graph has a cycle through {cycles[0]}")
                status = 1
            else:
                mine = transitive_reduction({(u, x) for x in nodes for u in uses[x]}, anc)
                if mine == built:
                    checks.append(f"OK: the TeX's \\uses edges, transitively reduced, are the "
                                  f"built graph's {len(built)} edges")
                else:
                    status = 1
                    checks.append(f"FAILED: the TeX's reduced \\uses edges differ from the built "
                                  f"graph: only in the TeX {sorted(mine - built)[:5]}, only in "
                                  f"the graph {sorted(built - mine)[:5]}")
            mine_pins = sorted(p for e in envs for p in e["pins"])
            decls = sorted(ln for ln in LEAN_DECLS.read_text().splitlines() if ln)
            if mine_pins == decls:
                checks.append(f"OK: the TeX's pins are blueprint/lean_decls ({len(decls)}, "
                              f"nodes and other environments together)")
            else:
                status = 1
                checks.append("FAILED: the TeX's pins differ from blueprint/lean_decls")
    elif default_root:
        checks.append("skipped: blueprint/web or blueprint/lean_decls is missing "
                      "(run blueprint/verify.sh)")
    else:
        checks.append(f"skipped: --tex-root {a.tex_root} is not the built blueprint's")

    mains = main_results()
    pins = [p for n in nodes.values() for p in n["pins"]]
    lines, how = run_lean(pins + mains, not a.no_cache)
    lean = Lean(lines)
    if lean.missing:
        die(f"pins with no Lean constant: {', '.join(lean.missing)}")
    absent = [m for m in mains if m not in lean.t]
    if absent:
        die(f"main results with no Lean constant: {', '.join(absent)}")
    res = analyse(nodes, lean, mains)

    n_pins, n_distinct = len(pins), len(set(pins))
    print(f"blueprint-deps: {len(nodes)} nodes in {len({n['file'] for n in nodes.values()})} "
          f"files, {n_pins} pins ({n_distinct} distinct); {lean.header['constants']} Lean "
          f"constants from {how}; {len(mains)} main results")
    for c in checks:
        print(f"consistency: {c}")
    for c in res["cycles"][:1]:
        print(f"the \\uses graph has a cycle through {c}")
    for note in notes:
        print(f"parse note: {note}")

    if a.label or a.chapter:
        sel = [x for x in order if x in a.label or nodes[x]["chapter"] in chapters]
        if chapters:
            print()
            summary(nodes, order, res, chapters)
        for x in sel:
            print()
            print_node(x, nodes[x], res["nodes"][x], res, lean, full=bool(a.label))
        return status

    print()
    print("## Summary per chapter")
    print()
    summary(nodes, order, res, set())
    if a.summary:
        return status
    print()
    print("## (1) Edges: nodes with a missing, implied or unbacked edge, unchecked, or drawn "
          "unfilled")
    for x in order:
        r = res["nodes"][x]
        if (r["missing"] or r["implied"] or r["unbacked"] or not nodes[x]["pins"]
                or not nodes[x]["stmt_leanok"]):
            print()
            print_node(x, nodes[x], dict(r, dead=[]), res, lean, full=False)
    print()
    print("## (2) Pins outside the closure of every main result")
    print()
    for x in order:
        dead = res["nodes"][x]["dead"]
        if dead:
            whole = " (every pin)" if len(dead) == len(nodes[x]["pins"]) else ""
            print(f"{x}{whole}: {', '.join(dead)}")
    print()
    print("## (3) Pins per node: four or more")
    print()
    for x in sorted(order, key=lambda y: (-len(nodes[y]["pins"]), order.index(y))):
        if len(nodes[x]["pins"]) >= 4:
            print(f"{x} ({nodes[x]['chapter']}): {len(nodes[x]['pins'])} pins")
    return status


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:  # `| head`
        sys.exit(0)
