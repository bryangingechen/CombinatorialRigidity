#!/usr/bin/env python3
"""Check the blueprint labels that the Lean doc comments name.

Written for RECONCILE round 3, task 2 (`notes/Reconcile-lean-cleanup.md` *Lemma checklist*; the
check `notes/Prose-report.md` §2.1 proposes for L10–L11). The project's docstrings name the
blueprint node they serve, and nothing else checks the name: each move of a pin left docstrings
naming a node the pin had left, or a label the blueprint lacks (the ledger's `F-230`–`F-264`).
Usage, from anywhere (paths resolve against the repository root):

    python3 scripts/check-docstring-labels.py              # the findings, then the counts
    python3 scripts/check-docstring-labels.py --counts     # the counts by directory only
    python3 scripts/check-docstring-labels.py --lean       # also check the name resolution
    python3 scripts/check-docstring-labels.py --self-test  # the acceptance tests

`--tex-root DIR` reads the chapters from `DIR` (a scratch copy of `blueprint/src`) and
`--lean-root DIR` the Lean from `DIR` (a scratch copy of the repository's Lean), so a planted case
can be run on a copy of the real tree.

**Inputs.** From the TeX, read by `scripts/blueprint-deps.py`'s parser (`\\input` followed from
`chapter/main.tex`, TeX comments stripped): every `\\label` (a sectioning label or an
environment's, any kind), and each theorem-like environment's label, kind and `\\lean{…}` pins. A
*node* is a `definition`, `lemma`, `theorem`, `corollary` or `proposition` (plastexdepgraph's
node types). From the Lean: every `.lean` file under `CombinatorialRigidity/`, with
`CombinatorialRigidity.lean` and `Main.lean`; in each, every doc comment (`/-- … -/`, and the
module and section docstrings `/-! … -/`), Lean's nesting of block comments respected, and line
comments, plain block comments and string literals skipped. A `/-- … -/` followed (past
attributes and modifiers) by a declaration keyword is that declaration's docstring; its full
name is read from the `namespace` … `end` blocks around it (`section` and `mutual` blocks
counted, a `_root_.` name taken as written). `--lean` checks the resolution: every name read so,
outside `Main.lean` (not a library module), must be a constant of the Lean environment, read from
`scripts/blueprint-deps.py`'s Lean cache (a fresh `lake lean` run if the cache is stale). Any
other `/-- … -/` (a structure field's or a constructor's) is checked for labels only.

**A label** is a token `<prefix>:<name>` with a prefix the blueprint uses (`def`, `lem`, `thm`,
`cor`, `prop`, `rem`, `fmlnote`, `ex`, `sec`, `ssec`, `chap`) and a name of letters, digits and
inner hyphens (the blueprint's labels are all of that form), backticked or not, with no letter,
digit or underscore just before it. A docstring's whitespace is collapsed first. A label broken
across two lines then reads `lem:x- y`: when `lem:x-y` is a blueprint label and `lem:x` is not, it
is reported as broken (no `grep` finds it) and read as `lem:x-y` below; otherwise `lem:x` is read.

**The lead** of a docstring is its text up to its first sentence end: a `.` or `:` followed by
whitespace (or the docstring's end), outside backticks and parentheses. The project's docstrings
open with a bold title and a parenthetical, as in `**Title** (<label>, KT Lemma 5.4): <body>`, so
the lead holds the title, the parenthetical and any label in either. The lead parenthetical's
*first item* is its text up to its first `,`, `;`, ` — ` or ` / ` outside backticks and inner
parentheses; it is *bare* when it is a single label, backticked or not.

**What the docstring gives as its own node** depends on whether the blueprint pins the
declaration (some environment, a node or not, lists its full name in `\\lean{…}`):

- A **pinned** declaration: every node label in its lead. The project writes a pin's own node
  there, so a lead that names nodes, none of which pins it, names a node the pin left or never
  had (a pin moved to a finer node keeps naming the coarser one: `F-233`, `F-235`, `F-244`).
- An **unpinned** declaration: the lead parenthetical's first item, when it is bare and its kind
  matches the declaration's (`def:` for a `def`, `abbrev`, `structure`, `class`, `inductive`,
  `instance`, `opaque` or `axiom`; `lem:`, `thm:`, `cor:` or `prop:` for a `theorem` or
  `lemma`). A bare label of the matching kind, first, reads as the node's Lean, which is what an
  unpinned declaration's docstring still says when its pin moved off it (`F-238`, `F-256`,
  `F-258`, `F-264`). A theorem that names the definition it concerns cites the concept, and a
  label after the first item, or qualified within it (`a step of <label>`, `<label>'s second
  step`, `<label> infra`), names the node a helper serves: neither is its own node. So a helper
  whose first item is a bare label is reported as well; its fix is to say, in that item, how it
  serves the node.

**Findings**, each a line `<file>:<line>: …`:

1. *missing*: a label, in any doc comment, that no `\\label` of the blueprint carries, or one broken
   across a line;
2. *pinned, another node*: a pinned declaration whose lead names nodes, none of which pins it
   (the labels that pin it listed);
3. *unpinned, own node*: an unpinned declaration whose lead gives a node as its own (the node's
   pins listed).

A label the blueprint lacks is the first kind only. Counts are by the Lean file's directory; the
round's gate is the total, which a commit must not raise. Labels in line comments and plain block
comments are not read. The output does not depend on `PYTHONHASHSEED`, and a run takes about a
second. Exit codes: 0 for a report (findings are not failures), 1 for a failed `--self-test` or
`--lean` check, 2 when an input is missing. The acceptance tests (`--self-test`'s planted cases,
each kind and each parsing edge; and four planted on a copy of the tree) and the first report are
recorded in `notes/Reconcile-lean-cleanup.md` (task 2).
"""
import argparse
import collections
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PREFIXES = ("def", "lem", "thm", "cor", "prop", "rem", "fmlnote", "ex", "sec", "ssec", "chap")
LABEL = re.compile(r"(?<![A-Za-z0-9_])(?:" + "|".join(PREFIXES) +
                   r"):[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?")
NODE_PREFIX_KIND = {"def": "def", "lem": "thm", "thm": "thm", "cor": "thm", "prop": "thm"}
DECL_KIND = {"theorem": "thm", "lemma": "thm", "def": "def", "abbrev": "def",
             "structure": "def", "class": "def", "inductive": "def", "instance": "def",
             "opaque": "def", "axiom": "def"}
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "public",
             "scoped", "local", "meta")
DECL = re.compile(
    r"\s*(?:@\[(?:[^\[\]]|\[[^\[\]]*\])*\]\s*)*"
    r"((?:(?:" + "|".join(MODIFIERS) + r")\s+)*)"
    r"(theorem|lemma|def|abbrev|instance|structure|class\s+inductive|class|inductive|opaque|"
    r"axiom|example|alias)\b\s*(?:\(priority\s*:=[^)]*\)\s*)?([^\s:({\[⦃]*)")
SCOPE = re.compile(r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:public|private|noncomputable|meta)"
                   r"[ \t]+)*(namespace|section|end|mutual)\b[ \t]*(\S*)")
CHAR = re.compile(r"'(?:\\[^']*|[^\\'\n])'")


def load_blueprint_deps():
    spec = importlib.util.spec_from_file_location("blueprint_deps",
                                                  ROOT / "scripts" / "blueprint-deps.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------------------------
# The TeX


class Blueprint:
    """The labels, the node labels, and the pins, from a TeX root."""

    def __init__(self, labels, envs, node_envs):
        self.labels = set(labels)
        self.node = {e["label"] for e in envs if e["label"] and e["env"] in node_envs}
        self.pins = collections.defaultdict(list)       # label -> its pins
        self.pinned_by = collections.defaultdict(set)   # declaration -> the labels pinning it
        for e in envs:
            if e["label"]:
                self.pins[e["label"]] += e["pins"]
                for p in e["pins"]:
                    self.pinned_by[p].add(e["label"])


def read_blueprint(tex_root, bd):
    envs, _ = bd.parse_tex(tex_root)
    labels, seen = [], set()

    def scan(rel):
        if rel in seen:
            return
        seen.add(rel)
        path = tex_root / rel
        if not path.exists():
            bd.die(f"\\input{{{rel}}}: {path} does not exist")
        text = bd.strip_comments(path.read_text())
        labels.extend(bd.args_of("label", text))
        for inc in re.findall(r"\\input\{([^}]*)\}", text):
            inc = inc.strip()
            scan(inc if inc.endswith(".tex") else inc + ".tex")

    scan("chapter/main.tex")
    return Blueprint(labels, envs, bd.NODE_ENVS)


# ---------------------------------------------------------------------------------------------
# The Lean


def scan_lean(text):
    """`text` with every comment and string literal blanked (newlines kept), and its doc
    comments as (start, end, kind, body), kind `doc` for `/--` and `mod` for `/-!`."""
    n, out, docs, i = len(text), list(text), [], 0

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif text.startswith("/-", i):
            kind = "doc" if text.startswith("/--", i) else "mod" if text.startswith("/-!", i) \
                else None
            depth, j = 1, i + 2
            while depth and j < n:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if kind:
                docs.append((i, j, kind, text[i + 3:j - 2]))
            blank(i, j)
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            blank(i, j + 1)
            i = j + 1
        else:
            m = None
            if text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'.!?")):
                m = CHAR.match(text, i)
            if m:
                blank(i, m.end())
                i = m.end()
            else:
                i += 1
    return "".join(out), docs


def read_lean_file(rel, text):
    """Every doc comment of one file: a dict with its line, kind (`doc`/`mod`), the declaration
    keyword (`None` for a module docstring, `other` for a field's or a constructor's), the full
    name (`None` when there is none), and the body with its whitespace collapsed."""
    code, docs = scan_lean(text)
    events = sorted([(m.start(), 0, m.group(1), m.group(2)) for m in SCOPE.finditer(code)] +
                    [(d[0], 1, d, None) for d in docs], key=lambda e: e[0])
    stack, res = [], []
    for pos, what, a, b in events:
        if what == 0:
            if a == "end":
                if stack:
                    stack.pop()
            else:
                stack.append((a, b))
            continue
        start, end, kind, body = a
        keyword = name = None
        if kind == "doc":
            m = DECL.match(code, end)
            if not m:
                keyword = "other"
            else:
                keyword = re.sub(r"\s+", " ", m.group(2))
                raw = m.group(3)
                if raw and keyword not in ("example",):
                    name = raw[len("_root_."):] if raw.startswith("_root_.") else ".".join(
                        [x for k, x in stack if k == "namespace"] + [raw])
        res.append({"file": rel, "line": text.count("\n", 0, start) + 1, "kind": kind,
                    "keyword": keyword, "name": name,
                    "body": re.sub(r"\s+", " ", body).strip()})
    return res


def lean_files(lean_root):
    files = sorted((lean_root / "CombinatorialRigidity").rglob("*.lean"))
    files += [lean_root / f for f in ("CombinatorialRigidity.lean", "Main.lean")
              if (lean_root / f).exists()]
    if not files:
        print(f"check-docstring-labels: no Lean files under {lean_root}", file=sys.stderr)
        sys.exit(2)
    return files


# ---------------------------------------------------------------------------------------------
# The rule


def split_top(s, seps):
    """`s` cut at its first separator outside backticks and parentheses: (head, rest or None)."""
    depth, tick, i = 0, False, 0
    while i < len(s):
        c = s[i]
        if c == "`":
            tick = not tick
        elif not tick and c == "(":
            depth += 1
        elif not tick and c == ")":
            depth -= 1
        elif not tick and depth == 0:
            for sep in seps:
                if s.startswith(sep, i):
                    return s[:i], s[i + len(sep):]
        i += 1
    return s, None


def marks(text):
    """Per character of `text`: (in backticks, in bold, parenthesis depth), the state before the
    character. Bold is `**` outside backticks, ignored when its count is odd (an unclosed `**`)."""
    bold_on = len(re.findall(r"\*\*", re.sub(r"`[^`]*`", "", text))) % 2 == 0
    out, tick, bold, depth, i = [], False, False, 0, 0
    while i < len(text):
        out.append((tick, bold, depth))
        c = text[i]
        if c == "`":
            tick = not tick
        elif not tick and bold_on and text.startswith("**", i):
            bold = not bold
            out.append((tick, not bold, depth))
            i += 1
        elif not tick and c == "(":
            depth += 1
        elif not tick and c == ")":
            depth = max(0, depth - 1)
        i += 1
    return out


def lead_of(body):
    """The docstring's text up to its first sentence end: a `.` or `:` before whitespace or the
    end, outside backticks, bold and parentheses, or a bold title's closing `**` just after a `.`
    or `:` (`**Title.**`)."""
    m = marks(body)
    for i, (tick, bold, depth) in enumerate(m):
        if tick or depth:
            continue
        if (not bold and body[i] in ".:" and (i + 1 == len(body) or body[i + 1] == " ")):
            return body[:i]
        if (bold and body.startswith("**", i) and i + 2 < len(m) and not m[i + 2][1] and
                body[i - 1] in ".:"):
            return body[:i + 2]
    return body


def first_parenthetical(lead):
    """The content of the lead's first parenthetical outside backticks and bold, or None."""
    m = marks(lead)
    for i, (tick, bold, depth) in enumerate(m):
        if lead[i] == "(" and not tick and not bold and depth == 0:
            j = i + 1
            while j < len(lead) and not (lead[j] == ")" and not m[j][0] and m[j][2] == 1):
                j += 1
            return lead[i + 1:j]
    return None


def bare_first_item(lead):
    """The label the lead parenthetical's first item is, when that item is a single label."""
    inner = first_parenthetical(lead)
    if inner is None:
        return None
    head, _ = split_top(inner, (",", ";", " — ", " / "))
    head = head.strip()
    if head.startswith("`") and head.endswith("`") and len(head) > 1:
        head = head[1:-1]
    return head if LABEL.fullmatch(head) else None


def rejoin(body, labels):
    """`body` with each label broken across a line (`lem:x-` + whitespace + `y`, collapsed to one
    space) joined, when the joined form is a blueprint label; and the broken ones, as
    (first part, joined)."""
    broken = []

    def join(m):
        joined = m.group(1) + "-" + m.group(2)
        if m.group(1) in labels or joined not in labels:
            return m.group(0)
        broken.append((m.group(1), joined))
        return joined

    tail = r"([A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)"
    return re.sub("(" + LABEL.pattern + r")- " + tail, join, body), broken


def analyse(docs, bp):
    """The three kinds of finding, each a sorted list of (file, line, text)."""
    missing, other_node, own_node = [], [], []
    for d in docs:
        where = (d["name"] if d["name"] else "a module or section docstring" if d["kind"] == "mod"
                 else "a field's or constructor's docstring" if d["keyword"] == "other"
                 else f"an unnamed `{d['keyword']}`")
        body, broken = rejoin(d["body"], bp.labels)
        for part, joined in sorted(set(broken)):
            missing.append((d["file"], d["line"],
                            f"`{part}` ({where}): `{joined}` broken across a line"))
        for lab in sorted(set(LABEL.findall(body))):
            if lab not in bp.labels:
                missing.append((d["file"], d["line"], f"`{lab}` ({where})"))
        if not d["name"]:
            continue
        lead = lead_of(body)
        mine = bp.pinned_by.get(d["name"], set())
        if mine:
            named = [x for x in dict.fromkeys(LABEL.findall(lead)) if x in bp.node]
            if named and not set(named) & mine:
                q = lambda xs: ", ".join(f"`{x}`" for x in xs)  # noqa: E731
                other_node.append((d["file"], d["line"], f"{d['name']}: the lead names {q(named)}; "
                                   f"it is pinned at {q(sorted(mine))}"))
        else:
            own = bare_first_item(lead)
            if (own and own in bp.node and own.split(":")[0] in NODE_PREFIX_KIND and
                    NODE_PREFIX_KIND[own.split(":")[0]] == DECL_KIND.get(d["keyword"])):
                pins = bp.pins.get(own, [])
                own_node.append((d["file"], d["line"],
                                 f"{d['name']}: the lead gives `{own}` as its node; no node pins "
                                 f"it, and `{own}` pins {', '.join(pins) if pins else 'nothing'}"))
    return sorted(missing), sorted(other_node), sorted(own_node)


KINDS = ("missing", "pinned, another node", "unpinned, own node")


def report(findings, counts_only, out):
    if not counts_only:
        for title, rows in zip(KINDS, findings):
            out.append(f"## {title} ({len(rows)})")
            out += [f"{f}:{ln}: {t}" for f, ln, t in rows]
    by_dir = collections.defaultdict(lambda: [0, 0, 0])
    for k, rows in enumerate(findings):
        for f, _, _ in rows:
            by_dir[str(Path(f).parent)][k] += 1
    out.append("## counts by directory: missing, pinned another node, unpinned own node, total")
    for dr in sorted(by_dir):
        c = by_dir[dr]
        out.append(f"{dr}: {c[0]} {c[1]} {c[2]} {sum(c)}")
    t = [len(r) for r in findings]
    out.append(f"total {sum(t)}: {t[0]} missing, {t[1]} pinned another node, "
               f"{t[2]} unpinned own node")


# ---------------------------------------------------------------------------------------------
# The acceptance tests: planted cases, each a fixture with its expected findings


SELF_TEST_LEAN = r'''
/-! Module header naming `sec:known`, `lem:absent` and `thm:known-b`. -/
namespace A.B
/-- **Pinned, its own node** (`lem:known-a`, KT Lemma 1): body. -/
theorem good : True := trivial
/-- **Pinned, another node** (`lem:known-b`): body names `lem:known-a` after the lead. -/
theorem moved : True := trivial
/-- **Pinned, a definition cited** (`def:known-d`, the concept): body. -/
@[simp] protected theorem cited : True := trivial
/-- **Pinned, a section only** (`sec:known`): body. -/
theorem sec_only : True := trivial
/-- **Pinned, no label**: body. -/
theorem none_named : True := trivial
/-- **Unpinned, bare** (`lem:known-a`; KT Lemma 1). -/
private theorem stale : True := trivial
/-- **Unpinned, qualified** (`lem:known-a` infra, a helper): body. -/
theorem helper1 : True := trivial
/-- **Unpinned, later item** (degree substrate, `lem:known-a`): body. -/
theorem helper2 : True := trivial
/-- **Unpinned, the concept** (`def:known-d`): body. -/
theorem concept : True := trivial
/-- **Unpinned definition, a lemma first** (lem:known-a): body. -/
def serves : Nat := 0
/-- **Unpinned definition, its definition** (`def:known-d`, the term): body. -/
noncomputable def stale_def : Nat := 0
/-- **Unpinned, after the lead**: body (`lem:known-a`). -/
theorem late : True := trivial
/-- **Unpinned, possessive** (`lem:known-a`'s second step): body. -/
theorem possessive : True := trivial
/-- **A label split across lines** (`lem:known-
a`): body. -/
theorem split_label : True := trivial
/-- **Pinned: a colon in the bold title** (`lem:known-b`): body. -/
theorem colon_title : True := trivial
/-- **Unpinned, a title that is a sentence.** Body (`lem:known-a`). -/
theorem title_sentence : True := trivial
end A.B
-- `lem:absent-in-line-comment` is not read
/- `lem:absent-in-plain-comment` is not read /- nested -/ still not -/
def str : String := "/-- `lem:absent-in-string` -/"
namespace C
section S
/-- **Root name** (`lem:known-c`): body. -/
theorem _root_.D.rooted : True := trivial
end S
mutual
/-- **Mutual** (`def:known-d`): body. -/
def m1 : Nat → Nat | 0 => 0 | n + 1 => m2 n
/-- No label. -/
def m2 : Nat → Nat | 0 => 0 | n + 1 => m1 n
end
/-- **After `mutual`'s end** (`lem:known-c`): body. -/
theorem after_mutual : True := trivial
structure T where
  /-- A field naming `lem:absent-field`. -/
  x : Nat
end C
'''

SELF_TEST_PINS = {"lem:known-a": ["A.B.good", "A.B.split_label"], "lem:known-b": ["A.B.other"],
                  "lem:known-c": ["D.rooted", "C.after_mutual"],
                  "def:known-d": ["A.B.moved_def"]}
SELF_TEST_PINNED_EXTRA = {"A.B.moved": "lem:known-e", "A.B.cited": "lem:known-e",
                          "A.B.colon_title": "lem:known-e",
                          "A.B.sec_only": "lem:known-e", "A.B.none_named": "lem:known-e"}
SELF_TEST_EXPECTED = (
    [  # missing
        ("T.lean", 2, "`lem:absent` (a module or section docstring)"),
        ("T.lean", 30, "`lem:known` (A.B.split_label): `lem:known-a` broken across a line"),
        ("T.lean", 55, "`lem:absent-field` (a field's or constructor's docstring)"),
    ],
    [  # pinned, another node
        ("T.lean", 6, "A.B.moved: the lead names `lem:known-b`; it is pinned at `lem:known-e`"),
        ("T.lean", 8, "A.B.cited: the lead names `def:known-d`; it is pinned at `lem:known-e`"),
        ("T.lean", 33, "A.B.colon_title: the lead names `lem:known-b`; it is pinned at "
                       "`lem:known-e`"),
    ],
    [  # unpinned, own node
        ("T.lean", 14, "A.B.stale: the lead gives `lem:known-a` as its node; no node pins it, "
                       "and `lem:known-a` pins A.B.good, A.B.split_label"),
        ("T.lean", 24, "A.B.stale_def: the lead gives `def:known-d` as its node; no node pins it, "
                       "and `def:known-d` pins A.B.moved_def"),
        ("T.lean", 47, "C.m1: the lead gives `def:known-d` as its node; no node pins it, and "
                       "`def:known-d` pins A.B.moved_def"),
    ],
)
SELF_TEST_NAMES = ["A.B.good", "A.B.moved", "A.B.cited", "A.B.sec_only", "A.B.none_named",
                   "A.B.stale", "A.B.helper1", "A.B.helper2", "A.B.concept", "A.B.serves",
                   "A.B.stale_def", "A.B.late", "A.B.possessive", "A.B.split_label",
                   "A.B.colon_title", "A.B.title_sentence", "D.rooted", "C.m1", "C.m2",
                   "C.after_mutual"]


def self_test():
    docs = read_lean_file("T.lean", SELF_TEST_LEAN)
    ok = True
    names = [d["name"] for d in docs if d["name"]]
    if names != SELF_TEST_NAMES:
        print(f"FAIL names: {names}")
        ok = False
    envs = [{"label": x, "env": "lemma" if x.startswith("lem:") else "definition", "pins": p}
            for x, p in SELF_TEST_PINS.items()]
    envs += [{"label": "lem:known-e", "env": "lemma", "pins": list(SELF_TEST_PINNED_EXTRA)}]
    labels = [e["label"] for e in envs] + ["sec:known", "thm:known-b"]
    bp = Blueprint(labels, envs, ("definition", "lemma"))
    got = analyse(docs, bp)
    for title, g, w in zip(KINDS, got, SELF_TEST_EXPECTED):
        if g != w:
            ok = False
            print(f"FAIL {title}:\n  got      {g}\n  expected {w}")
    print("self-test: " + ("all planted cases as expected" if ok else "FAILED"))
    return 0 if ok else 1


# ---------------------------------------------------------------------------------------------


def check_names(docs, bd, bp_pins_tex_root):
    """`--lean`: every resolved name outside `Main.lean` is a Lean constant."""
    envs, _ = bd.parse_tex(bp_pins_tex_root)
    nodes = [e for e in envs if e["env"] in bd.NODE_ENVS and e["label"]]
    pins = [p for e in nodes for p in e["pins"]]
    lines, how = bd.run_lean(pins + bd.main_results(), True)
    consts, private = set(), set()
    for ln in lines[1:]:
        r = json.loads(ln)
        if "n" in r:
            consts.add(r["n"])
            m = re.match(r"_private\.(?:[^.]+\.)*?0\.(.*)$", r["n"])
            if m:
                private.add(m.group(1))
    named = [d for d in docs if d["name"] and d["file"] != "Main.lean"]
    bad = [d for d in named if d["name"] not in consts and d["name"] not in private]
    print(f"--lean: {len(named)} declaration names read outside Main.lean, {len(bad)} not a "
          f"constant of the environment ({how})")
    for d in bad:
        print(f"  {d['file']}:{d['line']}: {d['name']}")
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--counts", action="store_true")
    ap.add_argument("--lean", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--tex-root", default=str(ROOT / "blueprint" / "src"))
    ap.add_argument("--lean-root", default=str(ROOT))
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    bd = load_blueprint_deps()
    tex_root, lean_root = Path(a.tex_root).resolve(), Path(a.lean_root).resolve()
    bp = read_blueprint(tex_root, bd)
    docs = []
    for f in lean_files(lean_root):
        docs += read_lean_file(str(f.relative_to(lean_root)), f.read_text())
    out = []
    report(analyse(docs, bp), a.counts, out)
    print("\n".join(out))
    if a.lean:
        return check_names(docs, bd, tex_root)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:  # `| head`
        sys.exit(0)
