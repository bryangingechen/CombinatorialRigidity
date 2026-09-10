#!/usr/bin/env python3
"""Claim ledger for the PENCIL corpus: what every label-clause CLAIMS about
its own evidence, queryable in one call instead of a grep/sed hunt.

Why this exists -- a RETRIEVAL problem, measured. A research direction opening
a dispatch has to know what is already proved. Today it finds out by grepping
the 41 000-line workbook for a label, `sed`-ing the surrounding lines, and
repeating: one traced dispatch (direction BNONUNI, 2026-09-09) spent ~35 such
probes recovering ~18 prior `(BE-.)` statements. Those probes read only ~11k
tokens of CONTENT but grew the agent's context by ~137k, because each probe
carries its own reasoning turn. Across eleven sampled dispatches the median
agent wrote its first line at ~210k tokens, from a 36k start.

So the cost is TURNS, not bytes, and the fix is not "read less" -- it is
"answer it in one call". That is this script.

  --label '(BE-216)'      every clause of one label, full text, with its
                          section, step, status and citations
  --status PROVED         every claim at a status (--section / --file narrow)
  --frontier              claims not yet closed whose every citation IS closed
                          -- the cheapest live leaves
  --cited-by '(BE-216)'   what breaks if this claim falls
  --brief L1 L2 ...       a briefing-packet block for a label set, statements
                          quoted verbatim so a dispatch spec never retypes one
  --delta <ref>           status change-set against a git ref, for pasting
                          into a landing's commit message
  --lint                  GATE: the status vocabulary, on claims this commit
                          adds or changes (--all for the corpus, --strict to
                          also fail a new claim left untagged)
  --list / --stats        per-file counts; the tag-vocabulary census
  --selftest              parser audit (coverage, unattached sub-items)

NOT CHECKED IN, BY DESIGN. The ledger is regenerated into a gitignored cache
(`notes/.ledger-cache/`) whenever a source file is newer than the cache;
generation over the whole 2.8 MB workbook measures ~0.2 s. Three reasons, in
order of weight, recorded in `notes/Harness-structure.md` slice 8:

  1. A stored ledger would be one more SUMMARY SURFACE, and this corpus's
     documented pathology is a summary disagreeing with the body prose it
     summarizes (dispatch-log F12; BDECOR, where a proviso dropped on six
     summary surfaces while the body prose stayed correct, so no gate could
     fire). A ledger regenerated from the prose cannot drift from it.
  2. It matches the project's own precedent: no derived artifact is checked
     in -- `notes/scripts/README.md` records a driver command and its runtime,
     and the FIGURE lives in workbook prose.
  3. Storage, the smallest reason: ~190 KiB/month packed at the measured 107
     workbook landings per month.

There is deliberately NO `--verify`: a cache regenerated whenever its source
is newer cannot disagree with the source, so there is nothing to verify.

NO LINE COLUMN -- this was measured and it is the schema's one real trap. A
stored line number shifts for every row below any mid-file edit: regenerating
at HEAD and twenty workbook landings back, a schema WITH line numbers churns
165% of its rows (the whole file rewritten each landing) against 36% without,
and 35 of those 36 points are genuinely new rows. Locations are resolved at
QUERY time instead -- `locate()` greps the opener's exact string -- so output
carries a live, always-correct line number that no artifact keeps in sync.

CLAIM IDENTITY, which `--delta` depends on and which is subtler than it
looks. A claim is (file, section-key, label, clause), where the section KEY is
the gap token plus the direction code -- `§(K-bare-ext)/BEFOURP` -- and never
the heading text. Section headings are themselves status surfaces that get
rewritten in place as directions land (`§(K-dom)`'s grew a whole clause when
DSAT landed), and 37 sections share the `§(K-bare-ext)` prefix, told apart
only by their direction. Keying on heading text reported 500+ phantom
add/removes; keying without the section at all collapsed the 20 labels that
are claimed in more than one section and invented three status transitions on
claims that never moved. `--delta` further classifies a claim that leaves one
section and reappears in another as RELOCATED rather than removed -- direction
RESGRID's six `(RS-.)` claims moved with their section, and a naive diff
reported six deletions and no arrivals.

WHAT THIS IS NOT. An index, exactly as `notes/Pencil-labels.md` says of
itself: the owning section stays authoritative for what a claim MEANS.
Regeneration guarantees the ledger matches the prose. It guarantees nothing
about whether the prose is right -- a `PROVED` here is a claim by whoever
wrote that clause, never a check of it. Read the section before building on a
row.

PARSING, and the three shapes that would break a naive reader.

  1. A label opener is `> **(LABEL)(clause)**` with the bold closing
     IMMEDIATELY after the label -- that is what separates an opener from
     ordinary bolded prose like `> **(CH-1)'s girth >= 4 excludes**`, of
     which the workbook has 158. Requiring the close cuts 1 177 candidate
     lines to 942 real openers.
  2. Bare `(i)` / `(ii)` / `(c)` / `(a2)` openers are SUB-CLAUSES of the most
     recent labelled opener, not labels of their own (96 occurrences). They
     inherit the enclosing label; a parser that treats them as labels invents
     an `ii` family.
  3. 41% of tag parentheticals do NOT close on their opening line. The tag is
     read by a balanced-paren scan across the joined clause block, with
     inline code spans masked first, or it is truncated -- which is how an
     earlier prototype mis-read 378 of 921 tags.

STATUS is taken from the LEADING TOKEN of the tag only, and nothing else.
`*(proven; and enumerated ...)*` is PROVED; `*(two NEGATIVE CONTROLS, both
asserted)*` is UNTAGGED, because `two` is not a status word and a claim's
status is not to be guessed from a word appearing somewhere inside its
editorial gloss. UNTAGGED is a first-class status, not a parse failure: 47% of
the corpus's openers genuinely carry no status marker, and saying so is the
point -- it tells a direction exactly which claims it must read prose for.
The raw tag is preserved verbatim in every row, so nothing is lost.

THE VOCABULARY (slice 9). The bracketed form goes before the gloss, so the
editorial voice survives:

    > **(BE-216)(i)** `[PROVED]` *(the sum is hypothesis-free)* At a firing ...

  PROVED . PROVED-MOD <label> . INFORMAL <gap> . ASSERTED <driver>
  MEASURED <driver> . CONSTRUCTED <driver> . CONJECTURED . REFUTED <witness>
  MOOT/RETIRED <successor> . OPEN

It takes precedence over the leading-token reading. The trailing obligations
are what `--lint` checks, and they mechanize three rules the phase already
promoted: RESEARCH-ARC section 4 (a driver per headline sentence), section 7
(name the evidence stratum), and the 2026-09-09 sharpening that a kill
condition naming a number must carry its derivation.

`--lint` BINDS THE BRACKETED FORM ONLY, and that is deliberate. Only 42% of
the corpus's existing MEASURED claims name a driver anywhere in their clause,
so a retroactive rule would fail correct prose and be switched off rather than
obeyed. An author who writes `[MEASURED]` opts into naming the driver; legacy
freeform tags stay ungated until slice 10 converts them, and conversion is
where the naming gets added. `--lint` compares against HEAD and checks only
what a commit ADDS or CHANGES, so -- like the other two docs gates -- it must
run BEFORE committing, or with `--all`.
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CACHE = os.path.join(HERE, ".ledger-cache")

# The corpus, in reading order. `notes/Harness-structure.md` slice 12 splits
# these; this list is the single place that then changes.
SOURCES = [
    "notes/Pencil-informal.md",
    "notes/Pencil-informal-grid.md",
    "notes/Pencil-W4-informal.md",
    "notes/Pencil-strategy.md",
    "notes/Pencil-fanout.md",
]

# --- the closed vocabulary (`notes/Harness-structure.md` slice 9) -----------
# Maps a leading tag token to its status. Keys are matched case-insensitively
# against the tag's first word(s), longest first. A status whose row carries
# `needs` must name that thing; slice 9's --lint enforces it, this slice only
# records what is there.
VOCAB = {
    "proved by exhaustion": ("PROVED", "exhaustion"),
    "proven by exhaustion": ("PROVED", "exhaustion"),
    "proven-informally": ("INFORMAL", None),
    "proved-informally": ("INFORMAL", None),
    "proven informally": ("INFORMAL", None),
    "proved": ("PROVED", None),
    "proven": ("PROVED", None),
    "measured": ("MEASURED", None),
    "asserted": ("ASSERTED", None),
    "constructed": ("CONSTRUCTED", None),
    "conjectured": ("CONJECTURED", None),
    "refuted": ("REFUTED", None),
    "refutation": ("REFUTED", None),
    "moot": ("MOOT", None),
    "retired": ("RETIRED", None),
    "open": ("OPEN", None),
    "informal": ("INFORMAL", None),
}
# Statuses that count as "this claim is closed" for --frontier.
CLOSED = {"PROVED", "REFUTED", "MOOT", "RETIRED"}
# The bracketed form's obligations (`notes/Harness-structure.md` slice 9).
# Value is what the clause must NAME, or None. These are enforced by --lint on
# the BRACKETED form only -- deliberately, because only 42% of the corpus's
# existing MEASURED claims name a driver anywhere in their clause, so a
# retroactive rule would fail correct prose and be disabled rather than obeyed
# (`CLAUDE.md`: a gate that fails the tree on day one gets turned off). An
# author who opts into `[MEASURED]` opts into naming the driver; legacy
# freeform tags stay ungated until slice 10 converts them, and conversion is
# where the naming gets added.
BRACKET_OK = {
    "PROVED": None,
    "PROVED-MOD": "label",     # which claim it is modulo
    "INFORMAL": "gap",         # what is not argued
    "ASSERTED": "driver",      # RESEARCH-ARC section 4: a driver per claim
    "MEASURED": "driver",
    "CONSTRUCTED": "driver",
    "CONJECTURED": None,
    "REFUTED": "witness",
    "MOOT": "successor",
    "RETIRED": "successor",
    "OPEN": None,
}
NEEDS_PATTERN = {
    "label": re.compile(r"\([A-ZΛ][A-Za-zΛ0-9]*[-–][A-Za-z0-9_₀-₉\']+\)"),
    "driver": re.compile(r"--[a-z][a-z0-9-]{2,}|\b[a-z][a-z0-9_]{2,}\.py\b"
                         r"|\b[a-z][a-z0-9_]{2,}\.[a-z_]+\(|`[a-z][a-z0-9_]*\.[a-z_]+`"),
    "witness": re.compile(r"\([A-ZΛ][A-Za-zΛ0-9]*[-–][A-Za-z0-9_₀-₉\']+\)|`[^`]+`"),
    "successor": re.compile(r"\([A-ZΛ][A-Za-zΛ0-9]*[-–][A-Za-z0-9_₀-₉\']+\)"),
    "gap": re.compile(r"\S"),
}

# `> **(LABEL)(clause)**` with the bold closing right after -- see PARSING (1).
OPENER = re.compile(r"^>\s*\*\*\(([^)]{1,60})\)((?:\([^)]{1,12}\))?)\*\*")
# A bare sub-clause token: roman numeral, single letter, optional sub/digit.
SUBITEM = re.compile(r"^(?:[ivx]{1,4}|[a-z][₀-₉\d]?|\d{1,2})$")
# A label-shaped citation inside prose.
CITE = re.compile(r"\(([A-ZΛ][A-Za-zΛ0-9]*(?:-[A-Za-z0-9_₀-₉']+)?)\)")
CODE = re.compile(r"`[^`]*`")
BRACKET = re.compile(r"^\s*`\[([A-Z][A-Z-]*)\]`")
GAP = re.compile(r"§\(([^)]+)\)")
DIRECTION = re.compile(r"direction\s+([A-Z][A-Z0-9]{2,})")


def section_key(heading):
    """Stable identity for a section, immune to its prose being rewritten.

    Section headings are themselves status surfaces: `§(K-dom)`'s grew a whole
    new clause when direction DSAT landed, and 37 sections share the prefix
    `§(K-bare-ext)` and are told apart only by their direction code. So
    identity is (gap token, direction code) -- never the heading text, which
    changes under a claim whose status did not. Keying on full headings
    reported three spurious transitions and 500+ phantom add/removes.
    """
    gap = GAP.search(heading)
    dirn = DIRECTION.search(heading)
    if not gap:
        return heading[:40].strip()
    return f"§({gap.group(1)})" + (f"/{dirn.group(1)}" if dirn else "")


def sh(cmd, cwd=ROOT):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


# --------------------------------------------------------------------------
# parsing
# --------------------------------------------------------------------------

def read_tag(block):
    """Return (raw_tag, rest) from a joined clause block.

    The tag is the leading `*( ... )*` parenthetical. 41% of them run past
    their opening line, so this scans for the matching close with inline code
    masked (a backticked `f(x)` must not close the tag). Returns ('', block)
    when the clause opens with no tag at all.
    """
    s = block.lstrip()
    if not s.startswith("*("):
        return "", block
    masked = CODE.sub(lambda m: " " * len(m.group(0)), s)
    depth = 0
    for i, ch in enumerate(masked[1:], start=1):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return s[2:i].strip(), s[i + 1:].lstrip("* \t")
    return "", block  # unbalanced: treat as untagged rather than guess


def classify(raw, block):
    """(status, evidence) from a tag. Leading token only -- see the docstring."""
    m = BRACKET.match(block)
    if m:  # slice 9's bracketed form wins outright
        tag = m.group(1)
        return (tag if tag in BRACKET_OK else "UNTAGGED"), None
    if not raw:
        return "UNTAGGED", None
    flat = re.sub(r"[*_`]", "", raw).strip().lower()
    for key in sorted(VOCAB, key=len, reverse=True):
        if flat.startswith(key):
            nxt = flat[len(key):len(key) + 1]
            if nxt and nxt.isalpha():
                continue  # `provenance` must not match `proven`
            return VOCAB[key]
    return "UNTAGGED", None


def parse(path, text):
    """Yield ledger rows for one source file."""
    section = step = ""
    cur_label = ""
    rows = []
    pending = None  # (label, clause, section, step, [body lines])

    def flush():
        if pending is None:
            return
        label, clause, sec, stp, body = pending
        block = " ".join(body).strip()
        # Slice 9's form is `[STATUS]` then the usual gloss. Strip the bracket
        # first so the gloss is still captured as the tag and the bracket does
        # not leak into `claim` -- where its own backticks once satisfied the
        # `[REFUTED] must name a witness` check, passing a clause that named
        # nothing.
        bm = BRACKET.match(block)
        bracket = bm.group(1) if bm else ""
        rest0 = block[bm.end():].lstrip() if bm else block
        raw, rest = read_tag(rest0)
        status, evidence = classify(raw, block)
        if bracket:
            status = bracket if bracket in BRACKET_OK else "UNTAGGED"
        cites = sorted({c for c in CITE.findall(CODE.sub(" ", rest))
                        if c != label and (("-" in c) or c in ALLCAPS_BARE)})
        rows.append({
            "file": path, "section": sec, "seckey": section_key(sec), "step": stp,
            "label": label, "clause": clause,
            "status": status, "evidence": evidence or "",
            "tag": raw, "bracket": bracket,
            "claim": re.sub(r"\s+", " ", rest),
            "cites": ";".join(cites),
        })

    for line in text.split("\n"):
        if line.startswith("## "):
            flush(); pending = None
            section, cur_label = line[3:].strip(), ""
            continue
        if line.startswith("### "):
            flush(); pending = None
            step = line[4:].strip()
            continue
        m = OPENER.match(line)
        if m:
            flush()
            tok, clause = m.group(1), m.group(2).strip("()")
            if SUBITEM.match(tok):
                # a sub-clause of the enclosing label -- see PARSING (2)
                label, clause = cur_label, tok
            else:
                label = tok
                cur_label = tok
            pending = (label, clause, section, step, [line[m.end():]])
            continue
        if pending is not None:
            if line.startswith(">"):
                pending[4].append(line.lstrip("> ").rstrip())
            else:
                flush(); pending = None
    flush()
    return [r for r in rows if r["label"]]


# Bare (dashless) label families that really are labels, not prose: the
# collision-prone ones `notes/Pencil-labels.md` (L5) documents.
ALLCAPS_BARE = set()


def build():
    rows = []
    for rel in SOURCES:
        p = os.path.join(ROOT, rel)
        if not os.path.isfile(p):
            continue
        with open(p, encoding="utf-8") as f:
            rows.extend(parse(rel, f.read()))
    # Five label-clauses are stated TWICE inside one section (a claim restated
    # in the section's own Verification block, mostly). Without an ordinal the
    # identity key collides, and a colliding key silently drops one row from
    # --delta and reports the other as changed-every-run in --lint. Ordinals
    # are assigned in document order, so they are stable under appends.
    seen = {}
    for r in rows:
        k = (r["file"], r["seckey"], r["label"], r["clause"])
        seen[k] = seen.get(k, 0) + 1
        r["occ"] = str(seen[k])
    return rows


# --------------------------------------------------------------------------
# cache
# --------------------------------------------------------------------------

FIELDS = ["file", "section", "seckey", "step", "label", "clause", "occ",
          "status", "evidence", "bracket", "tag", "claim", "cites"]


def fingerprint():
    fp = {}
    for rel in SOURCES:
        p = os.path.join(ROOT, rel)
        if os.path.isfile(p):
            st = os.stat(p)
            fp[rel] = [st.st_size, st.st_mtime_ns]
    return fp


def load(rebuild=False):
    tsv = os.path.join(CACHE, "ledger.tsv")
    man = os.path.join(CACHE, "sources.json")
    fp = fingerprint()
    if not rebuild and os.path.isfile(tsv) and os.path.isfile(man):
        try:
            if json.load(open(man)) == fp:
                with open(tsv, encoding="utf-8") as f:
                    hdr = f.readline().rstrip("\n").split("\t")
                    return [dict(zip(hdr, l.rstrip("\n").split("\t")))
                            for l in f if l.strip()]
        except Exception:
            pass  # any cache problem is a rebuild, never an error
    rows = build()
    os.makedirs(CACHE, exist_ok=True)
    with open(tsv, "w", encoding="utf-8") as f:
        f.write("\t".join(FIELDS) + "\n")
        for r in rows:
            f.write("\t".join(str(r.get(k, "")).replace("\t", " ")
                              for k in FIELDS) + "\n")
    json.dump(fp, open(man, "w"))
    return rows


def locate(row):
    """Live line number, resolved now -- never stored. See the docstring.

    Scoped to the row's own SECTION, not just its file: 20 labels are claimed
    in more than one section (the registry's collision case), so a file-wide
    first-match would point a reader at the wrong home -- both `(D3)` rows
    reported the same line before this was scoped.
    """
    p = os.path.join(ROOT, row["file"])
    needle = f"**({row['label']})"
    if row["clause"]:
        needle += f"({row['clause']})"
    needle += "**"
    first = 0
    try:
        with open(p, encoding="utf-8") as f:
            section = ""
            for i, line in enumerate(f, 1):
                if line.startswith("## "):
                    section = section_key(line[3:].strip())
                elif line.startswith(">") and needle in line:
                    if section == row["seckey"]:
                        return i
                    first = first or i
    except OSError:
        pass
    return first


# --------------------------------------------------------------------------
# output
# --------------------------------------------------------------------------

def trunc(t, n):
    """Truncate for a scanning view, and SAY SO -- a silently cut claim can
    drop the proviso that makes it true, which is the BGENUINE failure this
    tool exists to prevent. `--brief` and `--full` never call this."""
    return t if len(t) <= n else t[:n].rstrip() + f" …[+{len(t)-n} chars; --full]"


def cmd_lint(rows, args):
    """Gate the status vocabulary on NEW or EDITED openers.

    Grandfathering is the whole design. Slice 8 measured 666 UNTAGGED claims
    (51% of the corpus); a gate that failed on those would be switched off in
    a week. So: legacy openers pass untouched, and what is checked is what
    this commit ADDS or CHANGES, compared against HEAD.

    Like the other two docs gates it inspects changed-vs-HEAD files, so it
    must be run BEFORE committing, or with --all (`notes/Pencil-structure.md`
    *Gates for any continuation*, blind spot 1).
    """
    before = {}
    if not args.all:
        for rel in SOURCES:
            r = sh(["git", "show", f"HEAD:{rel}"])
            if r.returncode == 0:
                seen = {}
                for row in parse(rel, r.stdout):
                    kk = (rel, row["seckey"], row["label"], row["clause"])
                    seen[kk] = seen.get(kk, 0) + 1
                    before[kk + (str(seen[kk]),)] = row

    bad, untagged, checked = [], [], 0
    for r in rows:
        k = (r["file"], r["seckey"], r["label"], r["clause"], r.get("occ", "1"))
        if not args.all:
            old = before.get(k)
            if old is not None and old["tag"] == r["tag"] and old["claim"] == r["claim"]:
                continue  # untouched by this commit
        checked += 1
        bracket = r.get("bracket", "")
        if bracket and bracket not in BRACKET_OK:
            bad.append((r, f"`[{bracket}]` is not in the vocabulary "
                           f"({', '.join(sorted(BRACKET_OK))})"))
            continue
        if bracket:
            needs = BRACKET_OK[bracket]
            if needs:
                pat = NEEDS_PATTERN[needs]
                if not pat.search(r["tag"] + " " + r["claim"]):
                    bad.append((r, f"[{r['status']}] must name a {needs}; "
                                   f"none found in the tag or clause"))
        elif r["status"] == "UNTAGGED":
            untagged.append(r)

    scope = "whole corpus" if args.all else "claims added or changed vs HEAD"
    print(f"# ledger lint -- {checked} claim(s) checked ({scope})")
    for r, why in bad:
        print(f"FAIL {name(r):<18} {where(r)}\n     {why}")
    if untagged:
        head = untagged[:12]
        print(f"\n{len(untagged)} UNTAGGED "
              f"{'(pre-existing; slice 10 backfills these)' if args.all else 'in this change'}:")
        for r in head:
            print(f"  {name(r):<18} {where(r)}")
        if len(untagged) > len(head):
            print(f"  ... {len(untagged) - len(head)} more")
        if args.strict and not args.all:
            print("\n--strict: a new claim must carry a bracketed status.")
    if bad:
        print(f"\nFAILED: {len(bad)} vocabulary violation(s).")
        return 1
    if args.strict and untagged and not args.all:
        return 1
    print("\nOK: no vocabulary violations."
          + ("" if args.all else " (Run before committing; --all for the corpus.)"))
    return 0


def name(r):
    return f"({r['label']})" + (f"({r['clause']})" if r["clause"] else "")


def where(r):
    bits = [r["file"].replace("notes/", "")]
    if r["section"]:
        bits.append(r["section"][:44])
    if r["step"]:
        bits.append(r["step"][:28])
    return " | ".join(bits)


def show(r, full=False, loc=True):
    ln = f":{locate(r)}" if loc else ""
    head = f"{name(r):<18} [{r['status']}]"
    if r["evidence"]:
        head += f" ({r['evidence']})"
    print(f"{head}\n    {where(r)}{ln}")
    if r["tag"]:
        print(f"    tag: {re.sub(chr(10), ' ', r['tag'])[:160]}")
    body = r["claim"] if full else trunc(r["claim"], 220)
    if body:
        print(f"    {body}")
    if r["cites"]:
        print(f"    cites: {' '.join('(' + c + ')' for c in r['cites'].split(';'))}")
    print()


def select(rows, label):
    want = label.strip().strip("()")
    base = want.split(")(")[0]
    return [r for r in rows if r["label"] == base or name(r) == f"({want})"]


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------

def cmd_label(rows, args):
    hits = select(rows, args.label)
    if not hits:
        print(f"no such label: {args.label}", file=sys.stderr)
        return 1
    homes = {(h["file"], h["seckey"]) for h in hits}
    if len(homes) > 1:
        print(f"# NOTE: ({args.label.strip('()')}) is claimed in {len(homes)} "
              f"sections -- a collision the registry warns about "
              f"(notes/Pencil-labels.md). All shown.\n")
    for r in hits:
        show(r, full=args.full)
    return 0


def cmd_status(rows, args):
    want = args.status.upper()
    hits = [r for r in rows if r["status"] == want]
    if args.section:
        hits = [r for r in hits if args.section.lower() in r["section"].lower()]
    if args.file:
        hits = [r for r in hits if args.file in r["file"]]
    print(f"# {len(hits)} claim(s) at [{want}]"
          + (f" in sections matching {args.section!r}" if args.section else "")
          + "\n")
    for r in hits[:args.head]:
        show(r, full=args.full, loc=False)
    if len(hits) > args.head:
        print(f"... {len(hits) - args.head} more (raise --head)")
    return 0


def cmd_frontier(rows, args):
    by = {}
    for r in rows:
        by.setdefault(r["label"], []).append(r)

    def closed(lab):
        rs = by.get(lab)
        return bool(rs) and any(x["status"] in CLOSED for x in rs)

    out = []
    for r in rows:
        if r["status"] in CLOSED or not r["cites"]:
            continue
        cites = r["cites"].split(";")
        known = [c for c in cites if c in by]
        if known and all(closed(c) for c in known):
            out.append((len(known), r))
    out.sort(key=lambda t: -t[0])
    print(f"# {len(out)} open claim(s) whose every KNOWN citation is closed "
          f"-- the cheapest live leaves.\n"
          f"# 'Closed' means the cited label carries a PROVED/REFUTED/MOOT/"
          f"RETIRED clause. It is a claim by its author, not a check.\n")
    for n, r in out[:args.head]:
        show(r, full=args.full, loc=False)
    if len(out) > args.head:
        print(f"... {len(out) - args.head} more (raise --head)")
    return 0


def cmd_cited_by(rows, args):
    want = args.cited_by.strip().strip("()").split(")(")[0]
    hits = [r for r in rows if want in r["cites"].split(";")]
    print(f"# {len(hits)} claim(s) cite ({want}) -- what a change to it "
          f"reaches.\n")
    for r in hits[:args.head]:
        show(r, full=args.full, loc=False)
    return 0


def cmd_brief(rows, args):
    """The briefing-packet primitive: statements quoted, never retyped."""
    print("# Briefing block -- generated by notes/ledger.py --brief.")
    print("# Statements are quoted verbatim from the workbook WITH their")
    print("# hypotheses; a spec must not retype one from a summary surface")
    print("# (RESEARCH-ARC.md section 7, the BGENUINE incident).\n")
    miss = []
    for lab in args.brief:
        hits = select(rows, lab)
        if not hits:
            miss.append(lab)
            continue
        for r in hits:
            print(f"## {name(r)}  [{r['status']}]"
                  + (f" ({r['evidence']})" if r["evidence"] else ""))
            print(f"    {where(r)}:{locate(r)}")
            if r["tag"]:
                print(f"    tag: {r['tag']}")
            print(f"\n    {r['claim']}\n")  # never truncated -- see cmd_brief
            if r["cites"]:
                print("    cites: "
                      + " ".join("(" + c + ")" for c in r["cites"].split(";")))
            print()
    if miss:
        print(f"# NOT FOUND (check the registry): {', '.join(miss)}")
        return 1
    return 0


def cmd_delta(rows, args):
    """Status change-set vs a git ref, for the landing's commit message."""
    old = []
    for rel in SOURCES:
        r = sh(["git", "show", f"{args.delta}:{rel}"])
        if r.returncode == 0:
            old.extend(parse(rel, r.stdout))
    # Keyed by SECTION too: 20 labels are claimed in more than one section of
    # one file, and a (file, label, clause) key collapses them -- which
    # reported three spurious `X -> UNTAGGED` transitions before this was
    # fixed, one of them on a label whose real status never moved.
    key = lambda r: (r["file"], r["seckey"], r["label"], r["clause"],
                     r.get("occ", "1"))
    before = {key(r): r for r in old}
    after = {key(r): r for r in rows}
    changed, added = [], []
    for k, r in after.items():
        if k not in before:
            added.append(r)
        elif before[k]["status"] != r["status"]:
            changed.append((before[k]["status"], r))
    gone = [r for k, r in before.items() if k not in after]

    # A claim that leaves one (file, section) and reappears in another is a
    # RELOCATION, not a deletion -- direction RESGRID moved §(K-res)'s six
    # (RS-.) claims into the grid workbook, which a file-keyed diff would
    # otherwise report as six removals with no corresponding arrivals.
    ident = lambda r: (r["label"], r["clause"], r.get("occ", "1"))
    arrived = {ident(r): r for r in added}
    relocated = []
    for r in list(gone):
        dst = arrived.get(ident(r))
        if dst is not None:
            relocated.append((r, dst))
            gone.remove(r)
            added.remove(dst)
            if r["status"] != dst["status"]:
                changed.append((r["status"], dst))
    print(f"# ledger delta vs {args.delta}")
    for was, r in sorted(changed, key=lambda t: t[1]["label"]):
        ev = f" ({r['evidence']})" if r["evidence"] else ""
        print(f"  {name(r):<18} {was} -> {r['status']}{ev}")
    if added:
        print(f"  + {len(added)} new claim(s): "
              + " ".join(name(r) for r in added[:14])
              + (" ..." if len(added) > 14 else ""))
    if gone:
        print(f"  - {len(gone)} removed: "
              + " ".join(name(r) for r in gone[:14])
              + (" ..." if len(gone) > 14 else ""))
    if relocated:
        print(f"  ~ {len(relocated)} relocated (same claim, new home): "
              + "; ".join(f"{name(a)} {a['seckey']}->{b['seckey']}"
                          for a, b in relocated[:6])
              + (" ..." if len(relocated) > 8 else ""))
    if not (changed or added or gone or relocated):
        print("  (no change)")
    return 0


def cmd_list(rows, args):
    print(f"{len(rows)} claims across {len({r['file'] for r in rows})} files\n")
    for rel in SOURCES:
        rs = [r for r in rows if r["file"] == rel]
        if not rs:
            continue
        counts = {}
        for r in rs:
            counts[r["status"]] = counts.get(r["status"], 0) + 1
        head = ", ".join(f"{k} {v}" for k, v in
                         sorted(counts.items(), key=lambda t: -t[1]))
        print(f"  {rel:<34} {len(rs):5d} claims   {head}")
    return 0


def cmd_stats(rows, args):
    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    tot = len(rows)
    print(f"status census over {tot} claims\n")
    for k, v in sorted(counts.items(), key=lambda t: -t[1]):
        print(f"  {v:5d}  {100*v/tot:5.1f}%  {k}")
    un = [r for r in rows if r["status"] == "UNTAGGED" and r["tag"]]
    print(f"\n{len(un)} UNTAGGED claims DO carry a parenthetical whose leading "
          f"token is not a status word.\nThese are slice 10's backfill "
          f"candidates; the 20 commonest leading tokens:\n")
    heads = {}
    for r in un:
        h = re.sub(r"[*_`]", "", r["tag"]).strip().split(";")[0][:34]
        heads[h] = heads.get(h, 0) + 1
    for k, v in sorted(heads.items(), key=lambda t: -t[1])[:20]:
        print(f"  {v:4d}  {k}")
    return 0


def cmd_selftest(rows, args):
    """Parser audit: coverage against raw candidates, and what was dropped."""
    ok = True
    for rel in SOURCES:
        p = os.path.join(ROOT, rel)
        if not os.path.isfile(p):
            continue
        text = open(p, encoding="utf-8").read()
        cand = sum(1 for l in text.split("\n")
                   if l.startswith(">") and "**(" in l)
        opened = loose = 0
        cur = ""
        for l in text.split("\n"):
            if l.startswith("## "):
                cur = ""
            m = OPENER.match(l)
            if not m:
                continue
            opened += 1
            tok = m.group(1)
            if SUBITEM.match(tok):
                # A bare `(a)`/`(iii)` with no labelled opener above it in the
                # section is a narrative bullet, not a claim -- the fan-out
                # write-ups use that shape. Dropping it is correct; it is
                # counted here so the arithmetic below still closes.
                if not cur:
                    loose += 1
            else:
                cur = tok
        got = len([r for r in rows if r["file"] == rel])
        print(f"{rel}\n   {cand:5d} blockquote lines containing '**('\n"
              f"   {opened:5d} match the opener shape (bold closes after the "
              f"label)\n   {loose:5d} unattached sub-item bullets (no parent "
              f"label in section; dropped)\n   {got:5d} ledger rows")
        if got != opened - loose:
            print(f"   !! {opened - loose - got} opener(s) unaccounted for")
            ok = False
    orphan = [r for r in rows if not r["label"]]
    if orphan:
        print(f"!! {len(orphan)} rows with no label"); ok = False
    subs = [r for r in rows if SUBITEM.match(r["label"])]
    if subs:
        print(f"!! {len(subs)} rows whose LABEL is a bare sub-item token "
              f"(should have been attached to a parent): "
              + " ".join(name(r) for r in subs[:10]))
        ok = False
    multi = {}
    for r in rows:
        multi.setdefault(r["label"], set()).add((r["file"], r["seckey"]))
    coll = {k: v for k, v in multi.items() if len(v) > 1}
    print(f"\n{len(coll)} label(s) claimed in more than one section "
          f"(the registry's collision case; --label shows all homes):")
    for k, v in sorted(coll.items())[:12]:
        print(f"   ({k}) in {len(v)} sections")
    print("\nselftest:", "OK" if ok else "FAILED")
    return 0 if ok else 1


def main(argv):
    p = argparse.ArgumentParser(
        prog="ledger.py",
        description="Query what the PENCIL corpus claims about its own "
                    "evidence (see the docstring; regenerated, never stored).")
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--label", metavar="L", help="every clause of one label")
    mode.add_argument("--status", metavar="S", help="claims at a status")
    mode.add_argument("--frontier", action="store_true",
                      help="open claims whose every known citation is closed")
    mode.add_argument("--cited-by", metavar="L", help="what cites this claim")
    mode.add_argument("--brief", nargs="+", metavar="L",
                      help="briefing-packet block for a label set")
    mode.add_argument("--delta", metavar="REF",
                      help="status change-set vs a git ref")
    mode.add_argument("--list", action="store_true", help="per-file counts")
    mode.add_argument("--stats", action="store_true", help="status census")
    mode.add_argument("--lint", action="store_true",
                      help="gate the status vocabulary on new/edited claims")
    mode.add_argument("--selftest", action="store_true", help="parser audit")
    p.add_argument("--section", metavar="S", help="narrow by section substring")
    p.add_argument("--file", metavar="F", help="narrow by file substring")
    p.add_argument("--head", type=int, default=40, help="max rows (default 40)")
    p.add_argument("--full", action="store_true", help="untruncated claim text")
    p.add_argument("--rebuild", action="store_true", help="force cache rebuild")
    p.add_argument("--all", action="store_true",
                   help="--lint: check the whole corpus, not just this change")
    p.add_argument("--strict", action="store_true",
                   help="--lint: also fail on a NEW claim left UNTAGGED")
    args = p.parse_args(argv)

    rows = load(rebuild=args.rebuild)
    if args.label:
        return cmd_label(rows, args)
    if args.status:
        return cmd_status(rows, args)
    if args.frontier:
        return cmd_frontier(rows, args)
    if args.cited_by:
        return cmd_cited_by(rows, args)
    if args.brief:
        return cmd_brief(rows, args)
    if args.delta:
        return cmd_delta(rows, args)
    if args.lint:
        return cmd_lint(rows, args)
    if args.list:
        return cmd_list(rows, args)
    if args.stats:
        return cmd_stats(rows, args)
    return cmd_selftest(rows, args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
