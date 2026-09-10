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
  --round N --direction D --labels L1 L2 ... [--question T] [--out]
                          a dispatch briefing packet with the claim statements
                          GENERATED, so a spec never retypes one
  --backlog [--decisive]  UNTAGGED claims ranked by citations -- the tagging
                          worklist; --decisive narrows to those whose own
                          clause already states a status (transcription)
  --reserve TOK ...       0-hit check a proposed label prefix, corpus-wide
                          (RESEARCH-ARC section 1, mechanized)
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

WHAT THIS IS NOT. An index, exactly as `notes/pencil/labels.md` says of
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
import collections
import glob
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
# The workbook is one file per section since the 2026-09-09 split
# (`notes/Harness-structure.md` slice 12), so the source list is a glob rather
# than a hand-maintained enumeration -- a new direction's file is picked up
# with no edit here, which is the point of the split.
def _sources():
    pat = os.path.join(ROOT, "notes/pencil/workbook")
    found = sorted(glob.glob(os.path.join(pat, "*.md"))
                   + glob.glob(os.path.join(pat, "bare-ext", "*.md")))
    rel = [os.path.relpath(f, ROOT) for f in found
           if not os.path.basename(f).startswith(("README", "_"))]
    # Two files outside `workbook/` also carry label-clause openers: the
    # strategy doc's own C/U/ZH families and the fan-out write-ups. They are
    # few (16 claims) but they are claims, and a ledger that silently skipped
    # them would answer "no such label" for a label that exists.
    return rel + ["notes/pencil/strategy.md", "notes/pencil/fanout.md"]


SOURCES = _sources()

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
# A leading `- ` / `* ` list marker is allowed: seven real openers use one.
OPENER = re.compile(r"^>\s*(?:[-*]\s+)?\*\*\(([^)]{1,60})\)"
                    r"((?:\([^)]{1,12}\))?)\*\*")
# The SAME shape but with more text inside the bold -- a titled opener
# (`**(OC-8) what (OUT) now reduces to, exactly.**`), an assertion
# (`**(ANH-R1) is discharged at the generic point ...**`), or a superseding
# verdict (`**(FR-R1) - PROVEN.**`). 87 such lines exist and were invisible
# until 2026-09-09; missing them is how `--label '(FR-R1)'` answered OPEN for
# a claim the corpus declares PROVEN with a 1976-site certificate. A
# POSSESSIVE after the label (`**(CH-1)'s girth ...**`) is ordinary prose and
# stays excluded, as does any bold whose label is not at its start.
# The inner text is TEMPERED (`(?:(?!\*\*).)`) rather than `[^*]`: these bolds
# routinely contain italics, and `[^*]` cannot span them -- which silently
# excluded the exact line this pattern was written for,
# `**(E-loc) is REFUTED - 2026-09-02, direction WELOC, *Steps EL1-EL6* below.**`
OPENER_WIDE = re.compile(r"^>\s*(?:[-*]\s+)?\*\*\(([^)]{1,60})\)"
                         r"((?:\([^)]{1,12}\))?)(?![\u2019']s\b)"
                         r"((?:(?!\*\*).){1,300}?)\*\*")
# Verdict words the corpus writes in CAPS inside such a bold. They are a HINT
# surfaced to the reader, never a status the tool assigns: `**(BE-44)(ii)** is
# **PROVED in the `dim<P> = 6` direction only**` is exactly why -- reading
# PROVED off it would drop the scope restriction that makes it true.
VERDICT_HINT = re.compile(r"\b(PROVEN|PROVED|REFUTED|SUPERSEDED|FIRED|MOOT|"
                          r"RETIRED|DISCHARGED|FALSE|CLOSED|OPEN)\b")
# A label token. `OPENER`'s `([^)]{1,60})` accepts ANY parenthetical, which
# indexed prose asides as claims with labels like `'legality, placement-free'`
# and `'2,3'`. A real label is a registry token or a bare sub-item.
LABELISH = re.compile(r"^(?:[A-ZΛ][A-Za-zΛ0-9]*(?:[-–][A-Za-z0-9_₀-₉'′]+)?"
                      r"|[ivx]{1,4}|[a-z][₀-₉\d]?|\d{1,2}|[A-Z]\d?|Λ\d[a-z]?)$")
# A bare sub-clause token: roman numeral, single letter, optional sub/digit.
SUBITEM = re.compile(r"^(?:[ivx]{1,4}|[a-z][₀-₉\d]?|\d{1,2})$")
# A label-shaped citation inside prose, with its CLAUSE when the corpus
# qualifies one -- `(BE-45)(ii)`. The corpus writes thousands of these, so
# citation counts can be computed at clause granularity; ranking by the
# LABEL's total instead put almost a different worklist at the top (only 6 of
# a top-40 survive re-ranking).
CITE = re.compile(r"\(([A-ZΛ][A-Za-zΛ0-9]*(?:-[A-Za-z0-9_₀-₉']+)?)\)"
                  r"(\((?:[ivx]{1,4}|[a-z]\d?|\d{1,2})\))?")
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


def parse(path, text, keep_fragments=False):
    """Yield ledger rows for one source file."""
    section = step = ""
    cur_label = ""
    rows = []
    pending = None  # (label, clause, section, step, [body lines])

    def flush():
        if pending is None:
            return
        label, clause, sec, stp, body, hint, wideflag, contflag = pending
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
        found = CITE.findall(CODE.sub(" ", rest))
        cites = sorted({c for c, _cl in found
                        if c != label and (("-" in c) or c in ALLCAPS_BARE)})
        # `label:clause` for the qualified ones, so --cited-by can be exact
        qual = sorted({f"{c}:{_cl.strip('()')}" for c, _cl in found
                       if _cl and c != label and "-" in c})
        rows.append({
            "file": path, "section": sec, "seckey": section_key(sec), "step": stp,
            "label": label, "clause": clause,
            "status": status, "evidence": evidence or "",
            "tag": raw, "bracket": bracket, "hint": hint, "wide": wideflag,
            "cite": contflag,
            "claim": re.sub(r"\s+", " ", rest),
            "cites": ";".join(cites), "citesq": ";".join(qual),
        })

    prev = ""
    for line in text.split("\n"):
        if line.startswith("## "):
            flush(); pending = None
            section, cur_label = line[3:].strip(), ""
            continue
        if line.startswith("### "):
            flush(); pending = None
            step = line[4:].strip()
            continue
        # A bold that starts a WRAPPED line is a mid-sentence prose citation,
        # not a claim opener: "...and by\n> **(BE-22)(vi)** a rigid side
        # collapses...". 40 such rows exist. They are kept in the index (so
        # --label still shows them) but flagged, because the class is not
        # cleanly separable -- `> **(A)** v* is a hub` after "So exactly one
        # of" is a genuine enumerated alternative. --backlog drops them.
        pp = prev.lstrip(">").strip()
        is_cont = bool(pp) and not prev.startswith(("#", "|")) \
            and not _TERMINAL.search(pp)
        prev = line
        m = OPENER.match(line)
        wide = None
        if not m:
            wide = OPENER_WIDE.match(line)
            m = wide
        if m:
            flush()
            tok, clause = m.group(1), m.group(2).strip("()")
            if not LABELISH.match(tok):
                pending = None   # flush() above does NOT clear it
                continue         # a parenthesised phrase, not a label
            if SUBITEM.match(tok):
                # a sub-clause of the enclosing label -- see PARSING (2)
                label, clause = cur_label, tok
            else:
                label = tok
                cur_label = tok
            hint = ""
            if wide is not None:
                inner = wide.group(3)
                hint = " ".join(sorted(set(VERDICT_HINT.findall(inner))))
                # A bracket written AFTER the bold has to be found before the
                # bold's own text is prepended, or `BRACKET.match` never fires
                # and the shape is untaggable -- which is what 93 claims were.
                tail = line[m.end():]
                bm2 = BRACKET.match(tail)
                if bm2:
                    body0 = (f"`[{bm2.group(1)}]` " + inner.strip() + " "
                             + tail[bm2.end():])
                else:
                    body0 = inner.strip() + " " + tail
            else:
                body0 = line[m.end():]
            pending = (label, clause, section, step, [body0], hint,
                       "1" if wide is not None else "", "1" if is_cont else "")
            continue
        if pending is not None:
            if line.startswith(">"):
                pending[4].append(line.lstrip("> ").rstrip())
            else:
                flush(); pending = None
    flush()
    kept = [r for r in rows if r["label"]]
    if not keep_fragments:
        kept = [r for r in kept if not _list_fragment(r)]
    # Occurrence ordinal, assigned HERE rather than in build(): five
    # label-clauses are stated twice inside one section, and any caller that
    # parses directly -- cmd_delta did -- otherwise collapses them and reports
    # fabricated status transitions on unchanged prose.
    seen = {}
    for r in kept:
        k = (r["seckey"], r["label"], r["clause"])
        seen[k] = seen.get(k, 0) + 1
        r["occ"] = str(seen[k])
    return kept


# A bolded label can open a PROSE LIST rather than a claim:
#   > **(BE-14)**, `hbareSplit`, the 2-cut composition lemma ... are untouched.
# The bold closes right after the label, so the opener test passes, and 17 such
# lines were being indexed as claims. They were harmless in the sense that
# matters -- every one came out UNTAGGED, because the leading-token status rule
# refuses to guess -- but they inflated the count and put a phantom second row
# under `--label '(BE-14)'` beside the real one. A genuine claim never opens
# with list punctuation or a lowercase continuation; a TAGGED opener is a claim
# whatever follows, so the filter only applies when there is no tag at all.
_TERMINAL = re.compile(r"([.!?:;]|\*\*|\)\*|\*|`|\)|\]|>)\s*$")
_FRAGMENT = re.compile(r"^['\u2019]s\b|^[,;:)]|^(?:and|or|is|are|was|were|"
                       r"which|that|plus|together|with|not)\b")


def _list_fragment(r):
    # STRICT openers only. A WIDE opener's text is the continuation of its own
    # bold phrase, so it legitimately begins with `is` / `and`:
    # `**(E-loc) is REFUTED - 2026-09-02, direction WELOC ...**` was being
    # discarded as prose by this filter -- the very refutation the wide
    # pattern had just been written to catch.
    return (not r["tag"] and not r.get("bracket") and not r.get("wide")
            and bool(_FRAGMENT.match(r["claim"].lstrip())))


# Bare (dashless) label families that really are labels, not prose: the
# collision-prone ones `notes/pencil/labels.md` (L5) documents.
ALLCAPS_BARE = set()


def build():
    rows = []
    for rel in SOURCES:
        p = os.path.join(ROOT, rel)
        if not os.path.isfile(p):
            continue
        with open(p, encoding="utf-8") as f:
            rows.extend(parse(rel, f.read()))
    return rows


# --------------------------------------------------------------------------
# cache
# --------------------------------------------------------------------------

FIELDS = ["file", "section", "seckey", "step", "label", "clause", "occ",
          "status", "evidence", "bracket", "hint", "wide", "cite", "tag",
          "claim", "cites", "citesq"]


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
    # Match the opener SHAPES rather than a fixed `**(L)**` needle: a wide
    # opener (`**(FR-R1) - PROVEN.**`) has text before the closing `**`, and a
    # needle-based search silently returned the first OTHER row's line for it.
    first = 0
    want_occ = int(row.get("occ", "1"))
    seen = 0
    try:
        with open(p, encoding="utf-8") as f:
            section = ""
            cur = ""
            for i, line in enumerate(f, 1):
                if line.startswith("## "):
                    section = section_key(line[3:].strip())
                    cur = ""
                    continue
                m = OPENER.match(line) or OPENER_WIDE.match(line)
                if not m:
                    continue
                tok, cl = m.group(1), m.group(2).strip("()")
                if not LABELISH.match(tok):
                    continue
                # Track the inherited label exactly as parse() does. A
                # sub-clause's source line reads `> **(i)** ...`, so matching
                # on the row's LABEL alone found nothing -- 34% of rows had no
                # line pointer at all, every one a sub-clause, which gutted
                # `--brief`'s whole job of pointing at the source.
                if SUBITEM.match(tok):
                    lab, cl = cur, tok
                else:
                    lab, cur = tok, tok
                if lab != row["label"] or cl != row["clause"]:
                    continue
                if section != row["seckey"]:
                    first = first or i
                    continue
                seen += 1
                if seen == want_occ:
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
    must be run BEFORE committing, or with --all (`notes/pencil/structure.md`
    *Gates for any continuation*, blind spot 1).
    """
    before = {}
    if not args.all:
        for rel in SOURCES:
            r = sh(["git", "show", f"HEAD:{rel}"])
            if r.returncode == 0:
                for row in parse(rel, r.stdout):
                    before[(rel, row["seckey"], row["label"],
                            row["clause"], row["occ"])] = row

    bad, untagged, checked = [], [], 0
    for r in rows:
        k = (r["file"], r["seckey"], r["label"], r["clause"], r["occ"])
        if not args.all:
            old = before.get(k)
            if (old is not None and old["tag"] == r["tag"]
                    and old["claim"] == r["claim"]
                    and old.get("bracket", "") == r.get("bracket", "")):
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


def cmd_backlog(rows, args):
    """UNTAGGED claims, ranked by how much of the corpus leans on them.

    This is slice 10's worklist, and its shape follows a measurement that
    retired the slice's original plan. 642 claims already classify correctly
    from a legacy freeform tag (`*(proven)*`, `*(measured)*`), because the
    leading-token rule reads them -- so mass-converting those to the bracketed
    form would edit hundreds of mathematical claims and change NO tool output.
    The value is entirely in the 666 that carry no recognizable status, and
    those need reading, not rewriting. Ranked by citation count so the reading
    starts where the corpus leans hardest.

    Tag a claim only when its OWN PROSE is decisive. `UNTAGGED` is a terminal
    state, not a defect: inventing a verdict is the one unrecoverable error
    available here.
    """
    import collections as _c
    cited, cited_cl = _c.Counter(), _c.Counter()
    for r in rows:
        for c in (r["cites"].split(";") if r["cites"] else []):
            cited[c] += 1
        for q in (r["citesq"].split(";") if r.get("citesq") else []):
            cited_cl[q] += 1

    def weight(r):
        """Own-clause citations where the corpus qualifies them, else the
        label's. Ranking every clause by its LABEL's total printed the same
        number against six different rows and put the most-revisited claims --
        the hardest, not the cheapest -- at the head of a worklist meant for
        transcription."""
        if r["clause"]:
            return cited_cl.get(f"{r['label']}:{r['clause']}", 0)
        return cited.get(r["label"], 0)
    stem = stem_headed(rows)
    un = [r for r in rows if r["status"] == "UNTAGGED" and not r.get("cite")
          and not (r["clause"] and (r["file"], r["seckey"], r["label"]) in stem)]
    if args.decisive:
        # The subset whose OWN clause already contains a status word somewhere
        # -- the tag simply never recorded it. These are transcription. The
        # rest are judgement, where `UNTAGGED` is usually the right answer and
        # a pass that forces them is how verdicts get invented.
        un = [r for r in un if _DECISIVE.search(r["tag"] + " " + r["claim"])]
    un.sort(key=lambda r: (-weight(r), -cited.get(r["label"], 0), r["label"]))
    withg = sum(1 for r in un if r["tag"])
    print(f"# {len(un)} UNTAGGED claims -- {withg} carry a gloss whose leading "
          f"token is not a status word, {len(un)-withg} carry none.\n"
          f"# Ranked by citations TO the label. Tag only where the prose is "
          f"decisive; UNTAGGED is a legitimate terminal state.\n")
    for r in un[:args.head]:
        w, lw = weight(r), cited.get(r["label"], 0)
        mark = "  UNCITED" if lw == 0 else ""
        print(f"{w:4d} cites  {name(r):<20} {where(r)}"
              + (f"   [label total {lw}]" if w != lw else "") + mark)
        if r["tag"]:
            print(f"            gloss: {r['tag'][:100]}")
    if len(un) > args.head:
        print(f"\n... {len(un)-args.head} more (raise --head)")
    return 0


# The corpus states evidence in more words than the vocabulary's own tokens:
# "exact; 47/47 seeds", "exhibited, per shape", "a per-pair proof, not a rate",
# "three verified witnesses + EXHAUSTIVE sweeps". Those are transcription too,
# and without them they sat in the judgement pile.
_DECISIVE = re.compile(r"\b(PROVED|PROVEN|REFUTED|MEASURED|ASSERTED|"
                       r"CONSTRUCTED|MOOT|RETIRED|SUPERSEDED|proved|proven|"
                       r"refuted|measured|asserted|constructed|verified|"
                       r"exhaustive|exhaustively|exhibited|proof)\b"
                       r"|\bexact[;,]")


def cmd_reserve(rows, args):
    """0-hit check for a proposed label prefix / section name.

    `RESEARCH-ARC.md` section 1 requires a reserved prefix be verified 0-hit as a
    RAW SUBSTRING across the whole corpus before dispatch -- not just against
    the siblings in flight, because a reservation protects a dispatch from its
    siblings, not from the existing corpus. That check was manual; this is it.
    """
    import glob as _g
    pats = [os.path.join(ROOT, p) for p in
            ("notes/**/*.md", "notes/**/*.py", "notes/**/*.m2",
             "blueprint/**/*.tex", "CombinatorialRigidity/**/*.lean")]
    files = [f for p in pats for f in _g.glob(p, recursive=True)
             if ".ledger-cache" not in f]
    bad = 0
    for token in args.reserve:
        hits = []
        for f in files:
            try:
                t = open(f, encoding="utf-8").read()
            except Exception:
                continue
            n = t.count(token)
            if n:
                hits.append((os.path.relpath(f, ROOT), n))
        if hits:
            bad += 1
            tot = sum(n for _, n in hits)
            print(f"COLLISION  {token!r}: {tot} hit(s) in {len(hits)} file(s)")
            for f, n in sorted(hits, key=lambda t: -t[1])[:6]:
                print(f"             {n:4d}  {f}")
        else:
            print(f"CLEAN      {token!r}: 0 hits across {len(files)} files")
    if bad:
        print(f"\n{bad} token(s) COLLIDE -- pick another, and read "
              f"notes/pencil/labels.md's minting rule before you do.")
        return 1
    print("\nAll clear. Record the reservation in notes/pencil/labels.md in the "
          "SAME commit that mints the first label.")
    return 0


def cmd_round(rows, args):
    """Emit a dispatch briefing packet with the claim statements GENERATED.

    The point is not formatting. `RESEARCH-ARC.md` section 7 records eight
    coordinator predictions refuted across seven kinds, and BGENUINE's was
    precisely a criterion quoted WITHOUT its hypotheses, copied from a summary
    surface -- which handed the dispatch the wrong yardstick and cost the
    round. Statements pasted here come from the claims' own prose, in full, so
    that failure is unavailable by construction. The coordinator writes the
    question and the deliverable; it does not retype the mathematics.
    """
    out = []
    w = out.append
    tag = f"{args.round}-{args.direction}" if args.direction else str(args.round)
    w(f"# Round {tag} — dispatch briefing\n")
    w("**Generated by `python3 notes/ledger.py --round`. The IN SCOPE claims below")
    w("are quoted verbatim from the workbook WITH their hypotheses — do not")
    w("retype a statement from a summary surface (`RESEARCH-ARC.md` §7, the")
    w("BGENUINE incident). Everything in ALL-CAPS brackets is the coordinator's")
    w("to fill before dispatch.**\n")
    w("## The question\n")
    w(args.question or "[ONE PARAGRAPH. The exact question this direction settles. "
                       "State it so a NO is as reportable as a YES.]\n")
    w("## Your context — this is it\n")
    w("Read this packet, your own reserved section, and the drivers named below.")
    w("**Do not read the workbook or `RESEARCH-ARC.md` end to end** — the claims")
    w("you need are quoted in full here, and `python3 notes/ledger.py --label")
    w("'(X)'` answers any further one in a single call. Retrieval by grep was")
    w("measured at ~35 probes and ~137k tokens of context growth for ~18 claims.\n")
    w("## In scope — the claims this direction rests on\n")
    miss = []
    for lab in (args.labels or []):
        hits = select(rows, lab)
        if not hits:
            miss.append(lab)
            continue
        for r in hits:
            w(f"### {name(r)}  `[{r['status']}]`"
              + (f" ({r['evidence']})" if r["evidence"] else ""))
            w(f"*{where(r)}:{locate(r)}*\n")
            if r["tag"]:
                w(f"> tag: {r['tag']}\n")
            w(r["claim"] + "\n")
            if r["cites"]:
                w("cites: " + " ".join("(" + c + ")" for c in r["cites"].split(";")) + "\n")
    if miss:
        w(f"**NOT FOUND — check `notes/pencil/labels.md`: {', '.join(miss)}**\n")
    w("## Reservation\n")
    w(f"Reserved label prefix: **[PREFIX]**; reserved section name: **[§(NAME)]**.")
    w("Both verified 0-hit with `python3 notes/ledger.py --reserve '[PREFIX]'`")
    w("before dispatch. A reservation protects you from your siblings, not from")
    w("the existing corpus — clause L1 still binds inside it.\n")
    w("## Harness\n")
    w("[WHICH DRIVERS, WHICH ENTRY POINTS. Name the functions you expect to reuse;")
    w("`notes/scripts/README.md` is the harness map. Every headline claim needs a")
    w("driver that tests THAT SENTENCE — and *exhaustive* / *forced* / *the only*")
    w("are their own claim class needing their own driver.]\n")
    w("## The coordinator's prediction — TO BE TESTED, NOT INHERITED\n")
    w("[STATE IT, AND NAME THE STRATUM ITS EVIDENCE COMES FROM. It may come back")
    w("refuted, split, reframed, moot, vindicated-by-its-own-escape-clause,")
    w("right-with-a-dropped-proviso, or inapplicable — all seven have happened")
    w("(`RESEARCH-ARC.md` §7). Also state where you expect to be wrong.]\n")
    w("## Deliverable and gates\n")
    w("[WHAT LANDS. Read-only draft outside the tree unless told otherwise.]")
    w("Every new claim carries a bracketed status with its obligation")
    w("(`[MEASURED]` names its driver, `[REFUTED]` its witness); a kill condition")
    w("naming a NUMBER carries its DERIVATION; caps are disclosed in-driver.")
    w("Before committing: `python3 notes/ledger.py --lint`, and")
    w("`notes/check-gapmap-cells.py` if the gap map changed.\n")
    text = "\n".join(out)
    if args.out:
        d = os.path.join(ROOT, "notes/pencil/rounds")
        os.makedirs(d, exist_ok=True)
        path = os.path.join(d, f"{tag}.md")
        open(path, "w", encoding="utf-8").write(text)
        print(f"wrote {os.path.relpath(path, ROOT)} "
              f"({len(text)} chars, ~{len(text)//4} tokens)")
    else:
        print(text)
    return 1 if miss else 0


# A verdict HINT normalizes onto the vocabulary only for the purpose of
# spotting disagreement. It never becomes a row's status.
_HINT_NORM = {"PROVEN": "PROVED", "PROVED": "PROVED", "FALSE": "REFUTED",
              "REFUTED": "REFUTED", "SUPERSEDED": "RETIRED",
              "RETIRED": "RETIRED", "MOOT": "MOOT", "DISCHARGED": "PROVED",
              "CLOSED": "PROVED", "FIRED": "", "OPEN": "OPEN"}


def head_status(rows):
    """(file, seckey, label) -> the group head's status, when the head has one.

    A very common shape here is one theorem written as a stem plus numbered
    conclusions: `(GR-61)`'s head is `[PROVED]` with body "Let `z` be
    admissible and `S` a chunk. Then", its tag saying "EVERY CLAUSE machine-
    asserted at 31 047 708 pairs", and its five clauses each carrying no tag.
    295 untagged rows are that shape -- they are not 295 unknowns, they are
    the conclusions of theorems whose status is stated one line above.

    This SURFACES the head's status; it never assigns it. Auto-inheritance
    would invent verdicts: `(BE-43)` has (i) and (ii) PROVED and (iii) reading
    "GAP (i) is NOT soft".
    """
    g = {}
    for r in rows:
        if not r["clause"] and r["status"] != "UNTAGGED":
            k = (r["file"], r["seckey"], r["label"])
            g.setdefault(k, (r["status"], r["claim"].strip()))
    return g


def stem_headed(rows):
    """Group keys whose tagged head is a bare HYPOTHESIS STEM, not its own
    claim -- so the clauses under it are that theorem's conclusions."""
    out = set()
    for k, (st, body) in head_status(rows).items():
        if len(body) < 80 or body.rstrip().endswith(("Then", "Then:", ":")):
            out.add(k)
    return out


def contested(rows):
    """label -> the disagreeing verdict signals carried by its rows.

    THE failure this exists for: `(FR-R1)` carries an early row tagged `open`
    and a later line reading `**(FR-R1) - PROVEN.**` with a 1976-site
    certificate. Before 2026-09-09 the later line was not indexed at all and
    `--label` answered a flat `[OPEN]` -- so an agent picking work from
    `--frontier` or `--status OPEN` would take a SOLVED problem as an open
    research target. Indexing it is only half the fix; the corpus genuinely
    holds both, and the honest behaviour is to SURFACE the disagreement rather
    than silently serve either one.
    """
    sig = {}
    for r in rows:
        sigs = sig.setdefault((r["label"], r["clause"]), set())
        if r["status"] != "UNTAGGED":
            sigs.add(r["status"])
        for h in (r.get("hint") or "").split():
            n = _HINT_NORM.get(h, "")
            if n:
                sigs.add(n)
    # Flag on EITHER of two shapes. (a) Genuinely disagreeing signals --
    # `(FR-R1)` OPEN vs PROVED. (b) A verdict word appearing on ONE row of a
    # multi-row label-clause while the others record none -- `(E-loc)`, whose
    # positive statement carries no status signal at all and whose refutation
    # sits three lines below it. Shape (b) is the more dangerous of the two,
    # because nothing about the positive row looks stale.
    nrows = collections.Counter((r["label"], r["clause"]) for r in rows)
    out = {}
    for k, v in sig.items():
        if len(v) > 1 or (v and nrows[k] > 1):
            out[k] = v
    return out


_HEADS = {}


def name(r):
    """Display name. The ordinal is shown when >1 because five label-clauses
    are stated TWICE in one section: without it a reader sees two rows with
    the same name and different text and cannot tell which is which."""
    occ = r.get("occ", "1")
    return (f"({r['label']})" + (f"({r['clause']})" if r["clause"] else "")
            + (f"#{occ}" if occ not in ("", "1") else ""))


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
    if r.get("hint"):
        print(f"    VERDICT WORD IN THE BOLD: {r['hint']}  "
              f"(a hint from the prose, NOT a status this tool assigns)")
    if r["status"] == "UNTAGGED" and r["clause"]:
        h = _HEADS.get((r["file"], r["seckey"], r["label"]))
        if h:
            print(f"    GROUP HEAD ({r['label']}) is [{h[0]}] — this clause may "
                  f"be covered by it; read the head, do not assume")
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
        print(f"no claim opener found for {args.label}.\n"
              f"That is not the same as 'no such label': a status stated in a "
              f"section's VERDICT BLOCK rather than in a `> **(LABEL)**` "
              f"blockquote is not indexed (e.g. `(S1)`). Read the owning "
              f"section, or `grep -rn '{args.label.strip('()')}' "
              f"notes/pencil/`.", file=sys.stderr)
        return 1
    allcon = contested(rows)
    con = set()
    for h in hits:
        con |= allcon.get((h["label"], h["clause"]), set())
    con = con or None
    if con:
        print(f"# !! CONTESTED: this label carries a verdict signal on some "
              f"rows and not others: {', '.join(sorted(con))}.\n"
              f"#    Read every row below before using any one of them — a "
              f"later row may supersede an earlier.\n")
    homes = {(h["file"], h["seckey"]) for h in hits}
    if len(homes) > 1:
        print(f"# NOTE: ({args.label.strip('()')}) is claimed in {len(homes)} "
              f"sections -- a collision the registry warns about "
              f"(notes/pencil/labels.md). All shown.\n")
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
    con = contested(rows)
    ncon = sum(1 for r in hits if (r["label"], r["clause"]) in con)
    print(f"# {len(hits)} claim(s) at [{want}]"
          + (f" in sections matching {args.section!r}" if args.section else "")
          + (f" -- {ncon} of them CONTESTED (another row disagrees; "
             f"marked !!)" if ncon else "") + "\n")
    for r in hits[:args.head]:
        if (r["label"], r["clause"]) in con:
            print(f"!! CONTESTED "
                  f"({', '.join(sorted(con[(r['label'], r['clause'])]))})")
        show(r, full=args.full, loc=False)
    if len(hits) > args.head:
        print(f"... {len(hits) - args.head} more (raise --head)")
    return 0


def cmd_frontier(rows, args):
    """Claims whose every known citation is closed -- split by whether this
    tool actually KNOWS the claim is open.

    The split is not cosmetic. `UNTAGGED` means "no machine-readable status",
    NOT "unproved" -- and 82% of this frontier was untagged when the split was
    added, so a single undifferentiated list was presenting *I don't know* as
    *this is ready to attack*. A reader could be handed a claim that is
    already proved and merely untagged; `(FR-R1)` is the worked example, where
    the corpus carries an exhaustive certificate the tag never recorded. The
    two groups take DIFFERENT next actions: the first is work, the second is a
    tagging decision that must precede work.
    """
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
    live = [t for t in out if t[1]["status"] != "UNTAGGED"]
    unknown = [t for t in out if t[1]["status"] == "UNTAGGED"]
    con = contested(rows)

    def emit(group, cap):
        for n, r in group[:cap]:
            if (r["label"], r["clause"]) in con:
                print(f"!! CONTESTED "
                      f"({', '.join(sorted(con[(r['label'], r['clause'])]))})")
            show(r, full=args.full, loc=False)
        if len(group) > cap:
            print(f"... {len(group) - cap} more (raise --head)\n")

    print(f"# Frontier: {len(out)} claim(s) whose every KNOWN citation is "
          f"closed.\n"
          f"# 'Closed' means the cited label carries a PROVED/REFUTED/MOOT/"
          f"RETIRED clause -- a claim by its author, not a check.\n")
    print(f"## KNOWN-OPEN — {len(live)} claim(s), status recorded and not "
          f"closed.\n## These are work.\n")
    emit(live, args.head)
    if args.known:
        print(f"## STATUS-UNKNOWN — {len(unknown)} further claim(s) hidden by "
              f"--known.\n##    Run without --known to see them.")
        return 0
    print(f"\n## STATUS-UNKNOWN — {len(unknown)} claim(s) carrying NO "
          f"machine-readable status.\n"
          f"## These are NOT known to be open: UNTAGGED means this tool cannot "
          f"tell, and\n## a claim here may already be settled in prose the tag "
          f"never recorded. The\n## next action is a TAGGING decision (read "
          f"the clause), not an attack on the\n## mathematics. `--known` "
          f"hides this group; `--backlog` ranks it.\n")
    emit(unknown, args.head)
    return 0


def cmd_cited_by(rows, args):
    """What cites this claim. Accepts a CLAUSE: `--cited-by '(BE-45)(ii)'`.

    The corpus qualifies thousands of its citations by clause, so a
    label-granular answer to "what breaks if this falls" is over-broad -- it
    returns everything citing any clause of the label.
    """
    q = args.cited_by.strip().strip("()")
    parts = q.split(")(")
    want, wclause = parts[0], (parts[1] if len(parts) > 1 else "")
    if wclause:
        key = f"{want}:{wclause}"
        hits = [r for r in rows if key in (r.get("citesq") or "").split(";")]
        print(f"# {len(hits)} claim(s) cite ({want})({wclause}) SPECIFICALLY "
              f"-- clause-granular, so this is what a change to THAT CLAUSE "
              f"reaches.\n")
    else:
        hits = [r for r in rows if want in r["cites"].split(";")]
        nq = len({c for r in rows
                  for c in (r.get("citesq") or "").split(";")
                  if c.startswith(want + ":")})
        print(f"# {len(hits)} claim(s) cite ({want}) -- what a change to it "
              f"reaches.\n"
              + (f"# {nq} of its clauses are cited BY NAME elsewhere; "
                 f"`--cited-by '({want})(ii)'` narrows to one.\n"
                 if nq else ""))
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
    key = lambda r: (r["file"], r["seckey"], r["label"], r["clause"], r["occ"])
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
    ident = lambda r: (r["label"], r["clause"], r["occ"])
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
        opened = loose = nonlabel = 0
        cur = ""
        for l in text.split("\n"):
            if l.startswith("## "):
                cur = ""
            m = OPENER.match(l) or OPENER_WIDE.match(l)
            if not m:
                continue
            if not LABELISH.match(m.group(1)):
                nonlabel += 1      # a parenthesised phrase, not a label
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
        frag = len([r for r in parse(rel, text, keep_fragments=True)
                    if _list_fragment(r)])
        print(f"{rel}\n   {cand:5d} blockquote lines containing '**('\n"
              f"   {opened:5d} match the opener shape (bold closes after the "
              f"label)\n   {loose:5d} unattached sub-item bullets (no parent "
              f"label in section; dropped)\n   {frag:5d} prose-list fragments "
              f"/ possessives (bolded label in prose; dropped)\n"
              f"   {nonlabel:5d} parenthesised phrases that are not labels "
              f"(dropped)\n   {got:5d} ledger rows")
        if got != opened - loose - frag:
            print(f"   !! {opened - loose - frag - got} opener(s) unaccounted for")
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
    # COVERAGE, checked against a signal independent of the opener regexes.
    # The old selftest only asked "did every line the regex matched become a
    # row?" -- circular, and it certified OK while `(BE-E4')` (193 corpus
    # mentions) and `(PENCIL-SATURATES)` (128) had NO row at all. This asks
    # the other question: which heavily-cited labels does the ledger not
    # index? A nonzero answer is not automatically a bug -- a status stated
    # in a section VERDICT BLOCK rather than a blockquote opener is out of
    # scope by design (e.g. `(S1)`) -- so it reports rather than fails.
    have = {r["label"] for r in rows}
    mentions = collections.Counter()
    for rel in SOURCES:
        try:
            t = open(os.path.join(ROOT, rel), encoding="utf-8").read()
        except OSError:
            continue
        secnames = set(re.findall(r"§\(([^)]+)\)", t))
        for lab in CITE.findall(t):
            if "-" in lab and lab not in secnames:
                mentions[lab] += 1
    gaps = [(n, l) for l, n in mentions.items() if l not in have and n >= 20]
    gaps.sort(reverse=True)
    print(f"\ncoverage: {len(have)} labels indexed; "
          f"{len(gaps)} label(s) mentioned 20+ times with NO row"
          + (" -- read each; a section-verdict-block status is out of scope"
             if gaps else ""))
    for n, l in gaps[:12]:
        print(f"   {n:4d} mentions  ({l})")

    con = contested(rows)
    print(f"\n{len(con)} label(s) CONTESTED (rows carrying disagreeing verdict "
          f"signals) -- --label flags each:")
    for (l, cl), v in sorted(con.items())[:10]:
        nm = f"({l})" + (f"({cl})" if cl else "")
        print(f"   {nm}: {', '.join(sorted(v))}")
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
    mode.add_argument("--round", metavar="N",
                      help="emit a dispatch briefing packet (with --brief)")
    mode.add_argument("--backlog", action="store_true",
                      help="UNTAGGED claims ranked by citations (slice 10's worklist)")
    mode.add_argument("--reserve", nargs="+", metavar="TOK",
                      help="0-hit check a proposed label prefix / section name")
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
    p.add_argument("--labels", nargs="+", metavar="L", default=[],
                   help="--round: the claims this direction rests on")
    p.add_argument("--direction", metavar="CODE", help="--round: direction code")
    p.add_argument("--question", metavar="TEXT", help="--round: the question")
    p.add_argument("--out", action="store_true",
                   help="--round: write notes/pencil/rounds/<N>-<DIR>.md")
    p.add_argument("--decisive", action="store_true",
                   help="--backlog: only untagged claims whose own clause "
                        "already contains a status word (transcription, not "
                        "judgement)")
    p.add_argument("--known", action="store_true",
                   help="--frontier: only claims with a recorded status; hide "
                        "the UNTAGGED group, which is a tagging decision "
                        "rather than work")
    p.add_argument("--strict", action="store_true",
                   help="--lint: also fail on a NEW claim left UNTAGGED")
    args = p.parse_args(argv)

    rows = load(rebuild=args.rebuild)
    _HEADS.update(head_status(rows))
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
    if args.backlog:
        return cmd_backlog(rows, args)
    if args.reserve:
        return cmd_reserve(rows, args)
    if args.round:
        return cmd_round(rows, args)
    if args.lint:
        return cmd_lint(rows, args)
    if args.list:
        return cmd_list(rows, args)
    if args.stats:
        return cmd_stats(rows, args)
    return cmd_selftest(rows, args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
