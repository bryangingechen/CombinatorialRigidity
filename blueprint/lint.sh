#!/usr/bin/env bash
#
# blueprint/lint.sh — the fast static reference checks as one command.
#
# Runs the three grep/awk-scriptable gates documented in
# blueprint/CLAUDE.md *Static checks before commit*:
#
#   1. Every \uses{...} and \cref/\Cref{...} target has a \label{...}.
#   2. Every \cite{...} key has a bibliography.bib entry, and every
#      bib entry is cited somewhere.
#   3. Supersession gate: no live (non-superseded) node's \uses{...}
#      reaches a node whose environment title carries `superseded`.
#   4. Hanging-pin gate: no theorem-like node carries a statement \leanok
#      without a \lean{...} pin (an uncheckable "green" — checkdecls only
#      verifies names that ARE pinned, so this class slips through it).
#   5. Vocabulary gate (Phase 23-cleanup P1): no banned project-internal
#      process vocabulary (brick/motive/producer/stratum/green-modulo,
#      any Phase~N/Phase-N self-description outside chapter/intro.tex, raw
#      Lean hypothesis names in a statement block) — see the check's own
#      header comment below for the full rationale and carve-outs.
#   6. Multi-label \cref{a,b} guard (Phase23-cleanup #5 / Phase26-cleanup
#      B3, extended multi-line-aware in B5): plastex's cleveref shim
#      resolves \cref{...}'s whole argument as one \idref lookup — it has
#      no comma-list parsing, unlike real LaTeX cleveref — so \cref{a,b}
#      silently renders as the literal string "??" in the web build
#      (checkdecls/lean_verify don't cover prose, so nothing else catches
#      it). Write each label as its own \cref{a} and \cref{b} instead. The
#      check joins any `%`-continued line (TeX's "no newline" idiom) with
#      its successor before matching, so a \cref{a,b,%<newline>c} spanning
#      two source lines is caught too (B5's case-iii.tex:789-790 slipped
#      past the original single-line-only grep).
#   7. Subsubsection-cref guard (Phase26-cleanup B4): the web build's
#      secnumdepth excludes \subsubsection headings from numbering, so a
#      \cref/\Cref/\ref/\S\ref to a \subsubsection-level \label renders
#      "??" regardless of single/multi-label syntax — a distinct root
#      cause from check 6's bug, same visible symptom. Name the target in
#      prose instead of cross-referencing it numerically.
#
# Needs no venv / TeX / lake — pure text checks, runs in well under a
# second. It does NOT replace verify.sh (inv bp + inv web +
# checkdecls), nor the by-eye honesty gate on \leanok additions.
#
# Run from anywhere; exits non-zero with the offending names on the
# first failing check.

set -euo pipefail

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SRC="$SCRIPT_DIR/src"
cd "$SRC"

# Collect chapter TeX files (recursively under chapter/).
TEXFILES="$(find chapter -name '*.tex' | sort)"
if [ -z "$TEXFILES" ]; then
    echo "lint.sh: no chapter/*.tex files found under $SRC" >&2
    exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
FAIL=0

# shellcheck disable=SC2086
{ grep -hoE '\\label\{[^}]+\}' $TEXFILES | sed 's/\\label{//;s/}$//' || true; } \
    | sort -u > "$TMP/labels.txt"

# --- 1. \uses and \cref/\Cref resolution -------------------------------
# shellcheck disable=SC2086
{ grep -hoE '\\uses\{[^}]+\}' $TEXFILES | sed 's/\\uses{//;s/}$//' || true; } \
    | tr ',' '\n' | sed 's/^ *//;s/ *$//' | sort -u > "$TMP/uses.txt"
# shellcheck disable=SC2086
{ grep -hoiE '\\cref\{[^}]+\}' $TEXFILES | sed -E 's/\\[cC]ref\{//;s/}$//' || true; } \
    | tr ',' '\n' | sed 's/^ *//;s/ *$//' | sort -u > "$TMP/crefs.txt"

UNDEF_USES="$(comm -23 "$TMP/uses.txt" "$TMP/labels.txt")"
UNDEF_CREFS="$(comm -23 "$TMP/crefs.txt" "$TMP/labels.txt")"
if [ -n "$UNDEF_USES$UNDEF_CREFS" ]; then
    echo "lint.sh: \\uses / \\cref targets with no \\label:" >&2
    printf '%s\n%s\n' "$UNDEF_USES" "$UNDEF_CREFS" | grep -v '^$' | sed 's/^/  /' >&2
    FAIL=1
fi

# --- 2. \cite keys vs bibliography.bib ---------------------------------
if [ -f bibliography.bib ]; then
    # shellcheck disable=SC2086
    { grep -hoE '\\cite(\[[^]]*\])?\{[^}]+\}' $TEXFILES || true; } \
        | sed -E 's/\\cite(\[[^]]*\])?\{//;s/}$//' | tr ',' '\n' | sed 's/^ *//;s/ *$//' \
        | sort -u > "$TMP/cite-keys.txt"
    { grep -hoE '^@[a-zA-Z]+\{[^,]+' bibliography.bib | sed 's/^@[a-zA-Z]*{//' || true; } \
        | sort -u > "$TMP/bib-keys.txt"
    MISSING="$(comm -23 "$TMP/cite-keys.txt" "$TMP/bib-keys.txt")"
    UNUSED="$(comm -13 "$TMP/cite-keys.txt" "$TMP/bib-keys.txt")"
    if [ -n "$MISSING" ]; then
        echo "lint.sh: \\cite keys with no bib entry:" >&2
        echo "$MISSING" | sed 's/^/  /' >&2
        FAIL=1
    fi
    if [ -n "$UNUSED" ]; then
        echo "lint.sh: bib entries never cited:" >&2
        echo "$UNUSED" | sed 's/^/  /' >&2
        FAIL=1
    fi
fi

# --- 3. Supersession gate ----------------------------------------------
# Stage 1 — superseded labels (the environment title carries the
# `superseded` marker; the project's invariant is that \label{} sits on
# the line after \begin{...}[...]).
# shellcheck disable=SC2086
awk 'BEGIN{IGNORECASE=1}
 /\\begin\{(lemma|theorem|proposition|corollary|definition)\}\[/{e=1;s=($0~/superseded/)}
 e&&/\\label\{/{if(s){match($0,/\\label\{[^}]+\}/);l=substr($0,RSTART,RLENGTH);
   gsub(/\\label\{|\}/,"",l);print l} e=0;s=0}' $TEXFILES \
 | sort -u > "$TMP/sup-labels.txt"
# Stage 2 — labels reached by a \uses of a NON-superseded env (statement
# or proof; \uses bodies may wrap, so accumulate to the closing }). A
# \begin[...] resets the live flag; a \begin{proof} (no [title])
# inherits the preceding env's flag.
# shellcheck disable=SC2086
awk 'BEGIN{IGNORECASE=1;live=1;u=0}
 /\\begin\{(lemma|theorem|proposition|corollary|definition)\}\[/{live=($0!~/superseded/);u=0;b=""}
 {ln=$0; if(u)b=b ln; else{i=index(ln,"\\uses{"); if(i>0){u=1;b=substr(ln,i+6)}}
  if(u){j=index(b,"}"); if(j>0){body=substr(b,1,j-1);u=0;b="";
   if(live){n=split(body,a,",");for(k=1;k<=n;k++){gsub(/[ \t\r\n]/,"",a[k]);
     if(a[k]!="")print a[k]}}}}}' $TEXFILES \
 | sort -u > "$TMP/live-uses.txt"

VIOLATIONS="$(comm -12 "$TMP/sup-labels.txt" "$TMP/live-uses.txt")"
if [ -n "$VIOLATIONS" ]; then
    echo "lint.sh: live nodes \\uses-depend on superseded nodes:" >&2
    echo "$VIOLATIONS" | sed 's/^/  /' >&2
    FAIL=1
fi

# --- 4. Hanging-pin gate: \leanok statement with no \lean{} ------------
# A theorem-like node marked formalized (\leanok on the statement) must
# pin to a real declaration (\lean{...}); otherwise checkdecls cannot
# verify it (it checks only names that ARE pinned) — an uncheckable
# "green" that falls through every other gate. The statement block runs
# from \begin{env} to the node's \begin{proof} or \end{env}; a \leanok on
# the proof is separate and not counted here.
# shellcheck disable=SC2086
awk '
 /\\begin\{(lemma|theorem|proposition|corollary|definition)\}/{
   inenv=1;haveok=0;havelean=0;lab="";
   if($0~/\\leanok/)haveok=1; if($0~/\\lean\{/)havelean=1; next}
 inenv&&(/\\begin\{proof\}/||/\\end\{(lemma|theorem|proposition|corollary|definition)\}/){
   if(haveok&&!havelean)print (lab==""?"(unlabeled)":lab);
   inenv=0;haveok=0;havelean=0;lab="";next}
 inenv{
   if($0~/\\leanok/)haveok=1; if($0~/\\lean\{/)havelean=1;
   if(match($0,/\\label\{[^}]+\}/)){lab=substr($0,RSTART,RLENGTH);gsub(/\\label\{|\}/,"",lab)}}
 ' $TEXFILES | sort -u > "$TMP/hanging.txt"
if [ -s "$TMP/hanging.txt" ]; then
    echo "lint.sh: \\leanok nodes with no \\lean{} pin (uncheckable green):" >&2
    sed 's/^/  /' "$TMP/hanging.txt" >&2
    FAIL=1
fi

# --- 5. Vocabulary gate (P1, Phase 23-cleanup) --------------------------
# Blueprint prose should read as mathematics for a rigidity theorist who
# knows Katoh--Tanigawa 2011, not as an internal project-process log
# (AUTHORING.md *Audience & vocabulary*, the terminology dictionary).
# Three static sub-checks:
#
# 5a. Banned project-internal words: brick, motive, producer(s), stratum,
#     strata, green-modulo (AUTHORING.md's terminology dictionary gives
#     the plain-math replacement for each). Matched case-insensitively
#     (catches `GREEN-modulo`) and only when NOT immediately adjacent, on
#     either side, to a word character, `-`, `_`, `:`, or `.` on the left
#     / a word character, `-`, or `_` on the right --- the separators
#     used inside \label{}/\lean{}/\cref{}/\uses{} identifier tokens
#     (e.g. `lem:theorem-55-base-producer`, `theorem_55_base_producer_gen`).
#     This plain-adjacency test (rather than tracking which command's
#     argument a line sits in) also correctly skips a continuation line
#     of a multi-line \uses{...} list, which carries no \uses{ literal of
#     its own to key on. `.` is excluded only on the left (dotted Lean
#     namespace paths), not the right, so an ordinary sentence-final
#     period after a banned word ("...the producer.") still matches.
# 5b. Phase self-description (ANY `Phase~N` / `Phase-N`, whitespace- or
#     hyphen-separated; sub-phase codes `22a`-`22l` / `23a`-`23l`):
#     banned in every chapter file EXCEPT chapter/intro.tex, whose
#     "Organization of the blueprint" section is a deliberate,
#     reader-facing phase-numbered table of contents (blueprint/CLAUDE.md
#     *File layout*: "the four-arc organization + per-phase one-liner"),
#     not the process self-description ("Phase~19", "third stratum", a
#     standalone "Status." paragraph) that principle F (AUTHORING.md)
#     bars from the individual math chapters. (The gate originally
#     matched only `Phase~17`..`Phase~29`, the range the molecular-program
#     rot accumulated in; it was generalized to any phase number, and to
#     the hyphenated `Phase-N` form, when the non-molecular chapters were
#     swept --- sub-17 `Phase~N` process pointers were invisible to the
#     narrower form.)
# 5c. Raw Lean hypothesis names (`\mathtt{hfoo}`) inside a node's
#     STATEMENT block (the "carry"/"adjudicated carry" pattern the
#     terminology dictionary retires) --- scoped like check 4's
#     \begin{env} .. \begin{proof}/\end{env} tracking, since a proof's
#     own narrative may legitimately name an internal identifier once
#     when explaining a Lean-side mechanism, but a *statement* never
#     should.
#
# chapter/retrospective.tex (the Phase-29 appendix, "Notes on the
# formalization") is exempt from 5a and 5b for the same reason intro.tex
# is exempt from 5b: it is the one deliberate, reader-facing exception to
# this whole gate (blueprint/CLAUDE.md *The retrospective appendix*) ---
# its subject is the project's own process, so "motive"/"producer" and
# phase numbers are first-class mathematical content there, not leakage
# into the rest of the blueprint's math prose. 5c is untouched: the
# appendix uses no lemma/theorem/proposition/corollary/definition
# environments, so it is naturally out of that check's scope already.
#
# Retained-with-marker superseded nodes (rigidity-matrix.tex's
# lem:rank-polynomial-IH-relabel, molecular-induction.tex's
# lem:chain-data-of-noRigid) are deliberately NOT exempt from 5a/5b/5c:
# the D1 retain-with-marker convention (blueprint/CLAUDE.md *supersession
# gate*) requires a retained node to already read in Target style, with
# only the environment title's literal `superseded` marker special-cased
# (by check 3 above) --- it is a plain-English "retained for the record"
# note, not a verbatim historical dump exempt from the readability bar.
# Both current retained nodes already meet 5a/5b/5c cleanly.

APPENDIX_TEXFILE='chapter/retrospective.tex'
NOAPPENDIX_TEXFILES="$(printf '%s\n' $TEXFILES | grep -v "^${APPENDIX_TEXFILE}\$" || true)"

VOCAB_WORDS='brick|motive|producers?|stratum|strata|green-modulo'
# shellcheck disable=SC2086
{ grep -inE "(^|[^A-Za-z0-9_:.-])($VOCAB_WORDS)(\$|[^A-Za-z0-9_-])" $NOAPPENDIX_TEXFILES || true; } \
    > "$TMP/vocab-words.txt"
if [ -s "$TMP/vocab-words.txt" ]; then
    echo "lint.sh: banned project-internal vocabulary (AUTHORING.md terminology dictionary):" >&2
    sed 's/^/  /' "$TMP/vocab-words.txt" >&2
    FAIL=1
fi

NOINTRO_TEXFILES="$(printf '%s\n' $NOAPPENDIX_TEXFILES | grep -v '^chapter/intro\.tex$' || true)"
# shellcheck disable=SC2086
{ grep -noE '[Pp]hases?[-~ ][0-9]|\b2[23][a-l]\b' $NOINTRO_TEXFILES || true; } \
    > "$TMP/vocab-phase.txt"
if [ -s "$TMP/vocab-phase.txt" ]; then
    echo "lint.sh: phase self-description outside chapter/intro.tex:" >&2
    sed 's/^/  /' "$TMP/vocab-phase.txt" >&2
    FAIL=1
fi

# shellcheck disable=SC2086
awk '
 /\\begin\{(lemma|theorem|proposition|corollary|definition)\}/{inenv=1;lab="";next}
 inenv&&(/\\begin\{proof\}/||/\\end\{(lemma|theorem|proposition|corollary|definition)\}/){inenv=0;lab="";next}
 inenv{
   if(match($0,/\\label\{[^}]+\}/)){lab=substr($0,RSTART,RLENGTH);gsub(/\\label\{|\}/,"",lab)}
   if(match($0,/\\mathtt\{h[A-Za-z0-9]+\}/))
     print FILENAME":"FNR" [" (lab=="" ? "unlabeled" : lab) "] " $0
 }' $TEXFILES > "$TMP/vocab-rawhyp.txt"
if [ -s "$TMP/vocab-rawhyp.txt" ]; then
    echo "lint.sh: raw Lean hypothesis name (\\mathtt{h...}) in a statement block:" >&2
    sed 's/^/  /' "$TMP/vocab-rawhyp.txt" >&2
    FAIL=1
fi

# --- 6. Multi-label \cref{a,b} guard (multi-line-aware) -----------------
# Joins a `%`-terminated line with its successor (TeX's line-continuation
# idiom: a trailing `%` swallows the newline, gluing the next line's
# content directly on) before matching, so a \cref{a,b,%\nc} split across
# a `%`-continuation is caught the same as a same-line \cref{a,b}.
# shellcheck disable=SC2086
awk '
  FNR==1{
    if (buf!="") { emit(prevfile) }
    buf=""; startline=0; prevfile=FILENAME
  }
  {
    if (buf=="") startline=FNR
    line=$0
    if (line ~ /%[ \t]*$/) {
      sub(/%[ \t]*$/, "", line)
      buf = buf line
      prevfile=FILENAME
      next
    } else {
      buf = buf line
      emit(FILENAME)
      buf=""
    }
  }
  function emit(fn,   pos, rest, m) {
    rest = buf
    pos = startline
    while (match(rest, /\\[cC]ref\{[^}]*,[^}]*\}/)) {
      m = substr(rest, RSTART, RLENGTH)
      print fn ":" pos ": " m
      rest = substr(rest, RSTART+RLENGTH)
    }
  }
  END { if (buf!="") emit(prevfile) }
' $TEXFILES > "$TMP/multi-cref.txt"
if [ -s "$TMP/multi-cref.txt" ]; then
    echo "lint.sh: multi-label \\cref{a,b} renders as \"??\" under plastex (write \\cref{a} and \\cref{b}):" >&2
    sed 's/^/  /' "$TMP/multi-cref.txt" >&2
    FAIL=1
fi

# --- 7. Subsubsection-cref guard ----------------------------------------
# Detect \subsubsection-level labels by the project's own on-its-own-line
# invariant (mirrors check 3's \begin{...}[title] one): a \label{...} that
# is the sole content of the first non-blank line after a (possibly
# multi-line) \subsubsection{...} title is that heading's label. Brace
# depth is tracked to skip past a multi-line title before looking for the
# label line.
# shellcheck disable=SC2086
NONUM_LABELS="$(awk '
  /\\subsubsection\{/{
    depth = gsub(/\{/,"{") - gsub(/\}/,"}")
    mode = (depth > 0) ? 1 : 2
    next
  }
  mode==1{
    depth += gsub(/\{/,"{") - gsub(/\}/,"}")
    if (depth <= 0) mode = 2
    next
  }
  mode==2{
    if ($0 ~ /^[ \t]*$/) next
    if ($0 ~ /^[ \t]*\\label\{[^}]+\}[ \t]*$/) {
      l = $0; sub(/^[ \t]*\\label\{/,"",l); sub(/\}[ \t]*$/,"",l); print l
    }
    mode = 0
  }
' $TEXFILES | sort -u)"
if [ -n "$NONUM_LABELS" ]; then
    # shellcheck disable=SC2086
    { grep -hoiE '\\[cC]ref\{[^}]+\}' $TEXFILES || true; } \
        | sed -E 's/\\[cC]ref\{//;s/}$//' | tr ',' '\n' | sed 's/^ *//;s/ *$//' > "$TMP/subsub-refs.txt"
    # shellcheck disable=SC2086
    { grep -hoE '\\ref\{[^}]+\}' $TEXFILES || true; } \
        | sed -E 's/\\ref\{//;s/}$//' >> "$TMP/subsub-refs.txt"
    REFS_TO_NONUM="$(sort -u "$TMP/subsub-refs.txt" | comm -12 - <(printf '%s\n' "$NONUM_LABELS"))"
    if [ -n "$REFS_TO_NONUM" ]; then
        echo "lint.sh: \\cref/\\ref to an unnumbered \\subsubsection label (renders \"??\" — name the target in prose instead):" >&2
        echo "$REFS_TO_NONUM" | sed 's/^/  /' >&2
        FAIL=1
    fi
fi

if [ "$FAIL" -ne 0 ]; then
    echo "blueprint/lint.sh: FAILED." >&2
    exit 1
fi
echo "blueprint/lint.sh: all static reference checks passed."
