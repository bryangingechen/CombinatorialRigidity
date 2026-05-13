# blueprint/CLAUDE.md — agent operating manual for the blueprint

This file is the **agent-facing operating manual** for working on the
blueprint (the LaTeX/plastex doc under `blueprint/src/`). It is the
blueprint analogue of the top-level `CLAUDE.md`; the top-level one
covers Lean development.

Read this file when a session involves writing or revising blueprint
TeX — typically when a new phase lands and needs a chapter, or when an
existing chapter falls out of sync with the Lean.

For **workflow-mode discussion** (backfill vs forward, when to use
which, recommendation for Phase 6), see `blueprint/DESIGN.md`. This
file carries operational rules; `DESIGN.md` carries the rationale.

## Reading order

At session start, in order:

1. **This file** — process and authoring conventions.
2. **`blueprint/DESIGN.md`** — current workflow mode, selectivity
   rationale, open questions. Skim once per project; re-read when the
   workflow mode for a phase is under discussion.
3. **`../ROADMAP.md`** — what's done, what's mid-stream, which phase
   the new chapter (if any) corresponds to.
4. **`../notes/PhaseN.md`** for the chapter being written — gives the
   lemma checklist, definitions, decisions made during the phase.
5. **The Lean files themselves** for the relevant phase (skim doc-
   comments, file headers, and main lemma statements). Doc-comments
   often already contain the prose proof or rationale, ready to be
   adapted.
6. **Existing chapters** under `src/chapter/` — match their style.
   `chapter/sparsity.tex` is the canonical model for a Phase 1-style
   chapter (multiple sections + subsections, mix of definitions /
   lemmas / a theorem at the end).

## Authoring conventions (carleson-style)

The blueprint follows the convention used by
[fpvandoorn/carleson](https://github.com/fpvandoorn/carleson/blob/master/blueprint/src/)
and other leanblueprint projects. Key rules:

### Annotation order inside each environment

```latex
\begin{lemma}[Short descriptive title]
  \label{lem:my-lemma}
  \lean{Namespace.my_lemma}
  \leanok
  \uses{def:foo, lem:bar}
  Statement of the lemma, in mathematical English.
\end{lemma}
\begin{proof}
  \leanok
  \uses{lem:helper-used-in-proof-only}
  One- to three-sentence mathematical proof, in English.
\end{proof}
```

- `\label{...}` first; everything else cross-references it.
- `\leanok` says "this is formalized in Lean."
- `\lean{Fully.Qualified.Name}` links to the API docs. May contain
  multiple comma-separated names for group lemmas (e.g. corner
  cases).
- `\uses{...}` on the **statement** declares the dependencies of the
  statement; `\uses{...}` on the **proof** declares dependencies of
  the argument. The dep-graph distinguishes them.
- Always write a prose proof alongside `\leanok` — don't degenerate
  to leanok-only stubs. The dep-graph is the formal map; the prose
  is the human map.

### Label prefixes

Use semantic prefixes consistently:
- `def:` for definitions
- `lem:` for lemmas
- `thm:` for theorems
- `cor:` for corollaries
- `prop:` for propositions
- `sec:` for sections

This makes `\Cref{}` output read naturally
("Definition 1.2", "Lemma 3.4") thanks to `cleveref`.

### Cross-references

Use `\cref{...}` / `\Cref{...}` (cleveref), never bare `\ref`. Both
`print.tex` and `web.tex` load cleveref with `capitalize`, so
`\Cref{lem:foo}` produces "Lemma 1.2" with the right capitalization.

### What to include vs. skip

**Be selective.** The blueprint is a reader's doc for a human
audience, not a 1:1 mirror of the Lean. A typical Lean file has
many small declarations that don't merit a blueprint entry. The
default presumption is *exclude*; only include declarations that
clear one of the bars below.

- **Include**:
  - Definitions of project-level concepts (`IsSparse`, `IsLaman`,
    `IsTight`, `IsTightOn`, etc.).
  - Theorems that a reader would name out loud
    (e.g. "Laman's theorem", "tight-subset union closure").
  - Lemmas with non-trivial mathematical content used at a phase
    boundary or feeding a main theorem.
- **Skip**:
  - Pure tautologies that follow immediately from a definition
    (e.g. `edgesIn_subset_edgeSet` is just `A ∩ B ⊆ A`).
  - Constructors / accessors whose only job is to absorb
    `Sym2`-membership or And-projection boilerplate
    (e.g. `mk_mem_edgesIn`, `IsLaman.isSparse`,
    `IsLaman.edgeSet_ncard`). The fact they prove is already legible
    from the type signature.
  - Mirror lemmas under `CombinatorialRigidity/Mathlib/` — these are
    upstream-eligible facts about `Sym2`, `Set.ncard`, etc., not
    project results. They belong upstream, not in the blueprint.
  - Small bridge / glue lemmas whose names or statements are likely
    to change as the API stabilizes. These are also the highest-
    churn artefacts, and blueprinting them means re-editing the
    blueprint on every Lean refactor.
- **Group**: closely related corner cases under one `\begin{lemma}`
  with multiple comma-separated names in `\lean{...}` (see
  `lem:edgesIn-corners` in `sparsity.tex`).
- **Phase-N-prep lemmas that live in Phase-M files** still belong
  in the chapter for **file M**, not phase N. The blueprint reader
  cares about the formal landscape (which file holds what), not
  about which agent-session added a given lemma.

Heuristic that captures most of the above: *if the lemma's name or
statement is likely to change as the API stabilizes, that's a sign
it's churn-prone internal infrastructure — skip it.* See
`blueprint/DESIGN.md` for the rationale.

### Proof verbosity

Match the carleson style: one to three sentences, in English, that
gesture at the argument without trying to be exhaustive. A reader who
wants the full proof clicks through to the Lean. Examples in
`sparsity.tex`:
- Trivial: "Immediate from the definition."
- Short: "An edge has both endpoints in $\{v\}^c$ exactly when neither
  endpoint equals $v$ ..."
- Multi-step: the proof of `thm:isTightOn-union-inter` is the most
  detailed in the chapter and runs ~10 lines.

If the Lean proof is gnarly enough that the prose version would be
multi-paragraph, consider whether the blueprint should record a
*simpler* mathematical proof instead (the Lean proof may have
absorbed implementation noise that doesn't belong in the doc).

## Static checks before commit

Run these from `blueprint/src/`. They catch the failure modes that
the plastex build would catch later, but faster.

**All `\lean{...}` names resolve to real Lean declarations:**

```sh
grep -hoE '\\lean\{[^}]+\}' chapter/*.tex \
  | sed 's/\\lean{//;s/}$//' | tr ',' '\n' | sed 's/^ *//;s/ *$//' \
  | sort -u > /tmp/lean-names.txt
# Then for each name in /tmp/lean-names.txt, grep the corresponding
# basename in the relevant Lean file under ../../CombinatorialRigidity/.
```

**All `\uses{...}` and `\Cref{...}` labels are defined:**

```sh
grep -hoE '\\label\{[^}]+\}' chapter/*.tex | sed 's/\\label{//;s/}$//' \
  | sort > /tmp/labels.txt
grep -hoE '\\uses\{[^}]+\}' chapter/*.tex | sed 's/\\uses{//;s/}$//' \
  | tr ',' '\n' | sed 's/^ *//;s/ *$//' | sort -u > /tmp/uses.txt
comm -23 /tmp/uses.txt /tmp/labels.txt   # should be empty
```

Same idea for `\Cref{...}` / `\cref{...}`. Any output from `comm -23`
is a broken reference.

## Local build

The blueprint builds in two formats:
- **Web** (HTML + dep-graph) via plastex — primary; what CI deploys.
- **Print** (PDF) via xelatex — secondary.

### One-time setup

System dependencies (macOS, Apple Silicon assumed):

```sh
brew install graphviz                    # for pygraphviz
brew install --cask basictex             # for xelatex (~80 MB)
eval "$(/usr/libexec/path_helper)"       # add TeX to PATH this shell
sudo tlmgr update --self
sudo tlmgr install latexmk preview xkeyval \
  enumitem tikz-cd thmtools cleveref     # required by print.tex (inv bp)
```

Python venv (kept under `blueprint/.venv`, gitignored):

```sh
cd blueprint
python3 -m venv .venv
source .venv/bin/activate

# pygraphviz needs the brew-installed graphviz headers; pip won't
# find them on Apple Silicon without explicit flags:
CPPFLAGS="-I$(brew --prefix graphviz)/include" \
LDFLAGS="-L$(brew --prefix graphviz)/lib" \
  pip install pygraphviz

pip install -r requirements.txt          # plastex, leanblueprint, invoke
```

### Running builds

From `blueprint/`, with the venv activated:

```sh
inv web        # plastex → blueprint/web/index.html + dep_graph_document.html
inv bp         # latexmk drives xelatex to convergence → blueprint/print/print.pdf
inv serve      # preview the web build at http://localhost:8000
```

After `inv web`, **open `blueprint/web/dep_graph_document.html`** in a
browser. This is the unique value-add over plain LaTeX: every node
should be green (formalized) for completed phases, with edges showing
the `\uses{}` dependencies. A missing or red node is the signal
something's off — a typo in `\lean{...}`, a missing `\leanok`, or a
broken `\uses{...}`.

### CI

CI runs the same builds via `leanprover-community/docgen-action` —
see `.github/workflows/push.yml` (master push, deploys) and
`push_pr.yml` (PRs, no deploy). The blueprint job runs alongside the
Lean build and the upstreaming dashboard; a TeX or `\lean{...}` error
fails the whole pipeline.

## File layout

```
blueprint/
├── CLAUDE.md            ← this file (operating manual)
├── DESIGN.md            ← workflow-mode rationale, open questions
├── .gitignore           ← build artefacts + .venv/
├── requirements.txt     ← plastex / leanblueprint / invoke pins
├── tasks.py             ← invoke targets: web / bp / serve
└── src/
    ├── web.tex          ← entry for plastex (HTML + dep-graph)
    ├── print.tex        ← entry for xelatex (PDF)
    ├── bibliography.bib ← project references
    ├── extra_styles.css ← web-only style overrides
    ├── plastex.cfg      ← plastex configuration
    ├── latexmkrc        ← latexmk configuration
    ├── preamble/
    │   ├── common.tex   ← macros and theorem envs shared by both
    │   ├── print.tex    ← print-only packages and overrides
    │   └── web.tex      ← web-only packages and overrides
    └── chapter/
        ├── main.tex     ← top-level `\input{}` orchestration
        ├── intro.tex    ← project introduction (phase plan, reading
        │                  guide, hyperlinks to live docs)
        └── sparsity.tex ← Phase 1 chapter (canonical example)
```

### Adding a new chapter

1. Create `src/chapter/phaseName.tex`. Use `sparsity.tex` as the
   structural template.
2. Add an `\input{chapter/phaseName.tex}` line to `chapter/main.tex`
   (uncomment the placeholder that already exists for the phase).
3. Re-run `inv web` and check the dep-graph — the new chapter's
   nodes should connect cleanly to earlier chapters' nodes.

In **backfill mode** (the default; Phases 1–5), each entry carries
`\lean{...}` and `\leanok` from the start and the new chapter's
dep-graph nodes should be all green when committed.

In **forward mode** (proposed for Phase 6; see `blueprint/DESIGN.md`),
the same recipe applies, but:
- Omit `\lean{...}` and `\leanok` in each entry — they get added
  as Lean lemmas land in subsequent sessions.
- Prose proofs can be one-line gestures at this stage; flesh out
  during the phase-end pass.
- `\uses{...}` chains should still reflect the intended proof
  dependency structure — they're the point of forward mode.
- The dep-graph will be mostly red on first build; that's the
  to-do list.

### Macros

Live in `preamble/common.tex`. Current set is intentionally minimal
(`\edgesIn`, `\rk`, `\KK`, plus the usual `\N`, `\Z`, `\Q`, `\R`).
When a chapter wants a recurring piece of notation, add a macro
there rather than inline-redefining per chapter.

The `\edgesIn` macro takes an optional graph argument:
`\edgesIn{S}` produces $E_G[S]$, `\edgesIn[H]{S}` produces $E_H[S]$.
The default-`G` form is right ~95% of the time; reach for the
optional form only when transporting along isomorphisms or
otherwise comparing two graphs.

### Bibliography

Entries go in `src/bibliography.bib`. Cite with `\cite{key}`. The
existing entries (`laman1970`, `henneberg1911`,
`graverServatiusServatius1993`) are the project's canonical
references.

## Pitfalls

- **plastex emits warnings, not errors, on unknown commands.**
  `\github`, `\dochome`, etc. produce warnings when run outside a
  build that loads the blueprint plastex plugin. These are harmless
  in normal `inv web` runs but can mask real warnings — skim the
  console output, not just the exit code.
- **`_` in `\texttt{...}`.** LaTeX still treats `_` as a subscript
  inside `\texttt{...}`. Escape as `\_` (e.g.
  `\texttt{mk\_mem\_edgesIn}`) or use `\verb|...|`.
- **`\lean{Name1, Name2}` with multiple names** is fine for the
  HTML build (each links separately) but produces only one link
  target in the PDF. Reserve multi-name `\lean{}` for closely-
  related corner cases the reader genuinely thinks of as a unit.
- **No `.md` interference.** plastex parses only what `web.tex`
  `\input{}`s. xelatex parses only what `print.tex` `\input{}`s.
  Adding `.md` files anywhere under `blueprint/` is safe.
- **Python 3.9 quirks.** Recent `leanblueprint` releases sometimes
  require 3.10+. If you hit `SyntaxError` or `ImportError` after a
  `pip install -r requirements.txt`, the fix is usually
  `python3.12 -m venv .venv` and reinstall.

## Friction review (mandatory at end of session)

Same idea as the top-level `CLAUDE.md`'s friction review, narrowed to
the blueprint. The bar and destination depend on the workflow mode
(see `DESIGN.md` for the modes themselves):

- **Backfill mode** — friction is mostly TeX-level (macro behaviour,
  `\texttt{}` quoting, plastex warnings). Capture it in **this file**
  under "Pitfalls" or "Local build"; it doesn't cross-cut the rest
  of the project.
- **Forward mode** — friction can be structurally meaningful (the
  dep-graph encodes the proof plan). Cross-cutting items belong in
  `../notes/FRICTION.md` tagged `[blueprint]`.

Concrete questions, in either mode:

1. **Did any TeX construct fight you?** Macro that didn't behave as
   expected, an `\input{}` boundary that broke a numbering scheme, a
   plastex/leanblueprint quirk. Almost always: update this CLAUDE.md
   under Pitfalls.
2. **Did the dep-graph reveal a structural gap?** A `\uses{}` chain
   that's longer than the math actually needs, an orphan node, a
   cycle, a node that should really be split. Backfill: fix in this
   commit. Forward: fix or file a note — the dep-graph IS the plan,
   so an unexamined gap is technical debt.
3. **Did selection feel arbitrary?** If you spent time deciding
   whether a given Lean lemma deserves a blueprint entry, write the
   criterion you ended up using as a one-line note in this file
   under "Authoring conventions → What to include vs. skip". The
   next agent shouldn't relitigate the same call.

No new entries this session is fine — but only after you've checked.
