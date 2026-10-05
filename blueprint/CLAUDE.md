# blueprint/CLAUDE.md — agent operating manual for the blueprint

The **agent-facing operating manual** for the blueprint (the LaTeX/plastex
document under `blueprint/src/`). It auto-loads whenever a session reads
**anything** under `blueprint/`, a one-line `\leanok` flip included, so it
carries only the every-touch mechanics: node annotation, the static checks,
builds and file layout. Its siblings cover the rest: `../CLAUDE.md` (root,
always loaded) project-wide process, `../CombinatorialRigidity/CLAUDE.md` Lean
source ops, `../notes/CLAUDE.md` notes discipline.

Read on demand, not auto-loaded:

- **`AUTHORING.md`**: the prose and editorial conventions (label prefixes,
  citations, what to include, proof verbosity, audience and vocabulary, the
  retrospective appendix). Read it when writing or revising chapter prose.
- **`DESIGN.md`**: the rationale (backfill vs forward mode, selectivity) and
  the static checks' calibration cases. Re-read it when a phase's workflow
  mode is under discussion.
- **`RENDERING.md`**: rendering and previewing locally.
  **`SETUP-AND-PITFALLS.md`**: one-time setup and build pitfalls.

## Reading order

When writing a chapter (a forward-mode pin or `\leanok` flip needs only this
file):

1. This file, then `AUTHORING.md`.
2. `../ROADMAP.md` and the phase's `../notes/PhaseN.md`: what the chapter
   covers, and the decisions made.
3. The phase's Lean files: file headers, main statements and doc-comments,
   which often already hold the prose proof or rationale.
4. Existing chapters under `src/chapter/`: match their style.
   `chapter/sparsity.tex` is the canonical model of a chapter's structure.

## Authoring conventions (carleson-style)

The blueprint follows the convention of
[fpvandoorn/carleson](https://github.com/fpvandoorn/carleson/blob/master/blueprint/src/)
and other leanblueprint projects.

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
- `\lean{Fully.Qualified.Name}` links to the API docs. It may list several
  comma-separated names for group lemmas (e.g. corner cases).
- `\leanok` says "this is formalized in Lean". The statement and its proof
  carry it together (`lint.sh` check 8).
- `\uses{...}` on the **statement** declares the statement's dependencies; on
  the **proof**, the argument's. The dep-graph distinguishes them.
- Always write a prose proof alongside `\leanok`. The dep-graph is the formal
  map; the prose is the human map.

#### Sorry-blocked statements (red nodes)

A node whose Lean declaration exists but does not yet discharge it keeps
`\lean{...}` (the symbol resolves; the API page exists) and omits `\leanok` on
**both** the statement and the proof, so the dep-graph colors it red.
Carleson's convention relies on that absence alone; no `\notready` macro. A
`sorry`-free declaration that **launders a load-bearing hypothesis** (assumes
the hard part rather than proving it or `\uses`-linking a node that does) is
red for the same reason: see *the honesty gate* below.

### Prose and editorial conventions → `AUTHORING.md`

Label prefixes, cross-references, citations, what to include vs. skip (with
the narrative-bridge `@[deprecated]` shim), proof verbosity, and audience and
vocabulary are in **[`AUTHORING.md`](AUTHORING.md)**, read when authoring a
chapter. A routine pin or `\leanok` flip does not need them.

### The retrospective appendix → `AUTHORING.md`

`chapter/retrospective.tex` ("Notes on the formalization") is a deliberate
exception, confined to that one file, to two conventions: route history stays
out of live documents, and Lean identifiers are not prose subjects. `lint.sh`'s
vocabulary checks 5a and 5b exempt it. Its placement, register and TeX
mechanics (`alltt` excerpts, Unicode subscripts, long `\texttt{}` identifiers,
commit links) are in `AUTHORING.md` *The retrospective appendix*; read that
before editing the file.

## Static checks before commit

The **always-on per-commit gates** for any commit touching a `\lean{...}`
pointer, a `\label{...}`, a `\uses{...}` / `\cref{...}` reference, a
`\cite{...}` key or a `\leanok`. They catch what the plastex build would catch
later, in seconds. They are not a cleanup-round task: `CLEANUP.md` §A audits
divergence; it does not re-run gates that should have been green on each
commit.

**All `\lean{...}` names resolve to real Lean declarations.** The check is
`checkdecls`, which loads every project import and looks each name up. Run the
bundled gate by default:

```sh
blueprint/verify.sh        # runs inv bp, inv web, lake exe checkdecls
```

It works from any cwd (it does the cd/PATH/venv plumbing) in ~30–45 s, and its
final `checkdecls` step **prints nothing on success**: silence after the
`==> lake exe checkdecls` banner is green; a failure exits non-zero and names
the `\lean{...}`. `checkdecls` reads `blueprint/lean_decls` (gitignored),
which `inv web` regenerates, so its silence means something **only** after an
`inv web` that actually loaded the `blueprint` plastex package. `verify.sh`
refuses to run it when the plastex log shows a package-load error or
`lean_decls` is older than a source `.tex` (a skipped package read as green
from 2026-07-30 to 2026-09-15; `SETUP-AND-PITFALLS.md` *Pitfalls*,
libcgraph). Longhand: `( cd blueprint && source .venv/bin/activate && inv bp
&& inv web )`, then `lake exe checkdecls blueprint/lean_decls`. CI runs the
same check, and a missing declaration blocks the merge. The usual cause is a
missing enclosing namespace (`SimpleGraph.Henneberg.IsLaman.foo`, not
`SimpleGraph.IsLaman.foo`). Don't substitute grep.

**The other scriptable gates are `blueprint/lint.sh`** (any cwd, sub-second,
no venv, TeX or lake). Run it on any commit touching a `\label`, `\uses`,
`\cref`, `\cite`, `\leanok` or a supersession marker. Green is
`blueprint/lint.sh: all static reference checks passed.`; a failure prints
the offenders and exits non-zero. Its header comment documents each check and
its carve-outs:

- (1) every `\uses` and `\cref`/`\Cref` target has a `\label`; (2) every
  `\cite` key has a `bibliography.bib` entry, and every entry is cited;
- (3) the supersession gate below;
- (4) the **hanging-pin gate**: no statement carries `\leanok` without a
  `\lean{...}` pin. That is an *uncheckable green*: `checkdecls` verifies
  only names that are pinned;
- (5) the **vocabulary gate**: no project-internal process vocabulary (the
  banned words of `AUTHORING.md`'s terminology dictionary, phase
  self-description outside `chapter/intro.tex`, a raw Lean hypothesis name
  `\mathtt{hfoo}` in a statement block);
- (6, 7) the multi-label `\cref{a,b}` and subsubsection-`\cref` guards (both
  render "??" under plastex);
- (8) the **proof-level `\leanok` gate**: a node's statement and its proof
  agree on `\leanok` (the tree has no `sorry`, so a formalized statement has a
  formalized proof).

**No live-route node references a superseded one (the supersession
gate).** A commit that supersedes a route (replaces a chain of `\uses`'d nodes
with another) **owns reconciling every node on the old route, both statement
and proof, in the same commit**, not just the dead leaf and the live node's
statement. A live node whose statement says "route X is superseded" while its
proof still routes through X falls through every other gate (calibration:
`DESIGN.md` *Static-check calibrations*, Phase 22c).

- **Mark a superseded node in its environment title**: the literal word
  `superseded` in the `[...]` of `\begin{lemma}[...]` (e.g. `[M3 (superseded,
  motion-side): …]`). The title is what check 3 greps (it relies on the
  project's invariant that `\label{}` sits on the line after `\begin`);
  saying so in the body helps the reader but is not the marker. An isolated dead node is kept by
  default (retain-with-marker), inert.
- **A whole dead route collapses instead.** Once a dead route accretes several
  struck nodes plus route-history prose, delete the struck environments and
  that prose in the same commit, leaving one short remark (no `\label`ed
  environment) naming what was tried and why it does not match the source.
  `git log` is the audit trail (owner-confirmed default,
  `../notes/Phase23-cleanup.md` D1).
- **A node on a live route may not `\uses` a superseded node**, nor describe
  its live proof through one: reroute its edges and prose onto the replacement
  in the same commit. A `\cref{}` pointer in an explicit audit-trail aside is
  fine, and so is superseded-`\uses`-superseded (a consistent audit trail).
  Check 3 flags only a non-superseded node reaching into a superseded one;
  reconcile any hit before commit.

**Every hypothesis of a `\leanok` node is discharged (the honesty
gate).** The checks above resolve names and are blind to hypothesis content:
`checkdecls` passes a declaration carrying any number of smuggled hypotheses.
This gate is the semantic companion, run **by eye** on any commit that **adds
a `\leanok`** (it is not scriptable: "load-bearing vs ambient" is a judgement
call):

> A node may carry `\leanok` only if **every non-ambient hypothesis**
> of its `\lean{...}` declaration is either (a) discharged inside the
> Lean proof body, or (b) the *conclusion* of a node it `\uses{...}`.
> A load-bearing hypothesis that is neither — a dangling assumption
> with no node representing the obligation to prove it — means the
> node is **dishonestly green**. Keep it red (drop `\leanok`, keep
> `\lean{...}`) until the hypothesis is discharged or given its own
> tracked node.

"Ambient" means the lemma's genuine input data and typeclass or finiteness
assumptions (`[Fintype V]`, "Let $G$ be a minimal $k$-dof-graph", the
placement `p`); "load-bearing" means a hypothesis that *is* a mathematical
claim the lemma would otherwise have to prove. Case (b) is the legitimate
green-modulo pattern: `lem:case-I` is honestly green because its hypothesis
*is* `lem:genericity-device`, a `\uses`'d node that was red until discharged.
The failure is case (b) *claimed* but not *true*. The gate's clauses:

- **Case hypotheses are obligations, never ambient.** A hypothesis the source
  obtains by a case split, its failure handled by a separate named lemma
  (`hcSimple` ↔ KT Lemma 6.3, whose failure is Lemma 6.5), is load-bearing
  even when it reads like input data or its discharge is called "wiring".
  Before `\leanok` lands, name the source's other branch and either
  (a) discharge the dispatch in Lean, (b) mint a tracked red node for it, or
  (c) put it on the active phase's forward checklist with a one-line source
  pointer (`../DESIGN.md` *Statement faithfulness to the source*).
- **Producer / existence lemmas get extra scrutiny.** A node promising to
  *produce* something (`∃ p, …`, "attains full rank") whose Lean *assumes*
  what it claims to produce has smuggled its deliverable in as a hypothesis.
  This is a per-commit gate, run when the `\leanok` is added; `CLEANUP.md` §A
  step 1 is only its between-phases re-run (calibration: `DESIGN.md`
  *Static-check calibrations*, Phase 21b).
- **Sliced producers: scope the node to the conjunct actually built.** A
  producer built one conjunct at a time is a green node whose statement *and*
  role-prose claim only the conjunct proven, plus a sibling (or red) node for
  the rest, never one node claiming the whole slot (calibration: the same
  section, Phase 22i).
- **The arithmetic closes** (the gate's second half). Before a producer is
  scheduled as a build, trace its target rank, count or dimension through the
  construction and confirm it closes, not just that the `\uses` edges
  type-check; math-first when the math is the hard part (`../DESIGN.md`
  *Constructibility recon before scheduling a producer build*).
- **The structure matches** (the third half). A node formalizing a step of a
  published proof reproduces the source's argument *structure*, not just its
  conclusion and count. The tell: the counts line up, but you keep needing
  fresh hypotheses to bridge a gap the source doesn't have. A node green with
  its hard half deferred to a red sibling needs that sibling's feasibility
  re-verified before downstream nodes build on it: "green-with-a-red-sibling"
  ≠ "green" (`../DESIGN.md` *Match the source's argument structure, not just
  its conclusion*).

**A definition node's prose states what the Lean states (the
definition-faithfulness gate).** On any commit that adds `\leanok` to a `def:`
node, or adds or reshapes a `def … : Prop` modelling a paper notion, run the
**cheapest-witness audit**: ask what the cheapest satisfying witness is, and
read the node's prose against that, not against the paper. If the Lean is
deliberately weaker or stronger than the source notion, the prose says so
(what diverges, and where the honest form is tracked). No other gate catches
paper-strength prose over a weaker `Prop`: `checkdecls` is name-only, and the
honesty gate reads hypotheses, not definitions (calibration:
`def:rank-hypothesis`, `../DESIGN.md` *Statement faithfulness to the source*).

## Local build

Two formats: **web** (HTML + dep-graph, via plastex; primary, and what CI
deploys) and **print** (PDF, via xelatex). Run `inv bp` then `inv web`, in
that order (citations break otherwise), from `blueprint/` with the venv active
and TeX on `PATH`; the per-commit gate is `verify.sh` (above). The how-to (the
`PATH` fix, the per-Bash-call shell caveat, opening
`web/dep_graph_document.html`) is in `RENDERING.md`; one-time setup is in
`SETUP-AND-PITFALLS.md` *One-time setup*. CI runs the same builds via
`leanprover-community/docgen-action` (`.github/workflows/push.yml` on master,
which deploys; `push_pr.yml` on PRs, which doesn't); a TeX or `\lean{...}`
error fails the whole pipeline.

## File layout

```
blueprint/
├── CLAUDE.md            ← this file; AUTHORING.md, DESIGN.md, RENDERING.md,
│                          SETUP-AND-PITFALLS.md are read on demand
├── requirements.txt     ← plastex / leanblueprint / invoke pins
├── tasks.py             ← invoke targets: web / bp / serve
├── verify.sh, lint.sh   ← the gates above
└── src/
    ├── web.tex, print.tex      ← entries for plastex / xelatex
    ├── bibliography.bib, extra_styles.css (web only), plastex.cfg, latexmkrc
    ├── preamble/        ← common.tex (macros, theorem envs), print.tex, web.tex
    └── chapter/
        ├── main.tex     ← top-level `\input{}` orchestration
        ├── intro.tex    ← reader's introduction: scope, the four-arc
        │                  organization + per-phase one-liner, reading guide
        └── sparsity.tex ← Phase 1 chapter (canonical example)
```

`intro.tex` is a fixed-size orientation, not a status log: keep it jargon-free
and forward-weighted (`../PHASE-BOUNDARIES.md` *Sync the user-facing status
surfaces*).

### Adding a new chapter

Create `src/chapter/<name>.tex` (`sparsity.tex` is the structural template),
add its `\input{}` to `chapter/main.tex`, rebuild, and check that the
dep-graph connects the new nodes to earlier chapters. In **forward mode** (the
default since Phase 6; `DESIGN.md`), entries start without `\lean{...}` and
`\leanok`, which land with the Lean; prose proofs may be one-line gestures
until the phase-end pass; `\uses{...}` chains still record the intended proof
structure, and the mostly red first build is the to-do list. In **backfill
mode** (Phases 1–5) every entry is green when committed.

### Extending an existing chapter

A later phase's additions to an earlier chapter land in the **same commit** as
the Lean and are **interleaved topically**: the reader sees mathematical
order, not landing order. A phase that reshapes a blueprinted signature
(Phase 11's `Option` → `PebbleGameResult`) goes further, **restating existing
entries in place** per Layer commit; a reshaped node stays where it was, and the to-do list is the
phase note's *Layer plan*. Either way, a restated node reads as if its current
shape were always its shape: per-Layer scheduling ("was `some D'`") and Lean
plumbing (`Quot.out`, agreement witnesses) are changelog, not prose; state a
computable/`noncomputable` split in one sentence and let the link carry the
rest.

### Macros

In `preamble/common.tex`, deliberately few (`\edgesIn`, `\rk`, `\KK`, plus
`\N`, `\Z`, `\Q`, `\R`). Add a recurring notation there rather than
redefining it per chapter. `\edgesIn{S}` is $E_G[S]$ and `\edgesIn[H]{S}` is
$E_H[S]$; the optional graph is for comparing two graphs.

## Pitfalls

Build-time pitfalls (plastex warnings vs errors, the `inv web`-without-`inv
bp` citation break, `_` in `\texttt{...}`, math in section titles, …) are in
`SETUP-AND-PITFALLS.md` *Pitfalls*. Skim it when a build misbehaves.

## Friction review (mandatory)

The Lean side's friction review, narrowed to the blueprint. A TeX-level
pitfall (a macro, `\texttt{}` quoting, a plastex quirk) goes in
`SETUP-AND-PITFALLS.md` *Pitfalls*. A structural one goes in
`../notes/FRICTION.md`, tagged `[blueprint]`, since in forward mode the
dep-graph is the proof plan. Ask:

1. **Did a TeX construct fight you?** Record the pitfall.
2. **Did the dep-graph show a structural gap** (a `\uses` chain longer than the
   math needs, an orphan node, a cycle, a node that should be split)? Fix it
   in this commit or file a note: an unexamined gap in the plan is debt.
3. **Did selection feel arbitrary?** Write the criterion you used as one line
   in `AUTHORING.md` *What to include vs. skip*, so the next agent doesn't
   relitigate it.

No new entries is fine, but only after checking.
