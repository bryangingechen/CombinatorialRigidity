# blueprint/CLAUDE.md — agent operating manual for the blueprint

This file is the **agent-facing operating manual** for working on the
blueprint (the LaTeX/plastex doc under `blueprint/src/`). It is the
blueprint analogue of the top-level `CLAUDE.md`; the project uses a
four-way split:

- `../CLAUDE.md` (root, always loaded) — project-wide process: reading
  order, hand-off contract, citations, project history.
- `../CombinatorialRigidity/CLAUDE.md` — Lean source ops: build/lint
  gates, friction review, MCP tool guidance, quirks index.
- `../notes/CLAUDE.md` — phase-notes and friction-log discipline.
- This file — blueprint TeX ops: authoring conventions, static checks
  (including `checkdecls`), local builds (`inv bp` / `inv web`),
  dep-graph spot-check, forward-mode mechanics.

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

#### Sorry-blocked statements

A theorem whose Lean declaration exists but whose body is `sorry`
(typical for forward-mode work, or for downstream phases stated in
an upstream chapter — cf. `IsGenericallyRigid.exists_isLaman_le` in
`LamanTheorem.lean`, stated for Phase 6) is encoded as:

```latex
\begin{theorem}[...]
  \label{thm:my-theorem}
  \lean{Namespace.my_theorem}   % the Lean declaration exists
  \uses{...}                    % dep edges to its statement-level deps
  Statement.
\end{theorem}
\begin{proof}
  Sketch of the intended proof, in prose.
\end{proof}
```

i.e. `\lean{...}` is kept (the symbol resolves; the API doc page
exists), but `\leanok` is omitted on **both** the theorem environment
and the proof. The dep-graph then colors the node red. Carleson's
convention is to rely on this absence-of-`\leanok` signal alone; no
`\notready` macro is needed.

The same red-not-green discipline applies to a node whose Lean
declaration is `sorry`-free but **launders a load-bearing hypothesis**
(assumes the hard part rather than proving it or `\uses`-linking a
node that does). That is also a red node, for the same reason — the
obligation is not yet discharged. See *Static checks before commit →
the honesty gate* for the test and the Phase-21b
`lem:case-I-realization` calibration case.

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

### Citations

The blueprint loads a BibTeX bibliography from `src/bibliography.bib`
in both entry points (`print.tex`, `web.tex`) with the `amsalpha`
style. Cite published work with `\cite{key}`, combining multiple
citations with comma separation: `\cite{tayWhiteley1985,jordan2016}`.

Key convention: `firstAuthorYear` for single-author works
(`laman1970`), camelCased authors for multi-author works
(`tayWhiteley1985`, `graverServatiusServatius1993`). Match what's
already in `bibliography.bib`.

Top-level `CLAUDE.md → Referencing prior work` has the accuracy bar.
For the blueprint specifically:

- **Before adding a new bib entry**, verify title, authors,
  journal/series, volume, year, and page range against a primary
  source — DOI landing page, publisher metadata, or NASA ADS for
  older journals. Don't copy from second-hand citations without
  cross-checking.
- **Match attribution to who proved it.** When the modern
  presentation matters, name both: *"classical strategy of
  Tay--Whiteley 1985, in the modern presentation of Jord\'an 2016
  §2.2"* (`chapter/intro.tex` is the canonical example).
- **Verify any §N pointers** — §N must exist in the cited work and
  contain what you claim. Drop the section pointer rather than
  guess.

`leanblueprint pdf` (CI) and `inv bp` (local) drive `latexmk`, which
runs `bibtex` and produces `print/print.bbl`. `inv bp` also copies
that file to `src/web.bbl` so the subsequent `inv web` plastex run
renders the bibliography page and resolves in-prose `\cite{}`s. Both
formats use the same `amsalpha` style, so labels like `[TW85]`,
`[Jor16]` are stable across formats.

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

#### Narrative-bridge corollaries (the `@[deprecated]` shim pattern)

A hybrid between *Include* and *Skip*: a corollary worth naming as a
consequence for the project's central object (e.g. a Laman-specialised
form of a sparse-level theorem) but whose Lean version is a one-line
composition with **no downstream caller**. Prose-only invites silent
drift; a normal lemma proliferates API that competes with the general
form. The pattern: keep it a full `\begin{corollary}` with `\lean{}` +
`\leanok`, and formalize the Lean shim under `@[deprecated <general-form>
(since := "narrative-bridge")]` with the intent in its doc-comment — the
build still checks the prose (a rename breaks the shim body), the warning
discourages callsites, the dep-graph greens. (Why the non-date `since`
sentinel: `CombinatorialRigidity/CLAUDE.md` *Engineering conventions*.)
Canonical example: `cor:isLaman-exists-rowIndependent` ↔
`SimpleGraph.IsLaman.exists_rowIndependent_placement`
(`MatroidIdentification.lean`).

**Only when the Lean has zero expected callers.** Most specialized
lemmas (`IsLaman.iso`, `IsGenericallyRigid.card_mul_le_two`, …) are real
API with callers — formalize them eagerly, no `@[deprecated]`. If you
want `@[deprecated]` on a lemma that *has* callers, either refactor them
onto the general form or drop the marker (it's genuine API).

### Proof verbosity

Match the carleson style: one to three sentences of English gesturing
at the argument; a reader wanting the full proof clicks to the Lean.
(Models in `sparsity.tex`: "Immediate from the definition." up to the
~10-line `thm:isTightOn-union-inter`.)

**First make Lean as painless as the math; only then add prose asides.**
When a step is harder to formalize than to state, fix the *Lean* first
(better strategy, an upstreamable helper, sharper automation); only if
that fails add a brief aside naming the residual gap. "The Lean is just
verbose" is a smell — friction we accept in the blueprint the next phase
pays for.

**Be honest about formalization cost, both ways.**
- *Omit* (Lean noise invisible to the math): `omega`/`grind`/`simp`
  closes, typeclass elaboration, mathlib glue.
- *Note* (a one-line math step that grew real Lean infrastructure): a
  hand-rolled `Equiv` for a "canonical" move, a named helper standing in
  for a one-step correspondence, a case-split the math wouldn't take —
  one clause, so the prose is a faithful map, not a polished fiction.
- *Don't over-note* (the basis-free anti-pattern): prose narrating *how
  the formalization models* an object ("basis-free, deferring
  coordinatization", "abstract graded piece rather than a basis") is
  changelog, not math. One clause max, and only when the modelling choice
  is load-bearing for a later node; else cut it (it belongs in the Lean
  doc-comment). Phase 18's §2.2–2.4 accreted four such asides — don't
  reintroduce them.

**The carve-out: crux nodes earn full, detailed exposition.**
Terse-by-default is the rule above; the exception is the project's
deliverable of a *fully detailed, self-contained exposition* of
Katoh–Tanigawa's hardest arguments — spelling out the steps the paper
reasonably compresses, so each crux is followable without the authors'
context (a complement to KT's research exposition, not a verdict on it). A
genuinely hard node earns a full, followable prose proof — and which nodes
have earned it (and whether the prose has landed) is tracked in the
cross-phase ledger `../notes/BlueprintExposition.md`.
**Capture-now / write-later:** during a phase, add a one-line ledger entry
whenever a node reroutes/decomposes and surfaces a stable mathematical
insight (the case structure KT states compactly, why a strengthening is forced);
**write** the expanded exposition at phase-close (the broadened blueprint
re-read — top-level `CLAUDE.md` *When this commit closes a phase*), once the
argument is `sorry`-free. The carve-out is for *mathematical* difficulty
about **KT's math**, not our formalization setup — a reroute caused by a
project-side mistake does not earn an entry (the ledger's own header has
the sharpened inclusion criterion + the `(a)/(b)/(c)` flavors).

## Static checks before commit

These are the **always-on per-commit gates** for any commit that
touches a `\lean{...}` pointer, a `\label{...}`, a `\uses{...}` /
`\cref{...}` reference, or a `\cite{...}` key. They catch the
failure modes that the plastex build would catch later, but faster,
and run in seconds. Don't carry them as a separate cleanup-round
task — `CLEANUP.md` §A is for divergence audits, not for re-running
gates that should already have been green on each commit.

**All `\lean{...}` names resolve to real Lean declarations.** The
authoritative check is `checkdecls`, which loads every project import
and looks up each name in the Lean environment. It must run against a
freshly-regenerated `blueprint/lean_decls` (produced by `inv web` from
the current `\lean{...}` set; the file is gitignored).

The bundled command — and the one to use by default — is:

```sh
blueprint/verify.sh        # runs inv bp, inv web, lake exe checkdecls
```

The script handles cd/PATH/venv plumbing and works from any cwd; its
final `checkdecls` step **prints nothing on success** (silence after the
`==> lake exe checkdecls` banner = green; non-zero + the failing
`\lean{...}` name on failure). Longhand when the script can't apply:
`( cd blueprint && source .venv/bin/activate && inv bp && inv web )` then
`lake exe checkdecls blueprint/lean_decls`. CI runs the same check
(`docgen-action`); a missing-declaration failure is a hard merge blocker.
Most common cause: a missing enclosing `namespace` in the `\lean{...}`
pointer (`SimpleGraph.Henneberg.IsLaman.foo`, not
`SimpleGraph.IsLaman.foo`). `inv web` + `checkdecls` run in ~15s,
`verify.sh` ~30–45s — the everyday path, fast enough; don't substitute grep.

**The other scriptable gates are bundled in `blueprint/lint.sh`** —
run it (from any cwd; sub-second, no venv/TeX/lake needed) on any
commit touching a `\label` / `\uses` / `\cref` / `\cite` / `\leanok`
or a supersession marker. It checks:

- every `\uses{...}` and `\cref`/`\Cref{...}` target has a
  `\label{...}`;
- every `\cite{...}` key has a `bibliography.bib` entry, and every
  bib entry is cited somewhere;
- the supersession gate below;
- the **hanging-pin gate**: no theorem-like node carries a statement
  `\leanok` without a `\lean{...}` pin. Such a node is an *uncheckable
  green* — `checkdecls` verifies only names that **are** pinned, so a
  `\leanok`-without-`\lean{}` node slips through it (and through the
  honesty gate, which reads hypotheses, not the `\leanok`/`\lean`
  pairing). The scriptable form keys on the statement block (`\begin{env}`
  → the node's `\begin{proof}` or `\end{env}`), so a `\leanok` on the
  *proof* alone is not flagged. This is the scriptable companion to the
  honesty gate's no-pin variant; the calibration case
  (`lem:case-III-nested-rank-lower`, Phase 22k L7b — its `h622lb` discharge
  was folded inline into `case_III_realization` with no standalone decl to
  pin, fixed by extracting `case_III_nested_rank_lower`) is why the gate
  exists.

It prints the offending names and exits non-zero on failure;
`blueprint/lint.sh: all static reference checks passed.` is green.

**No live-route node references a superseded one (the supersession
gate).** When a commit supersedes a route or argument — replaces a
chain of `\uses`'d nodes with a different one — it **owns reconciling
every node on the old route, both statement and proof, in the same
commit**, not merely marking the dead *leaf* and updating the live
node's statement. The failure mode this catches (Phase-22c calibration
below) is a *live* node whose statement says "route X is superseded"
while its **proof still routes through X**: self-inconsistent prose that
falls through every other gate (the honesty gate fires only on `\leanok`
additions; the per-commit re-read checks only what the commit changed,
not downstream red nodes; "superseded" was free-text with no
machine-readable status). The discipline:

- **Mark superseded nodes with a greppable, standardized marker.** Put
  the literal word `superseded` in the **environment title** — the
  `[...]` of `\begin{lemma}[...]` (e.g. `[N7b-4 (superseded, row-side):
  …]`, `[M3 (superseded, motion-side): …]`). The title is the one line a
  one-environment-per-block `awk` can key on; restating it in the body
  prose (*"Red, superseded"*) is good for the reader but the **title**
  is what the check below greps. Keep the dead node (retain-with-marker)
  for the audit trail rather than deleting it — but make it inert.
- **A node still on a live route may not `\uses` (nor describe its live
  proof through) a superseded node.** Reroute its `\uses` edges and its
  prose onto the replacement in the *same* commit. A `\cref{}` *pointer*
  to a superseded node in an explicit audit-trail aside ("the earlier
  dead-ends, off the live route, are …") is fine; a `\uses` dependency
  edge or a live-proof step is not.
- **superseded-`\uses`-superseded is fine** — that is the internally
  consistent audit trail (e.g. M3 `\uses` M2, both struck). The gate
  flags only a *non-superseded* node reaching into a superseded one.

The scriptable form is `blueprint/lint.sh`'s third check (two `awk`
passes feeding a `comm`: enumerate labels whose environment title
contains `superseded` — the `\label{}` on the line after `\begin` is
the project's invariant — then assert no non-superseded node's
`\uses` targets one). Any hit is a live node depending on a struck
one — reconcile it before commit.

**Calibration case (Phase 22c).** Opening 22c to build the Case-II/III
stratum-1 nodes, the live `lem:case-II-realization` /
`lem:case-II-realization-placement` *statements* said "M3 / N7b-4
superseded" while their *proofs* still routed through them — rot that
had survived since the eq. (6.12) understanding was settled phases
earlier (KT, `../notes/Phase21b.md` *Finding A*), because the
superseded prose lived in *red* nodes invisible to the `\leanok`-gated
honesty gate. Commit `7ba0266` reconciled the prose; this gate + the
phase-open red-node consistency gate (`../CLAUDE.md` *When this commit
opens a phase*) keep it from recurring.

**Every hypothesis of a `\leanok` node is discharged (the honesty
gate).** The checks above are name/label *resolution* checks —
they are blind to hypothesis *content*, and `checkdecls` happily
passes a `\lean{...}` declaration carrying any number of smuggled
hypotheses as long as the name exists. This gate is the semantic
companion, and it is the one a human must run by eye on any commit
that **adds a `\leanok`** (it is not scriptable, because "load-bearing
vs ambient" is a judgement call). The rule:

> A node may carry `\leanok` only if **every non-ambient hypothesis**
> of its `\lean{...}` declaration is either (a) discharged inside the
> Lean proof body, or (b) the *conclusion* of a node it `\uses{...}`.
> A load-bearing hypothesis that is neither — a dangling assumption
> with no node representing the obligation to prove it — means the
> node is **dishonestly green**. Keep it red (drop `\leanok`, keep
> `\lean{...}`) until the hypothesis is discharged or given its own
> tracked node.

"Ambient" = the lemma's genuine input data and typeclass/finiteness
assumptions (`[Fintype V]`, "Let $G$ be a minimal $k$-dof-graph",
the placement `p`). "Load-bearing" = a hypothesis that *is* a
mathematical claim the lemma would otherwise have to prove. The
legitimate **green-modulo-X** pattern (forward mode's GREEN-modulo-21b
nodes) is exactly case (b): `lem:case-I` is honestly green because its
hypothesis *is* `lem:genericity-device`, a `\uses`'d node that was red
until discharged. The failure mode is case (b) *claimed* but not
*true* — a `\uses` edge that doesn't actually conclude the hypothesis.

**Case hypotheses are obligations, never ambient (Phase-22h
calibration).** A hypothesis the source paper obtains by a **case
split** — one whose *failure* is handled by a separate named lemma in
the source (`hcSimple : (G.rigidContract H r).Simple` ↔ KT Lemma 6.3,
whose failure is Lemma 6.5) — is load-bearing even when it reads like
input data, and even when the commit calls its discharge "wiring" or
"the coordinator's assembly". Before `\leanok` lands on a node
carrying one: name the source's other branch and either (a) discharge
the dispatch in Lean, (b) mint a tracked red node for the other
branch, or (c) put it on the *active* phase's forward checklist with a
one-line source pointer. Calibration: `lem:case-I-realization` went
green in 22a carrying `hcSimple` with none of the three — the
Lemma-6.5 arm had no tracking artifact anywhere and stayed orphaned
across five sub-phases until the §1.54 feed audit (postmortem:
`../DESIGN.md` *Statement faithfulness to the source*).

**Producer / existence lemmas get extra scrutiny.** A node whose
statement promises to *produce* something (`∃ p, …`,
`HasFullRankRealization`, "attains full rank") but whose Lean
*assumes* the very rank/rigidity/realization it claims to produce is
the textbook smell — the deliverable smuggled in as a hypothesis.
Phase 21b's `lem:case-I-realization` shipped green this way (it
assumed `hHrig`/`hcrig`, the simultaneous-rigid placement it was
named to construct, with no node tracking that obligation); the fix
was to drop `\leanok`, keep the proven composition carrier, and add
the red node `lem:case-I-splice-placement` for the construction. The
between-phases re-run of this gate is `CLEANUP.md` §A step 1 — but
this is a *per-commit* gate, run at the moment `\leanok` is added, not
a debt deferred to a cleanup round.

**Sliced producers — scope the node to the conjunct actually built.**
When a producer is built one conjunct at a time (the molecular program's
recurring bare-`HasPanelRealization` / GP-`HasGenericFullRankRealization`
split — the L3 base producer, the L4 cut-edge producer,
`theorem_55_all_k`'s `hsplitPos`/`hsplitZero` branches), the *intermediate* commit
lands only one half. Represent that as a **green node whose statement
*and* role-prose are scoped to the conjunct actually proven**, plus a
separate sibling (or red) node for the unbuilt conjunct — **never one
node claiming the full slot/pair while only half is built.** Two failure
modes, both seen in Phase 22i: a green node landing at the *weaker*
conjunct the slot doesn't want (row 89 — the GP conjunct discharged as
the bare type), and a node honestly green for its *statement* but whose
**prose overclaims its role** (row 92 — "fills the `hcut` slot" when only
the bare `HasPanelRealization` conjunct is built; `checkdecls` and the
hypothesis-honesty gate both pass, so only a design-§ re-read of the
role-prose catches it). The clean structure (settled at
`notes/Phase22-realization-design.md` §1.62(e)): green-bare node + a
sibling for the GP conjunct, mirroring how `theorem_55_all_k` keeps
`hsplitPos`/`hsplitZero` as separate branches.

The gate has a *second half*, and it is the one that bites producers:
even with every hypothesis honest, the intended **proof step may not
follow** or the **target count the construction can't reach**. Before a
producer node is scheduled as a *build* (or tagged "build-shaped"), trace
its target quantity (rank/count/dimension) through the construction and
confirm the **arithmetic closes** — not just that `\uses` edges
type-check; math-first when the math is the hard part. Rule + the
Phase-21b calibration (a `+(D−1)` vs `+D` one-line shortfall that sat
under four re-plans): `../DESIGN.md` *Constructibility recon before
scheduling a producer build*; dead-ends in `../notes/FRICTION.md`
*[process] Phase 21b realization producers*.

The gate has a *third half* — structural fidelity. The second half confirms the
**arithmetic** closes; this one confirms the **shape** does. When a `\leanok` (or
to-be-built) node formalizes a step of a published proof, its **composition lemma
must reproduce the source's argument *structure***, not just its conclusion and
count. A locally-sound modelling choice can re-express the source's argument as a
*different* one with a different — possibly intractable — obligation: Phase 22a's
splice translated KT's **block-triangular rank-addition** (leg-wise placements, the
ranks add) into a motion-space **common-seed glue** (one placement rigid on both
legs), and three passes produced undischargeable bridge hypotheses (`hpinc`,
`htransportGP`) whose *arithmetic closed* but whose *structure* didn't match KT. **The
tell:** the counts line up but you keep needing fresh hypotheses to bridge a gap the
source doesn't have. **Corollary:** a node that is *green with its hard half deferred
as a red sibling* (Phase-21b `lem:case-I-splice-seed` green, `lem:case-I-splice-placement`
red) must have that red sibling's feasibility **re-verified before downstream nodes
build on the green half** — "green-with-a-red-sibling" ≠ "green". Rule + the Phase-22a
calibration: `../DESIGN.md` *Match the source's argument structure, not just its
conclusion*; dead-end in `../notes/FRICTION.md` *[process] Phase 22a — motion-space
splice glue vs KT block-triangular*.

**A definition node's prose states what the Lean states (the
definition-faithfulness gate).** The honesty gate audits a theorem
node's *hypotheses*; this is its companion for **definitions**, where
the failure mode is prose at the *source's* strength over a weaker
Lean `Prop`. On any commit that adds `\leanok` to a `def:` node — or
adds/reshapes a `def … : Prop` modeling a paper notion — run the
**cheapest-witness audit**: ask what the cheapest satisfying witness
is, and read the node's prose against *that*, not against the paper.
If the Lean is deliberately weaker or stronger than the source notion,
the prose must say so explicitly (what diverges, and where the honest
form is tracked) — paper-strength prose over a weaker definition is a
masked divergence no other gate can catch (`checkdecls` is name-only;
the honesty gate reads hypotheses, not `Prop` bodies; a def has no
proof for the proof-reading passes to audit). Calibration (Phase-22h
postmortem): `def:rank-hypothesis` sat `\leanok` describing KT's
genuine panel-hinge realization ("no two hinges parallel") while the
pinned `HasFullRankRealization` was satisfiable by an all-zero-
extensor *welded* framework on every connected graph — the bare
conjunct of the formalized Thm 5.5 was vacuous, unnoticed from the
def's birth (Phase 21) through three weeks of building on top, because
the blueprint masked the divergence instead of exposing it. Full
narrative + the strengthening decision: `../DESIGN.md` *Statement
faithfulness to the source*.

## Local build

The blueprint builds in two formats:
- **Web** (HTML + dep-graph) via plastex — primary; what CI deploys.
- **Print** (PDF) via xelatex — secondary.

One-time setup (Homebrew + `tlmgr` packages + a Python venv with
`pygraphviz`'s Apple-Silicon-specific install flags) lives in
`SETUP-AND-PITFALLS.md`. Run those once per machine; agents are not
expected to re-read them on every session.

### Running builds → `RENDERING.md`

`inv bp` (xelatex → PDF + copies the `.bbl`) then `inv web` (plastex →
HTML + dep-graph), in that order (citations break otherwise), from
`blueprint/` with the venv activated and TeX on `PATH`. **The per-commit
gate is `blueprint/verify.sh`** (bp + web + checkdecls, quietly — see
*Static checks before commit* above). The full local-render how-to — the
exact `PATH` fix, the per-Bash-call shell caveat, the `inv` invocations,
and opening `web/dep_graph_document.html` — is in **`RENDERING.md`** (read
on demand when rendering/previewing locally).

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
├── verify.sh            ← bundled bp + web + checkdecls gate
├── lint.sh              ← fast static reference checks (labels,
│                           cites, supersession gate)
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
        ├── intro.tex    ← reader's introduction: scope, the four-arc
        │                  organization + per-phase one-liner, reading
        │                  guide. A fixed-size orientation, NOT a status
        │                  log — keep it jargon-free / forward-weighted
        │                  (../CLAUDE.md *Sync the user-facing status
        │                  surfaces*).
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

### Extending an existing chapter (later phase adds to an earlier file)

When a later phase adds infrastructure to an existing chapter's file, the
new entries land in the **same commit** as the work and are **interleaved
topically** — the reader sees natural mathematical order, not the order
phases landed (phase history goes in commit messages). (Phase 5 inserted
`IsGenericallyRigidInj` + new subsections mid-chapter into
`frameworks.tex`/`henneberg.tex`, not appended.)

A more aggressive variant — **restating entries in place** — applies when a
phase reshapes a blueprinted signature (e.g. Phase 11's `Option` →
`PebbleGameResult`): node-level edits land per Layer commit, the chapter
spends a few commits with selected nodes red, and a reshaped node stays
where it was (an *inserted* node goes in its natural position). See
`../notes/PhaseN.md` *Layer plan* in structural-edit phases.

**Keep reshape/phase history out of the prose.** Per-Layer scheduling ("was
`some D'`", "Layer 4b") and Lean-internal plumbing (`Quot.out`,
`Finset.toList`, agreement witnesses) are changelog — a restated node must
read as if its *current* shape were always the shape; state any
computable/`noncomputable` split in one sentence and click through for the
rest. (Phase 11's first pass violated this; the 2026-05 readability pass
stripped it — don't reintroduce it.)

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

## Pitfalls

Build-time pitfalls (plastex warnings vs errors, the silent
`inv web`-without-`inv bp` citation-break trap, `_` in
`\texttt{...}`, math in section titles, Python 3.9 quirks, etc.)
live in `SETUP-AND-PITFALLS.md`. Skim that file when a build behaves
unexpectedly.

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
