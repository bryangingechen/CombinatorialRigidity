# blueprint/AUTHORING.md — prose & editorial conventions (read on demand)

The prose-writing and editorial half of the blueprint authoring conventions,
split out of `blueprint/CLAUDE.md` so that always-loaded manual stays focused
on every-touch forward-mode mechanics (the red/green node encoding, static
checks, builds, file layout). **Read this when writing or revising a blueprint
chapter** — adding nodes, prose proofs, citations, or deciding what merits an
entry. It is *not* auto-loaded (it is a plain reference like `RENDERING.md` /
`SETUP-AND-PITFALLS.md`); `blueprint/CLAUDE.md` *Authoring conventions* points
here.

For the node-annotation mechanics (`\lean{}` / `\leanok` / `\uses{}` order,
the sorry-blocked red-node convention) and the carleson-style baseline this all
follows, see `blueprint/CLAUDE.md` *Authoring conventions*.

## Authoring conventions (prose & editorial)

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

### Audience & vocabulary

The molecular-conjecture chapters (Phases 17–26) target a specific
reader: **a mathematician working in rigidity theory who knows
Katoh–Tanigawa 2011 but has not carefully studied its proof.** The
audience test for any word or phrase in prose is: *would a rigidity
theorist who has read KT know this term?* If the answer is no — because
it names a Lean identifier, a phase number, a sub-phase code, or a
dependency-graph status rather than a mathematical object — it does not
belong in reader-facing prose. (Adopted at the post-Phase-23 cleanup
round, `../notes/Phase23-cleanup.md`, after a survey found ~60–90
process-vocabulary passages across six molecular chapters, including
inside headline theorem statements.)

**Target style:**

1. **Statement = the mathematical claim, at KT's strength, full stop.**
   Lean-encoding matters (conditioned conjuncts, ambient data like the
   fresh-edge supply, which pinned decl covers which half) move to a
   short italicized *Formalization note* after the proof — at most one
   per node, only where the Lean genuinely diverges. (Earlier chapters
   used rare inline parentheticals for this; the note is the same
   device, fenced off so the statement can't re-absorb it.)
   **Calibration v2 (owner review of R1, 2026-07-03) — statement
   purity is strict:** a theorem/definition environment contains
   *only* the claim. "X means:" expansions of the statement's terms,
   essentiality/vacuity discussions ("dropping this hypothesis makes
   the iff false because…"), and methodological asides ("the rank must
   be read V(G)-relative…") all move OUT — to a `\begin{remark}` node
   after the theorem, to the section's connective prose, or (only for
   genuine Lean-encoding divergence) to the Formalization note. If the
   definitions were explained properly upstream, most such commentary
   shrinks. The calibration case: `thm:molecular-conjecture`'s
   statement carried both a "'Realized as…' means:" paragraph and the
   ≥2-body essentiality discussion.
2. **Proof = a mathematical narrative in KT's vocabulary.** `\cref`s
   ride as parenthetical anchors, never as grammatical subjects.
   Narrative blocks that already exist in a chapter's prose (a
   general-`d` chain dispatch, a case dichotomy, a multi-step
   construction account) become the backbone of the actual proof, not
   a parallel essay running alongside a dep-graph-traversal proof.
3. **Titles = KT anchor + short math description.** No internal node
   codes (`L4a`, `N7b-2`, `W1`, `(R1)`, `route-2`, `V6-b`, sub-phase
   tags) in titles.
4. **Preambles = a half-page mathematical roadmap** of the chapter's
   argument (what is proved, in what order, what the reader needs). No
   phase numbers, no dep-graph/forward-mode status, no standalone
   *Status.* paragraphs — the dep-graph color convention (and the
   forward-mode "leaf-most red node" workflow it encodes) is explained
   once, in `chapter/intro.tex`'s *Reading this blueprint* section; a
   chapter preamble should never re-explain it.
5. **Identifier rule:** *hypothesis names never appear in prose;
   declaration names appear only parenthetically at step boundaries, as
   addresses, not as nouns.* Every sentence must read as mathematics
   with the parenthetical deleted.
6. **Role-labeled pins.** When a node pins more than one Lean decl, the
   Formalization note ends with a one-clause-per-decl map ("Formalized
   as `foo_all_k`; the `d = 3` instance is `foo`"). If the roles are
   genuinely distinct theorems, prefer splitting the node.
7. **Findability rule.** Each step that gets a sentence in a proof
   narrative must either `\cref` a node (whose pin carries the link) or
   name its Lean declaration inline at that step. The prose is a
   complete index of the load-bearing declarations; helpers stay
   unpinned.
8. **All existing gates hold.** Restated statements must match the
   pinned Lean's strength (the honesty + definition-faithfulness gates
   above, `blueprint/CLAUDE.md`); `\uses` edges are preserved unless a
   node split/merge deliberately reshapes them; `verify.sh` + `lint.sh`
   stay green per commit.

**Calibration v2 (owner review of the R1 draft, 2026-07-03) — five
further rules:**

9. **KT numbering always carries the "KT" prefix.** The rendered
   blueprint has its own theorem numbering (Theorem 23.7, …), so a bare
   "Theorem 4.9" or "Proposition 1.1" is ambiguous. Every reference to
   a Katoh–Tanigawa-numbered result or equation reads "KT Theorem 4.9",
   "KT Proposition 1.1", "KT eq. (6.1)", "KT Conjecture 1.2" — in
   titles, statements, and proofs alike.
10. **Formalization notes are mathematical English, not Lean syntax.**
    No `\mathtt{}`-rendered Lean formulas (`∃ Q, Q.graph = G ∧ …`), no
    internal audit codes ("B1"). A note names the pinned declaration(s)
    and describes any divergence in prose; a reader who cannot read
    Lean must still understand it.
11. **Connective prose between nodes.** Each subsection opens with a
    short orienting paragraph (what the coming nodes do, in what order,
    and why), and load-bearing definitions get a lead-in or follow-up
    sentence in running text. The chapter should read as an article
    with embedded formal statements, not a list of environments.
12. **Multi-paragraph proofs.** A proof longer than ~8 source lines is
    broken into paragraphs (blank lines) by argument movement — setup /
    case analysis / conclusion. plastex renders blank lines as
    paragraph breaks; single-wall-of-text proofs are an authoring
    defect, not a renderer limit.
13. **The fresh-edge-label convention is explained once.** One
    reader-facing remark (where the supply hypothesis first appears)
    explains the ambient-label-type artifact: the formalization fixes
    an edge-label type once, so edge-adding surgery needs a supply of
    unused labels — a bookkeeping hypothesis with no analogue in KT,
    satisfied by any large-enough label type (`\cref` the
    satisfiability lemma / witness). Everywhere else points at that
    remark instead of re-explaining.

**Calibration v3 (owner review of the R1d draft, 2026-07-03) — three
further rules:**

14. **Register: the flat, even prose of a published paper.** The
    calibration exemplar is Katoh–Tanigawa 2011 itself (a local copy
    lives under `.refs/`; read a few pages of its running prose before
    writing or revising a chapter, and match that register). The
    defect this rule targets reads as *breathless*: every paragraph
    pointing out something special or unique, which distracts instead
    of orienting. Concretely: no per-paragraph significance-pointing
    ("the heart of", "crucially", "exactly the", "remarkably"); asides
    set off by em-dashes are rationed — most convert to separate plain
    sentences or are cut; mechanism metaphors ("feeds", "feeds into",
    "drives", "fires", "builds", "wires") are replaced by plain
    mathematical verbs ("satisfies", "is used in", "yields",
    "introduces", "describes"). A paragraph succeeds when a working
    mathematician could have written it without comment.
15. **Pin budget: a node pins what the reader should open, not the
    full API.** One Lean declaration per node is the target; two or
    three with a role-labeled map (rule 6) is the ceiling. A node that
    accrues four or more pins is doing lemma work inside a definition
    (or bundling several results): split the auxiliary facts into
    their own nodes, or leave API helpers unpinned (rule 7). The pin
    exists so a reader can follow the Lean alongside the prose; a
    many-name pin list defeats that.
16. **Definitions define and stop; Formalization notes sit outside
    every environment.** Rule 1's statement purity applies to
    definition nodes with full force: a definition environment
    introduces the object and ends — consequences, existence
    constructions, model comparisons, and design commentary move to
    the surrounding prose or a remark (match how definitions read in
    the `.refs/` papers). And the *Formalization note* device is
    placed after the environment (after the proof for theorem-like
    nodes, directly after the environment for definitions) — never
    inside the statement block.

**Calibration v4 (owner review #3 + a two-reviewer KT-style audit,
2026-07-03) — one further rule:**

17. **A statement states; it does not situate.** Model every
    theorem-like statement on KT's own: *"Let [setup]. (Suppose […].)
    Then, [claim]."* — 1–4 sentences (KT's longest sampled, Lemma 6.5,
    is four), extendable only by a notation gloss ("where
    $D = \binom{d+1}{2}$") or a further-*mathematical* "i.e. / in
    particular" restatement. Every sentence inside the environment
    must be a hypothesis, the claim, or such a gloss. Four content
    classes read as flat mathematics and so survive rules 1/14/16 —
    all are banned inside statements: **(a) role/positioning** ("this
    is the transversality X requires for Y", "the entry point for …",
    "the general-$m$ generalization / sibling / companion of …");
    **(b) comparisons** ("by contrast …", "the one case where …");
    **(c) construction/proof material** — the witness, the reason,
    the method — which moves to the proof, where it usually already
    appears; **(d) Lean identifiers** — `\mathrm{}`/`\texttt{}`
    predicate or declaration names, which move to the Formalization
    note. Attribution stays — as the title's bracket or one plain
    sentence, never dressed as a role clause. Two mechanical tests
    before committing a statement: *(i) deletion test* — delete every
    sentence that is not hypothesis / claim / gloss; if what must be
    proved is unchanged, the deleted text was connective prose in
    disguise and belongs outside the environment. *(ii) standalone
    test* — the statement must read as if no other node in the
    chapter existed; a sentence naming what another node needs,
    generalizes, or contrasts with fails. The tell is a trailing
    sentence beginning "This is …". (Calibration: two-thirds of the
    R1e panel-layer nodes failed these tests while the flagship
    theorems passed — the earlier rules fixed the flagships without
    propagating to the supporting cast.)

**Terminology dictionary** (settled at the post-Phase-23 cleanup round;
extend it rather than inventing a parallel list):

| project term | replacement in reader-facing prose |
|---|---|
| brick | rank-addition lemma / rank bound (KT §6.1 language) |
| motive | induction statement / realization predicate (define once if kept at all) |
| producer | realization lemma / existence lemma |
| stratum, strata | drop (or "stage") |
| carry / adjudicated carry | rewritten away (a deferred hypothesis, named mathematically) |
| the `hub` bound | the motion-space lower bound + `\cref` to its lemma |
| arm / fire / route / spine / wire | plain mathematical prose |
| green / red / leaf-most / live to-do list | only in `intro.tex`'s one dep-graph note |
| Lean hypothesis names (e.g. `h622`, `hsplit`, `hsplitGP`, `hcontract`, `hcSimple`, `hgen`, `hcut`, `hD`, `h65`, `M4`) | never in prose (identifier rule 5 above) |

Lean file/section names (e.g. `Bricks.lean`) are invisible to blueprint
readers and are unaffected by this table.

