# Phase 28 — Retroactive blueprint scan: exposition coverage + non-molecular readability (work log)

**Status:** in progress (opened 2026-07-08; scope broadened 2026-07-08).

## Current state

**Next concrete step: the full A–F readability sweep of `matroid-union.tex`
(P12)** — next chapter in the Workstream 2 checklist (it already had the
principle-F pre-pass, phase numbers cleared; now gets its full sweep). Follow
the calibration bar set by the nine completed sweeps `sparsity.tex`,
`laman.tex`, `henneberg.tex`, `frameworks.tex`, `henneberg-rigidity.tex`,
`laman-theorem.tex`, `trivial-motions.tex`, `rigidity-matroid.tex`,
`count-matroid.tex` (see *Decisions made → calibration calls*). Run the
`AUTHORING.md` R-task order (B→E→C→D→A→F), preserving statement strength and
`\uses`/`\lean{}` pins; gate with `blueprint/lint.sh` + `blueprint/verify.sh`.
Workstream 1 (the retroactive
exposition-coverage scan) is **complete** — every candidate across the
molecular (Group B) and non-molecular (Group A) sweep screened **OUT** against
the ledger's source-side inclusion criterion, so no new ledger entries and no
blueprint prose landed (the header's 30-done count is unchanged). See the
*Retroactive coverage* records in `notes/BlueprintExposition.md`.

The phase was broadened at owner request (2026-07-08): the exposition-coverage
scan answers *"is there an un-exposited hard KT-math argument deserving a
detailed crux node?"* — it does **not** evaluate whether the existing prose
conforms to the current `blueprint/AUTHORING.md` A–F authoring principles +
terminology dictionary. Those were adopted at the post-Phase-23 cleanup round
and the R1–R9 readability rewrite applied them to the **molecular chapters
(17–26) only**; the non-molecular chapters (1–16) have never had that sweep.

## Workstream 1 — retroactive exposition-coverage scan (DONE)

Defined by the ledger's *Retroactive coverage → Scheduled retroactive scan*
bullets (`notes/BlueprintExposition.md`, set 2026-06-21). Run cleanup-style
over two groups; **both fully adjudicated, all OUT** (2026-07-08). No new
ledger entries, no prose, no `.tex`/`.lean` touched. Full reasoning lives in
`notes/BlueprintExposition.md` *Retroactive coverage*; the one-line verdicts:

- **Group B — the two un-ledgered molecular candidates: both OUT.** *22i
  (all-`k` genuine-hinge motive)* — project-side (a vacuous-pre-22i-motive →
  faithful-strengthening slip, `DESIGN.md` *Statement faithfulness to the
  source*; carrier split is excluded Lean-modelling; the one source-side kernel
  KT Lemma 5.3 is already exposited at `lem:rank-parallel-full`). *23a
  `linearIndependent_normals_of_algebraicIndependent_triple`* — routine
  det-polynomial "generic ⟹ LI" (mathlib-standard; KT never states it).
- **Group A — non-molecular phases 1–16: all screened OUT.** The flagged
  likely-IN Phase 5 Laman blocker argument (Jordán 2016 Lemma 2.1.4(b),
  verified pp.43–45) is a genuine source-side argument whose kernel is
  *already* exposited node-by-node (`thm:isTightOn-union-inter/-with-bonus`,
  `lem:isSparse-typeII-reverse-blocker`, `thm:isSparse-exists-typeI-or-typeII-reverse`);
  its un-exposited residual is project-side Lean bookkeeping. The rest screened
  OUT as reuse-heavy / matroid-standard / algorithmic.

## Workstream 2 — non-molecular A–F readability sweep (IN PROGRESS)

**The finding.** The `AUTHORING.md` six A–F principles (register, statement
hygiene, proof narrative, formalization notes, fidelity/anchoring, chapter
flow) + terminology dictionary were adopted at the post-Phase-23 cleanup round.
The R1–R9 readability rewrite that applied them hit the **molecular chapters
only** (panel-layer, case-i/ii/iii, genericity-and-count, rigidity-matrix,
molecular-induction, meet, deficiency, extensor). The non-molecular chapters
got at most R10's *light framing pass* (body-bar/body-hinge preamble) and R11's
*spot pass*; the core early chapters had **no A–F sweep at all**. The `lint.sh`
vocabulary gate does not backstop this — its banned list is molecular-flavored
(brick/motive/producer/…), and the principle-A issues (mechanism metaphors,
significance-pointing) are judgment calls, not scriptable. A grep confirms
concrete drift: mechanism metaphors (`feeds`/`carries`/`fires`/`threads`) and
significance-pointing (`The key`) across sparsity, laman-theorem, frameworks,
rigidity-matroid, pebble-game, executable, body-bar, body-hinge — a mix of real
violations and legitimate math usage (principle A is a judgment call).

**Method — per chapter, follow the `AUTHORING.md` R-task sweep order:**
statements first (B: deletion + standalone tests, move what fails), then the
anchor sweep (E, reading backward: every term of art / construction / symbol a
proof or note uses has met its introduction), then proofs (C), then notes &
pins (D), then the vocabulary/register greps (A: the terminology dictionary +
the significance-pointing / mechanism-metaphor bans), then preamble/connective
prose (F). The forward fidelity checks of E ride with the B/C passes.
**Preserve the math:** restated statements match the pinned Lean's strength
(honesty + definition-faithfulness gates), `\uses` edges and `\lean{}` pins are
preserved unless a node split/merge genuinely reshapes them — this is *prose
revision*, not re-statement. Gates: `blueprint/lint.sh` per commit, +
`blueprint/verify.sh` if any `\lean{}`/`\uses`/`\label` is touched. No
`lake build` (no Lean).

### Chapter checklist (one chapter per commit; group tiny adjacent ones)

- [x] `sparsity.tex` (P1) — **calibration chapter, DONE.** Full B→E→C→D→A→F
      sweep; sets the bar (calibration calls under *Decisions made*).
- [x] `laman.tex` (P2) — **DONE.** Full B→E→C→D→A→F sweep (calibration calls
      under *Decisions made*).
- [x] `henneberg.tex` (P3) — **DONE.** Full B→E→C→D→A→F sweep (calibration
      calls under *Decisions made*).
- [x] `frameworks.tex` (P4) — **DONE.** Full B→E→C→D→A→F sweep (calibration
      calls under *Decisions made*).
- [x] `henneberg-rigidity.tex` (P5) — **DONE.** Full B→E→C→D→A→F sweep
      (calibration calls under *Decisions made*).
- [x] `laman-theorem.tex` (P5–6) — **DONE.** Full B→E→C→D→A→F sweep
      (calibration calls under *Decisions made*).
- [x] `trivial-motions.tex` (P6) — **DONE.** Full B→E→C→D→A→F sweep
      (calibration calls under *Decisions made*).
- [x] `rigidity-matroid.tex` (P6–8) — **DONE.** Full B→E→C→D→A→F sweep
      (calibration calls under *Decisions made*).
- [x] `count-matroid.tex` (P7) — **DONE.** Full B→E→C→D→A→F sweep
      (calibration calls under *Decisions made*).
- [ ] `matroid-union.tex` (P12) — principle-F pre-pass only (phase numbers cleared); full A–F sweep pending
- [ ] `dfs.tex` (P9)
- [ ] `pebble-game.tex` (P9–11)
- [ ] `executable.tex` (P10)
- [ ] `body-bar.tex` (P13–15) — R10 gave the preamble a framing pass; needs the full A–F sweep
- [ ] `body-hinge.tex` (P16) — R10 partial; needs the full A–F sweep
- [ ] `intro.tex` — a **final light pass** only (reader-guide/status-surface
      discipline, not the full chapter sweep); confirm it still reads jargon-free

## Red-node consistency gate — N/A (judgment, not omission)

RETROSCAN opens to *scan* + *revise prose*, not to build already-stubbed
blueprint nodes — the whole program is green + axiom-clean. The gate (which
forces a pre-build re-read of target red nodes) is a no-op here by design. The
readability sweep touches only already-green nodes' prose; `lint.sh`/`verify.sh`
+ the honesty/definition-faithfulness gates cover it.

## Blockers / open questions

None.

## Hand-off / next phase

**Smallest next commit: the full A–F readability sweep of `matroid-union.tex` (P12)** —
run the `AUTHORING.md` R-task order (B→E→C→D→A→F) over it, preserving statement
strength and `\uses`/`\lean{}` pins, gate with `blueprint/lint.sh` +
`blueprint/verify.sh`. `matroid-union.tex` already had the principle-F pre-pass
(phase numbers cleared); this is its full sweep. Hold it to the completed
`sparsity.tex`/`laman.tex`/`henneberg.tex`/`frameworks.tex`/`henneberg-rigidity.tex`/`laman-theorem.tex`/`trivial-motions.tex`/`rigidity-matroid.tex`/`count-matroid.tex`
calibration bar (*Decisions made → calibration calls*). Then proceed down the chapter checklist
in reading order (one chapter per commit, grouping tiny adjacent ones). When the
checklist is clear, the phase
reaches close: run the phase-close checklist (`PHASE-BOUNDARIES.md`), which for
this phase means flipping + re-thinning the ROADMAP row, compressing §28,
confirming the arc-level public status surfaces, and the end-to-end
blueprint re-read (now covering the swept chapters). The exposition-coverage
scan (Workstream 1) is already recorded done.

## Decisions made during this phase

### Phase-local choices

- **`sparsity.tex` calibration calls (the bar for the rest of Workstream 2).**
  Rewrote the mechanism metaphors `driven by`/`feeds`/`powering` and the
  significance-pointing `combinatorial heart of`/`main structural fact` to plain
  math; dropped `API`, `selector`, `on the nose`, `milestone`, and the `Phase~5`/
  `Phase~7` prose pointers (sub-17 phase numbers were then a *manual*
  principle-F catch; now gate-enforced — see the gate-hardening entry below).
  Moved the def:isSparse ℕ-subtraction
  aside and the def:isTightOn role clause + Jordán "critical set" terminology out
  of the statements (B); the typeII proof's `Sym2.map`/`comap`/`Subtype.val`
  formula into a plain-English `fmlnote` (D). **Kept as legitimate:** "vertex
  type" (project-wide convention, not a dictionary term), the map $\edgesIn{\cdot}$
  "distributes"/"transports" (standard math verbs, not mechanism metaphors), and
  the one deletable parenthetical Lean address `(mathlib's SimpleGraph.incidenceSet)`
  at a notation-introduction (passes principle A's parenthetical-deletion test).
  Jordán §2.1 "critical set" citation *preserved verbatim*, not re-verified (prose
  move, not a citation audit).
- **`laman.tex` calibration calls (P2).** A: dropped `API` and the mechanism
  metaphors `feed`/`lever` (→ "supply" / "the degree conditions the Henneberg
  induction uses"). B: dropped the Lean type ascription from the $K_2$ statement
  (`$\top : \mathrm{SimpleGraph}(\mathrm{Fin}\,2)$` → "the complete graph $K_2$
  on two vertices"; `\lean{}` carries the exact object). E: first chapter to use
  `\top` for the complete graph — glossed it at first occurrence. **Kept
  legitimate:** `\top` as lattice notation (glossed, not banned); "vertex type";
  "$n$ vertices"/"bottoms out"/"collapses"/"specialize" as plain math; Type~I/II
  + Henneberg anchored in `intro.tex` (`sec:intro`). Prose-only (no ref-token
  changed); verify.sh green anyway.
- **`henneberg.tex` calibration calls (P3).** A: significance-pointing
  (`combinatorial heart of`, `headline`) and metaphors (`lever`, `feed`,
  `consumed`, `bumps`, `dispatch`, `wrinkle`, `in disguise`) → plain math;
  `iso` → "isomorphism"; `formalises` → `introduces`/`shows`. B: moved the
  def:typeI degree/collapse and def:typeII well-definedness + four-hypothesis
  notes out of the definitions to connective prose, and the
  lem:typeII-edgeSet-ncard "we do not assume $\{a,b\}\in E$" note out of the
  statement. C: split the reverse-decomposition proof into three paragraphs
  (setup/pendant, Type~I, Type~II); `typeII G' a b c` (was `x y c`) to match
  the statement's neighbor labels. D: two `fmlnote`s — the
  `Option`/`none`/`some` encoding rationale (def:typeI) and the
  flat-vs-operation statement-shape discussion (Laman reverse decomp),
  consolidating the two duplicated prose asides and relocating the
  `\cref{sec:rigidity-matroid-lifts}` pointer. F: dropped the flat-form aside
  from the preamble (now a phase-free roadmap); added Preservation /
  Worked-example lead-ins. **Kept legitimate:** "transports"/"collapses"/"raises"
  as plain verbs, "vertex type", the `\none`/`\some` notation, the project
  "bridge" term (self-glossing, from sparsity.tex), "pendant"/"$G[\{w\ne v\}]$"
  (self-glossed). Touched `\cref` (fmlnote relocation) → verify.sh; both green.
- **`frameworks.tex` calibration calls (P4).** A: dropped significance-pointing
  (`headline result` → `the section closes with`); dropped `API` (subsection
  `Rigidity-map API` → `Rank and kernel bounds`); `graph iso` → `graph
  isomorphism` (prose + three lemma titles); `vanilla` → `plain`; rewrote the
  ker-mono proof's `kills` to `vanishes on`/`value 0`, and the openness intro's
  `the analytic input that lets us` to plain math. B: dropped Lean type
  spellings from statements (`EuclideanSpace ℝ (Fin d)` → `\R^d` in
  def:framework; `G : SimpleGraph V` → `a graph G on V`; `d : ℕ` → `d ∈ ℕ`),
  and moved role/interpretation clauses out of three definitions (rigidityMap
  well-definedness; isInfinitesimallyRigid's ≤-vs-= interpretation, dropped as
  the preamble covers it; isGenericallyRigidInj's strictly-stronger/Henneberg-use
  clause → connective prose) plus the `card_mul_le` ℕ-subtraction aside. C: split
  the openness proof by argument movement; made the finrank proof's mathlib name
  parenthetical, not imperative. D: two `fmlnote`s — the
  entry-formula-not-differential modelling choice (def:rigidityMap) and the
  additive-vs-ℕ-subtraction statement shape (card_mul_le). F: rebalanced the
  preamble (dropped `headline`, moved the differentiability-machinery aside into
  the fmlnote), added lead-ins to three subsections. **Kept legitimate:** a map
  "carries"/"transports" a placement (standard verbs); `\mathrm{RigidityMap}`,
  `\mathrm{Framework}` as project notation; `\R^d` glossed as Euclidean $d$-space
  at first use; mathlib lemma names as parenthetical addresses; the "$n$ vertices"
  idiom. Touched `\cref` (relocations + one added) → verify.sh; both green.
- **`henneberg-rigidity.tex` calibration calls (P5).** A: rewrote the
  significance/mechanism words `delicate`, `genuinely`, and Lean-ish `wrapper`
  to plain math; `kills every $G$-edge` → "vanishes on" (frameworks precedent);
  `not parallel to` → "linearly independent"; the opaque "cofinite $\alpha$-set"
  → "all but finitely many points on the line"; normalized `dim 2` →
  "dimension 2" in titles, the three spellings of "one-parameter", and
  `kernel-dim` → "kernel-dimension". B: dropped `$G : \mathrm{SimpleGraph}\,V$`
  → "a graph $G$ on $V$" from all five statements (`\lean{}` carries the object).
  C: the Type~I generic-rigidity proof's cref-as-subject → cref parenthetical;
  the numbered hypotheses referenced as "the first/second hypothesis" (the
  enumerate renders arabic, mismatching the prose's roman "(i)/(ii)"). E:
  normalized the Lean dot-projection `G.\mathrm{RigidityMap}\,p` → the
  applicative `\mathrm{RigidityMap}\,G\,p` from `frameworks.tex`. D: no fmlnote
  (the `Option`/`none`/`some` encoding is noted upstream in `henneberg.tex`).
  **Kept legitimate:** "transports"/"pin(s)"/"lands in" as plain math, the
  `none`/`some`/`Option V` vertex-type notation, `\R^2` (glossed upstream), the
  "$p_0(a)$" form (placement already subscripted). Touched `\cref` (one
  relocation) → verify.sh; both green.
- **`laman-theorem.tex` calibration calls (P5–6).** A: `iso`/`iso transport`
  → "isomorphism"/"transport … along that isomorphism"; mechanism/register words
  `hands back`, `feeds`, `ships`, `consumes`, `basis-pick` → plain math;
  `genuinely property-agnostic`/`property-polymorphic` → "open property";
  `IR witness` → "infinitesimally rigid placement"; dropped the Lean `flat form`
  shape word and two `rfl`-on-`Nat` Lean-noise sentences; titles `d-general` →
  "general dimension", `dim 2` → "dimension 2" throughout. B: dropped
  `$G : \mathrm{SimpleGraph}\,V$` → "a graph $G$ on $V$" from four statements;
  dropped the Lean-dot display `G.\mathrm{IsGenericallyRigid}\,2 \iff \exists
  H \le G, H.\mathrm{IsLaman}` from the headline (prose states it; `\lean{}`
  carries the object). C: rewrote the assembly proof's `feeds the placement-fixed
  companion` and the Sym2 `canonical lift` bijection to math. D: converted the
  "Statement-form aside" (polymorphic-statement rationale) to one `fmlnote` on
  `lem:exists-affinelySpanning-of-eventually`; fixed two malformed
  `E(G)\to\R\to…` projection displays (restriction / evaluation maps). E:
  `\cref`'d `def:isLaman` (preamble first use) and `def:isSparse` (proof);
  de-`\emph`'d the imported "trivial Euclidean motions" (anchored via
  `\cref{sec:trivial-motions}`). **Kept legitimate:** "transports"/"supports"/
  "peel off a move" as plain verbs; `RigidityMap`/`Framework`/`rigidityRow`
  project notation and `\rk`; mathlib names as parenthetical addresses; the
  matroid remark (rewritten to name the rigidity matroid + `\cref` where it is
  assembled, dropping "off the critical path"/`Mathlib.Combinatorics.Matroid`);
  the "Equivalently, … has rank $|I|$" definitional restatement (principle-B
  "i.e." gloss). Touched `\cref` → verify.sh; both green.
- **`trivial-motions.tex` calibration calls (P6).** A: `consumes` → "uses",
  `driven by` → "associated to", `kills` → "cancels", `w.r.t.` → "with respect
  to"; dropped `API`; titles "d-general finrank lower bound" → "dimension lower
  bound" (dropped the Lean word `finrank` and "d-general" from the subsection +
  two lemma titles; general-$d$ scope stated in the preamble). B: dropped
  `$G : \mathrm{SimpleGraph}\,V$` → "a graph $G$ on $V$" (kernel-bound lemma);
  dropped `\top` from the linear-independence statement ("affine span $\top$" →
  "affinely spanning", matching the sibling statements); moved def:elemSkewMap's
  anti-symmetry / skew-matrix-form consequences out of the definition to a
  following sentence. C: rewrote the linear-independence proof's Lean `inl`/`inr`
  coefficient subscripts and `vectorSpan`/`range`/`\top` to plain math ($c_i$,
  $c_{i,j}$; "the differences span $\R^d$"), split it into two paragraphs by
  movement; made the two mathlib names parenthetical addresses, not grammatical
  subjects. D: one `fmlnote` on def:trivialMotionFamily for the index-set
  encoding ($\mathrm{Fin}\,d \sqcup \Sigma$, the $\mathrm{Fin}\,i \hookrightarrow
  \mathrm{Fin}\,d$ re-embedding), and simplified the definition's inline
  `.val`/$j'$-embedding bookkeeping to clean "ordered pairs $(i,j)$,
  $0 \le j < i$". E: `\cref`'d imported `def:framework`/`def:rigidityMap` at
  first (preamble) use. F: one-sentence lead-ins on the Translations /
  Infinitesimal-rotations / submodule subsections. **Kept legitimate:** `\to_\R`
  linear-map notation and $\dim_\R$ (established in `frameworks.tex`), "affinely
  spanning" (standard term, no def node), "generator"/"span"/"cancels" as plain
  verbs. Touched `\cref` → verify.sh; both green.
- **`rigidity-matroid.tex` calibration calls (P6–8).** A: expanded the chapter's
  pervasive `row-LI`/bare `LI` shorthand → `row-independent`/`linearly
  independent`/`linear independence` (0 occurrences across the 7 completed sweeps
  set the bar); dropped significance/register words `technical heart of`, `feeds`,
  `structurally meaningful`, `linear-algebra-flavoured`, `IH`; titles `iso`→"graph
  isomorphism", `dim 2`→"dimension 2"; proofs `dualMap`→"dual map",
  `IndepMatroid`/`Matroid` instance→"matroid". B: dropped
  `$G : \mathrm{SimpleGraph}\,V$`→"a graph $G$ on $V$" (10 statements); removed the
  undefined term "exposed" from the reverse-decomposition statement (restated the
  neighbour data plainly, matching the sibling Laman statement); moved the pendant
  role-clause and the Type~II `p|_V`-perturbation clause out of statements; dropped
  the `G.IsTightOn` Lean expression from the Terminology paragraph. C: split four
  dense proofs into paragraphs by movement; rewrote the `rfl`-after-`Sym2`-induction
  Lean-noise sentence to "the equality is definitional". D: converted the
  "Statement-form aside"→labelled `fmlnote:reverse-vs-lift-form` (henneberg's
  cross-ref repointed to it, was `\cref{sec:rigidity-matroid-lifts}`), the
  def:linearRigidityRow `Function.extend` parenthetical→fmlnote, and the corollary's
  `@[deprecated]` shim detail→fmlnote. E: `\cref`'d `def:edgeSet-rowIndependent` at
  preamble first use, glossed `K_V` ("complete graph on $V$"), normalized the Type~I
  extend lemma's undefined `p_a`/`p_b`→`p'_a`/`p'_b`. **Kept legitimate:**
  `Matroid.ofFun` as the named linear-matroid construction (glossed), the
  `apnelson1/Matroid` provenance address, `Framework`/`rigidityRow`/`\R^d` project
  notation and mathlib names as parenthetical addresses, "vertex type"/"$n$
  vertices". Touched `\cref`/`\label` (fmlnote + henneberg repoint) → verify.sh; both green.
- **`count-matroid.tex` calibration calls (P7).** A: dropped `combinatorial
  heart of`, `scaffolding`/`runs on`, `consumes`→"uses", `\texttt{Matroid}`→
  "matroid", "sparsity predicate"→"condition", "flavour"→"kind"; expanded the
  mathlib axiom field names (`indep\_empty`/…/`indep\_aug`) into plain-math axiom
  statements. B: dropped the Lean dot-expressions (`(fromEdgeSet I).IsSparse k ℓ`
  in def:countMatroid's display; `\mathtt{(fromEdgeSet I).IsTightOn}` in the
  Terminology aside) and the redundant `k ≥ 1` hypothesis (implied by `ℓ < 2k`
  over ℕ; not in the pinned Lean) from the three matroid statements; stripped
  def:isSparse-maxBlock to just the object (`maxBlock` is defined for any graph
  in Lean — dropped the sparsity hypothesis + consequences/role clauses to a
  connective lead-in); trimmed lem:isSparse-maxBlock-isTightOn to its pinned
  conclusion (tightness), "largest/`I`-component" → prose. E: introduced the
  shorthand *`I`-tight* once in Terminology (was unglossed); de-`\emph`'d the
  re-introduced `I-component`/`edge-disjoint`; introduced *free* (edge) in the
  aug proof before use (was an undefined "non-free"); fixed the **malformed**
  `\edgesIn{\cdot}{S}` (placeholder as mandatory arg → stray `S`). "Finset" →
  "finite subset" throughout (0 occurrences in the completed sweeps). C: kept the
  aug proof's four movements; `Now compute`→"Now count", `\bigsqcup`→`\bigcup`,
  "Finset-lattice join"→"union". D: no fmlnote. F: phase-free roadmap +
  aug-subsection lead-in; **corrected an outdated claim** — the closing said the
  pebble game "this project does not pursue", but P9–11 formalise it, so rewrote
  it to attribute the pebble game to Lee--Streinu and point forward to
  `\cref{sec:pebble-game}` (new cref; +1 `\cite{leeStreinu2008}`). **Kept
  legitimate:** `fromEdgeSet`/`maxBlock`/`\mathrm{Sym}_2 V`/`E(K_V)` (all glossed
  in the preceding `rigidity-matroid.tex`), `IndepMatroid.ofFinite` as a
  parenthetical address, "off-diagonal", Jordán's `M`-circuit/`M`-connected-
  component + "critical set" citations verbatim. Touched `\cref`/`\cite` →
  verify.sh; both green.
- **Gate hardening: check 5b now catches all `Phase~N`/`Phase-N` outside
  `intro.tex`** (owner-sanctioned between-sweep commit). Generalized
  `blueprint/lint.sh`'s check-5b regex from `Phase~17`–`Phase~29` to
  `[Pp]hases?[-~ ][0-9]` (any number; `~`/space/hyphen separator), keeping the
  `22a`–`23l` sub-codes and the `intro.tex` exemption. The sparsity/laman
  calibration's manual sub-17 `Phase~N` grep is now gate-enforced — later
  chapter sweeps no longer need it. Cleared the 6 sub-17 stragglers as a
  **narrow principle-F pre-pass** on `laman-theorem`/`matroid-union`/
  `rigidity-matroid` (dropped phase numbers + one `milestone~1`; `\cref`'d the
  actual node or named the result mathematically); prose-only, no ref-token
  changed. Of those 3, `laman-theorem.tex` and `rigidity-matroid.tex` have since
  had their full A–F sweeps; `matroid-union` still needs its (item unticked).
- **Scope broadened to add the non-molecular A–F readability sweep**
  (owner-adjudicated 2026-07-08). The exposition-coverage scan (Workstream 1)
  answers a different question (KT-math crux coverage) than prose conformance;
  the non-molecular chapters 1–16 were never A–F-swept (R1–R9 were molecular).
  Folded into Phase 28 (owner call) rather than a separate cleanup round,
  though it is a cleanup-flavored R-task sweep.
- **Workstream 1 (exposition-coverage scan): both groups OUT, no new entries.**
  Provisional "source-side" reads were hints; checked against the *landed*
  source (KT/Jordán text + landed Lean), none held. 22i is project-side
  (`DESIGN.md` *Statement faithfulness to the source*), the 23a triple is
  routine LA, and the Phase 5 blocker's kernel is already exposited. Both
  recorded as no-entry judgments; no forced entry. Full reasoning:
  `notes/BlueprintExposition.md` *Retroactive coverage*.
- **22i's project-side story is captured for RETRO, not written here.** It is
  already inventoried in `notes/FormalizationRetrospective.md` (the
  "`def:rank-hypothesis` vacuity slip" item, now cross-referencing the 22i
  carrier-strengthening angle); the full wrong-turns narrative is the deferred
  RETRO phase's deliverable, not RETROSCAN's, and the vocabulary gate bars the
  `motive`/`carrier` framing from chapter prose.
- **No public-status-surface edit** (matching the Phase 27 precedent). README /
  `home_page/index.md` / `intro.tex` carry status at the arc level
  ("phases 1–26 complete, no `sorry`s"); neither the scan nor the readability
  sweep changes the mathematical state. (The sweep *does* touch `intro.tex`
  prose for jargon-freeness — a reader-guide pass, distinct from the status
  claim.)
