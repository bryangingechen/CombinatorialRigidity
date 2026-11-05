# Phase 42 — PENCIL-D: design (cross-phase plan and recon)

**Status:** opened 2026-10-29 with the PI, sub-lettered, research first; **42m open**.
**42m** (PD-HEAD's `-generic`, `notes/Phase42m.md`) **opened 2026-11-05** at the PI's word (§1): the
eleven nodes of `pencil-d.tex`'s `-generic` (the cases of an induction on the bodies at few bodies,
a cut edge, a body of degree one, a pendant triangle, no planar-rigid set and a body of degree two
with hub neighbours; finding that body and its condition; the generic theorem and the headline) as
the chapter states them (§3). They are the blueprint's last red nodes, so its close is Phase 42's.
Its pre-build recon landed (§3): all eleven signatures kernel-checked, three nodes spiked complete
and the theorem and headline assembled on the rest; next, the first of seven builds.
**42l** (PD-HEAD's `-nondegenerate` and `-lift`, `notes/Phase42l.md`) **opened and closed
2026-11-04** at the PI's word (§1): the ten nodes of `pencil-d.tex`'s `-nondegenerate` and `-lift`
(nondegeneracy in dimension `d`, its agreement at `d = 3`, linear maps, feasibility in every
dimension, a parametrization in dimension three, lifts, lifts are nondegenerate, the general lift
attains, one lift suffices, lifts restrict to a subgraph), all green, as the chapter states them,
in four builds from its recon's spikes (verdict §3; at the PI's word, §1, the parametrization's
statement takes the Lean's six auxiliary vectors). PD-HEAD's other half, `-generic`, then opened
as 42m.
**42k** (PD-REDUCTION, `notes/Phase42k.md`) **opened and closed 2026-11-04** at the PI's word
(§1): the eight nodes of `pencil-d.tex`'s `-reduction` (a hinge in two pencils, moving a
realization by a linear map, moving one side of a cut edge, the cases at a loop, on at most two
bodies, at a cut edge and at parallel edges, and the realization theorem in every dimension), all
green, as the chapter states them, in three builds from its recon's spikes (verdict §3).
**42j** (PD-COVERAGE, `notes/Phase42j.md`) **opened and closed 2026-10-31** at the PI's word (§1):
the four nodes of `pencil-d.tex`'s `-chains` and `-coverage` (the chain count, a long chain or a
core, the coverage in every dimension and the distinct statement), all green, as the chapter
states them, in three builds from its recon's spikes (verdict §3).
**42i** (the fourth and last sub-phase of PD-STEPS, `notes/Phase42i.md`) **opened and closed
2026-10-31** at the PI's word (§1): the four nodes of `pencil-d.tex`'s `-short-three`, the open ear
with three interior bodies, all green, the theorem at `d = 4` to `6` as the chapter states it, on
a variant of 42h's factoring its recon pinned (verdict §3; at the PI's word, §1, stars-three's
statement and proof follow its Lean).
**42h** (the third sub-phase of PD-STEPS, `notes/Phase42h.md`) **opened and closed 2026-10-31** at
the PI's word (§1): the eight nodes of `pencil-d.tex`'s `-short-four`, Phase 40's short-ear step in
`Pᵈ` at four or more interior bodies, all green, their Lean in every `d` (verdict §3; at the PI's
word, §1, two-stars is stated on forms and stars-four's proof follows its Lean).
**42g** (the second sub-phase of PD-STEPS, `notes/Phase42g.md`) **opened 2026-10-30 and closed
2026-10-31** at the PI's word (§1): the seven nodes of `pencil-d.tex`'s `-long`, Phase 40's cycle
and long-ear steps in `Pᵈ` on CERT's closed polygons, all green (verdict §3).
**42f** (the first sub-phase of PD-STEPS, `notes/Phase42f.md`) **opened and closed 2026-10-30** at
the PI's word (§1): the six nodes of `pencil-d.tex`'s `-cut` and `-contract`, Phase 40e/40f/40k in
`Pᵈ`, all green (verdict §3); its open also cut three step nodes no coverage step uses (§1, §3).
**42e** (PD-CARRIER, `notes/Phase42e.md`) **opened and closed 2026-10-30** at the PI's word (§1):
formalizing 42d's proof began with its setting and the flat rank, four nodes of `pencil-d.tex`,
all green (verdict §3).
**42a** (PD-RECON, `notes/Phase42a.md`) **closed 2026-10-30**: the step table (§2.1), the thresholds
and the content `def[3] ≥ C(d,2) − 2` (§2.5), T1–T5 (§2.4), ONE-CLASS (§2.3, Result 27) and
SHORT-CORE's attack track (§2.3; closed 2026-10-30, `notes/attacks/short-core/state.md`): the
coverage's only new mathematics, the short ears at `d = 4`, is proved by hand, and from `d = 5` on
the coverage never needs the 3-body short ear, given CERT's open ears (proved at every `d`, 42d).
The route is the PI's (§1):
R2's steps, Result 15's embedding as the base row, any induction on `d` left to Tier 2. **42b**
(PD-STATE, `notes/Phase42b.md`) **closed 2026-10-30**: the statement layer in `Pᵈ`, its chapter
`blueprint/src/chapter/pencil-d.tex` formalized (17 nodes), on the carrier the PI took (§1, option
(a); §2.3 CARRIER). **42c** (PD-STABLE, `notes/Phase42c.md`) **closed 2026-10-30**: the embedding,
the sharp deficiency lemma and `Pᵈ` at `def[3] ≤ 3` (Tier 0, which the PI widened from `≤ 1`, §1),
`pencil-d.tex`'s section `sec:pencil-d-stable`, formalized (9 nodes; verdict §3). **42d** (PD-ALL,
`notes/Phase42d.md`) **opened and closed 2026-10-30** at the PI's word (§1): an informal proof at
every `d` of the conditioned pair's three conjuncts, the generic one included, as red nodes of
`pencil-d.tex` (verdict §3), from three tracks (CERT, NONDEG, WRITE-UP) run by `/coordinate-tracks
42d`. Evidence: `notes/Strata.md`, Results 12–27.

This file is the phase's entry point: the target (§0), the PI's decisions (§1), the recon (§2),
the layers by stable code (§3) and the open questions (§4). Letters are minted when a sub-phase
opens (`PHASE-BOUNDARIES.md`); until then the stable codes of §3 name the layers.

## 0. Target

**The `Pᵈ` pencil conjecture.** Let `G` satisfy `def:pencil-x0-standing` (finite, simple,
connected, minimum degree at least two), and let `d ≥ 2`. Take a general picture `q` and general
heights `z¹, …, z^{d−2} ∈ L(q)`. Then the hinges `b_u ∧ b_v`, with
`b_v = (q_v, z¹_v, …, z^{d−2}_v, 1)` (`Strata.md` Result 13), have rank `D(n−1) − def_D(G)`,
`D = C(d+1, 2)`. The headline is the multigraph form, Phase 39's `PencilPair` in dimension `d`,
through Phase 39's reduction.

Status: `d = 2, 3` are proved and formalized (Phases 40a, 40). Every `d` with `def_3 ≤ 1` is
`Strata.md` Result 17, and every `d` at `def_3 ≤ 3` follows from Result 17's proof with the sharp
deficiency lemma, proved and formalized (42c, `thm:pencil-d-deficiency-two-le-three`). Every `d` is
proved on paper (42d, `cor:pencil-d-conditioned-pair`); formalizing it began with the setting and
the flat rank (42e), then the induction's cut-vertex, bridge and contraction steps (42f), its
cycle and long-ear steps (42g), its short-ear step at four or more interior bodies (42h) and at
three, at `d = 4` to `6` (42i), which completes its steps, and the coverage, which puts them
together, with the distinct statement (42j), which completes the induction, and Phase 39's
reduction, which carries it to every multigraph (42k): the headline's bare and distinct conjuncts
at every `d ≥ 3` (`Graph.graded_pencil_realization_theorem`). The generic conjunct (PD-HEAD)
remains: its nondegeneracy and lifts in every dimension are formalized (42l), and the generic
theorem and the headline (`-generic`) are open (42m).
`d = 4, 5, 6` are measured (Results 11, 19), not found below target under the `--d4`
population's cap (`n ≤ 12`, 36 simple graphs) and 8 graphs past it. Where the
conjecture has content, that is 47 cells on 18 graphs, six of them cycles (§2.5).

**What it implies.** By Result 12, every per-body flag stratum of `Pᵈ` attains, KT's panel
theorem among them. That is a strengthening, not a new proof: Phase 40 itself uses KT Theorem 5.6
at `d = 2` and KT Lemma 6.3.

**What exists.** KT's chain is formalized in every `d` (Phases 21–23, 33, 41). The pencil layer is
`P³` only. `IsNondegPencilRealization` takes a `BodyHingeFramework K 2` and points `Fin 4 → K`
(`Pencil/Motive.lean`), and `main-component.tex` computes in `Λ²K⁴`'s flat coordinates. The
planar carrier is the reusable part: pictures, `L(q)`, the one-witness lemma, the
fibre-intersection lemma and Jackson–Jordán's equality.

## 1. The PI's decisions

- **PI, 2026-10-29 (queue):** PENCIL-D queued ahead of ORIGAMI: prove the pencil realization
  theorem in every `Pᵈ` and formalize it over the next few phases.
- **PI, 2026-10-29 (open), where PD-RECON runs:** "In-phase, as 42a (Recommended)".
  The options put were: in-phase as 42a, attended, recon-first as Phase 39 was, with any single
  step that needs a new argument split off as an attack track then; an attack track under
  `/attack`, the phase opening on PD-STATE's Lean; or in-phase with PD-STATE and PD-STABLE queued
  beside it.
- **PI, 2026-10-29 (open), the plan's home:** "Sub-lettered, Phase42-design.md (Recommended)".
  The program section moved here from `notes/Strata.md`, which keeps its Results and evidence.
- **PI, 2026-10-29 (planning), the defaults for the next sessions:** "Let's record your
  suggestions and let those be the default for the next session." The suggestions, as put
  (with §2.5's recommendations):
  1. Measure the statement where the proof breaks, before any attack track: §2.5's content-range
     graphs, in T1 and T2's driver mode.
  2. Tiered targets, each a closable headline. Tier 0: every `d` at `def[3] ≤ 1` (PD-STABLE,
     formal only). Tier 1: a `P⁴` theorem, so every `d` at `def[3] ≤ 2` (SHORT, ONE-EAR's `d = 4`
     case, CERT). Tier 2: every `d`.
  3. The bare and distinct conjuncts first, GENERIC after, deferring nondegeneracy's lift with it.
  4. PD-STATE and PD-STABLE open beside the research once T1 and T2 land, the Lean under
     `/coordinate-phase`; the carrier in dual form (a point per body, each closed neighbourhood in
     a plane).
  5. A second read of rows 9 (contraction) and 12 ((⋆), the two-body ear) before anything builds
     on them.

  The order put: T1, T2 and the content-range graphs; then T3 and T4 at `d = 4, 5` on the content
  range, sizing SHORT and ONE-EAR; then attack tracks, with PD-STATE and PD-STABLE in parallel.

  *Note, 2026-10-30 (not the PI's text):* by the sharp Result 16 (`notes/Strata.md`), Tier 1's `P⁴`
  theorem reaches every `d` at `def[3] ≤ 7`, not `≤ 2`, and Tier 0 is `def[3] ≤ 3` (the PI's
  2026-10-30 entry below). The content range is `def[3] ≥ C(d,2) − 2`.
- **PI, 2026-10-29 (after T5), the research call of §4:** "ONE-CLASS first (Recommended)". The
  options put: ONE-CLASS's lemma first, on deficiencies alone and checkable exactly against T5's
  population, its size unknown; ONE-EAR's attack at `d = 5` (the motive, a `Pᵈ` insertion lemma,
  X2), the default recorded at open; or SHORT-CORE first, needed either way. On the session's
  work, where the options were this call, PD-STATE's open, or the second read of rows 9 and 12:
  "Let's do 1 but dispatch subagents for the second reads if that can be done safely in
  parallel."
- **PI, 2026-10-29 (after the second reads), the route:** "OK, let's go with this
  recommendation." The recommendation, as put: no separate route discussion before PD-STATE, since
  R1 as a step is out (rows 9 and 14) and every test measured R2's steps. Record R2's step
  structure with Result 15's embedding as the base row, and leave an outer induction on `d` to
  Tier 2, where it may enter only through CERT's open ears at `d ≥ 7`. PD-STABLE states the
  embedding at every `d′ ≤ d`, not only at `d′ = 3`, so that Tier 1 reaches every `d` by it.
- **PI, 2026-10-30 (42b's open), the carrier:** "(a) 3-space as data (Rec.)". The question put:
  "PD-STATE's carrier: your default was the dual form, "a point per body, each closed
  neighbourhood in a plane". Taken literally as a condition on the normals, it fails against Phase
  39's definitions in two ways. (W1) Where adjacent panels coincide, the hinges are no longer fixed
  by the normals. Two bodies with one panel and three hinges forming a triangle pass the
  normal-span test but are not a pencil (checked in Lean). (W2) If hinges are always the meet of
  the two panels, parallel edges share one hinge, so the double edge can't reach rank D, which
  Phase 39's bare conjunct reaches. Which reading should the chapter state?" The options put:
  (a) 3-space as data (Rec.): your dual form, with each body's plane Π_v ∋ b_v carried as data and
  every hinge at v containing Π_v^⊥; at d = 3 it is exactly Phase 39's definition; about 3
  commits; what the chapter already states. (b) Primal (b_v, A_v): the same mathematics and cost,
  the data named the other way round. (c) Meet form only: cheapest, but the Pᵈ headline loses the
  bare multigraph conjunct, against §0. (d) Normals-only: fails W1, not viable.
- **PI, 2026-10-30 (PD-STABLE's open):** "Open as 42c, §3 scope (Recommended)". The scope: §3's
  items 1–3 as written, with FRICTION's `normalsJoin` map lemma landing with item 1.
- **PI, 2026-10-30 (PD-STABLE, the sharp range):** "Widen to def_2 ≤ 3 (Recommended)". The
  question as put: "The open found that the deficiency lemma's own proof gives a sharper range. On
  a connected G, def at dimension d′ equals def at every d ≥ d′ once def_2(G) + 3 ≤ C(d′+1, 2),
  rather than at d′ ≥ def_2 + 2. The range is tight on cycles: C₇ has def_2 = 4, def_3 = 1 and
  def_4 = 0. With d′ = 3 (C(4,2) = 6), Phase 40 plus the embedding then proves the pencil in every
  dimension at def_2(G) ≤ 3, not just ≤ 1. I checked this by hand. Should Tier 0's theorem,
  thm:pencil-d-deficiency-two-le-one, widen?" The option read: "Same proof; only the hypothesis
  and the node's name and wording change. No extra commits. The Tier 0 sentence on ROADMAP and
  the status surfaces says ≤ 3." (Notation: `def_2` = `def[3]`, `def_3` = `def[6]`.) The
  range's second consequence (§3 item 1's Tier 1 reach, §2.5's content range) the PI relays to
  the SHORT-CORE attack track.
- **PI, 2026-10-30 (after 42a's close), the plan after Tier 0:** asked whether a generic conjunct
  could be stated at every `d`, and offered a recon on it, the PI answered: "Yes, let's scope out
  a recon. This could run alongside work on CERT, right? Basically, I'm leaning towards not
  formalizing the results on d=4 yet and seeing if we can get an informal proof at all d,
  including some form of a generic conjunct. However, perhaps if it would be useful to formalize
  some of the ingredients now (e.g. to help keep future research sessions on track) then I'd be
  willing to consider that as part of the plan."
- **PI, 2026-10-30 (42d's open):** "Yes, let's open 42d with these three strands. It was a bit of
  a hassle to open and close the worktree manually for short-core; I wonder if we could
  coordinate all three tracks from a single central session? Let's go with your recommendations
  for where to place the work and for sizing things. The aim for the rest of this session will be
  to get a solid harness in place for continuing the work in future sessions until it's done."
  The strands as put: CERT as an attack track; NONDEG, the recon on a `Pᵈ` nondegeneracy (its
  questions Q0–Q4 now its brief's); and writing out at general `d` the steps judged to carry
  over. The recommendations taken: the write-up as red nodes in `pencil-d.tex`; the coverage's
  deficiency counting in Lean sized before any is built.
- **PI, 2026-10-30 (42d's open, after the sizing and the two briefs):** four answers to four
  questions. The harness (`/coordinate-tracks`, `writeup-opus`, `worktree.baseRef: head`, the
  pointers, two incident lines): "Accept as is (Recommended)". The coverage counting's Lean, put
  as COUNT-A (sparse estimates at every `D`, one commit, low risk), COUNT-B (Theorem S at `D` and
  ONE-CLASS, one or two commits, low risk) and COUNT-C (the chain count behind S53, two or three
  commits, moderate risk): "A and B now (Recommended)", whose option read "Run them as a
  lean-kind track under /coordinate-tracks, one at a time in the main checkout; they write their
  own green nodes in pencil-d.tex. C waits for formalization." CERT's brief: "Clear it; session 1
  checks R1 (Recommended)". NONDEG's brief: "Clear with these defaults" (the defaults verbatim in
  its header).
- **PI, 2026-10-30 (42d, after NONDEG session 1), the `Pᵈ` nondegeneracy:** asked "Which
  nondegeneracy should the Pᵈ generic conjunct use?", the PI answered "(A) C2-same": N1 and N3
  on the points, and the hub planes around each body meet as in `P³`
  (`dim ⋂_{w∈S} Π_w ≤ 4 − |S|`), with Phase 39's feasibility word for word in every `d`
  (`notes/attacks/nondeg/` S9). The other options were C2-vac and dropping the conjunct.
- **PI, 2026-10-30 (42d, after NONDEG review 2), the generic conjunct's write-up:** NONDEG closes;
  slice W10 proves (W) by "(b) Shorter route" (S36's base-generic witness placed in `S_L(Y)`) and
  carries S38's pieces, O8 and the route's other results ("Add S7 (a), S9, S14").
- **PI, 2026-10-30 (42d's close):** asked "For the 42d close after the fix-up, is this the plan you
  want? It is an intermediate sub-phase close: the Phase 42 row stays in progress, 42d is marked
  done, and formalization (PD-CARRIER through PD-HEAD) is named as the next step but not opened,
  since it waits on your word. The close runs PHASE-BOUNDARIES' checklist, including the chapter's
  end-to-end re-read. Nothing gets pushed without asking you.", the PI answered "Sanctioned as
  described (Recommended)".
- **PI, 2026-10-30 (42e's open):** asked "Phase 42e isn't open yet: 42d closed with formalizing its
  proof waiting on your word, as the layers PD-CARRIER, PD-STEPS, PD-COVERAGE, PD-REDUCTION,
  PD-HEAD over 66 red nodes of pencil-d.tex. What should 42e open as?", the PI answered
  "PD-CARRIER only (Recommended)", whose option read: "Phase 40b–40d in Pᵈ: the setting and the
  flat rank, 4 red nodes (lem:pencil-d-condition-linear, thm:pencil-d-flat-rank,
  cor:pencil-d-flat-attains, cor:pencil-d-jj-flat), much of the carrier already green from 42b.
  Opus open commit, a pre-build recon of those nodes against the carrier, then about 3–6 build
  commits. The open also maps the other red nodes to layers, no letters minted."
- **PI, 2026-10-30 (42f's open):** asked "Phase 42f isn't open yet. 42e (PD-CARRIER) closed with
  the next layer, PD-STEPS, waiting on your go-ahead. PD-STEPS is 28 red nodes in pencil-d.tex:
  -cut (3), -contract (3), -splitoff (1), -short (12), -long (7), -ear-deficiency (2). For
  comparison, Phase 40 took about 64 commits over 7 sub-phases (40e–40k) to formalize the same
  steps in P³. What should 42f open as?", the PI answered "-cut + -contract (Recommended)", whose
  option read: "6 nodes, Phase 40e/40f/40k in Pᵈ (cut vertex, bridges, contraction at an additive
  core or a def₂ = 0 core). Opus open commit, a pre-build recon against the carrier, then about
  4–8 builds. The rest of PD-STEPS stays mapped by section, with no letters minted."
- **PI, 2026-10-30 (42f's open),** on the question design doc §3 left to PD-STEPS's open
  (whether thm:pencil-d-splitoff and thm:pencil-d-open-ear-deficiency, with
  lem:pencil-d-polygon-ear, are formalized), the PI first asked: "Do these results have any
  independent value? If not, we could probably also cut them from the blueprint at some point
  too." The coordinator answered: little — in P³ both are load-bearing (Phase 40's coverage uses
  thm:pencil-x0-splitoff and thm:pencil-x0-open-ear-two), but in Pᵈ the coverage routes around
  them (chains with one or two interior bodies by the d = 3 embedding or the chain-or-core count,
  three or more by the deficiency-free ear steps); they show two more d = 3 steps carry over, the
  ear step assumes attainment at G[V₁] alone, and neither is a credible fallback since the chain
  count is proved on paper. Then asked "thm:pencil-d-splitoff, thm:pencil-d-open-ear-deficiency
  and lem:pencil-d-polygon-ear have no consumer and little independent value; they are referenced
  only within pencil-d.tex, with no Lean. What should happen to them?", the PI answered "Cut in
  42f's open (Recommended)", whose option read: "42f's open commit deletes the three nodes and the
  -splitoff / -ear-deficiency sections (about 370 lines of TeX), and keeps one sentence in the
  coverage section saying the d = 3 split-off and two-body ear steps aren't needed for d ≥ 4.
  PD-STEPS goes from 28 nodes to 25. git keeps the text."
  *Note (not the PI's text):* this supersedes, going forward, the PI's 42d answer "(a) Keep
  standalone" (`notes/Phase42d.md`), which stays as recorded.
- **PI, 2026-10-30 (42g's open):** asked "Phase 42g isn't open yet. 42f closed with the rest of
  PD-STEPS waiting on your go-ahead: 19 red nodes in pencil-d.tex, in two independent sections.
  -short (12 nodes) covers open ears with 3+ interior bodies: SHORT-CORE's step, the ear data, and
  the d = 4–6 three-body case. -long (7 nodes) covers CERT's cycles and long open ears: five
  linear-algebra lemmas on closed polygons of joins, then the cycle and long-ear steps. Neither
  section uses a node of the other. What should 42g open as?", the PI answered "-long first
  (Recommended)", whose option read: "7 nodes, Phase 40's cycle and long-ear steps in Pᵈ on CERT's
  polygons. Opus open commit, a pre-build recon against the carrier, then about 4–7 builds. -short
  stays mapped by section, no letter minted." The other options were "-short first" (12 nodes) and
  "Both, -short + -long" (19 nodes).
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so the
  estimate of about 4–7 builds is the coordinator's. "Neither section uses a node of the other" was
  the coordinator's hypothesis, from the `\uses` lists of `sec:pencil-d-long` read truncated at
  line breaks; 42g's open checked it with every list parsed whole: no `-long` node uses a `-short`
  node or the reverse, and `-long`'s four pointers to `sec:pencil-d-short` are notation
  (`notes/Phase42g.md` *Consistency read at the open*).
- **PI, 2026-10-30 (42g, after the recon's acceptance and the Grade/Polygon.lean build).** The
  coordinator had answered the PI's question "Which proofs are more natural, the formalized ones or
  the ones currently written?" with: the Lean routes read better for the star
  (lem:pencil-d-polygon-star: by contradiction through linearity in the first point when the
  vertices span, else a 2×2-minor functional vanishing on the span of the vertices; Y_0 ≠ 0 from
  J_0 ≠ 0) and for the insertion's one bad value (lem:pencil-d-polygon-insert: the first n members
  of F(t) are independent with span A, so F(t) is independent iff J_i + t·w ∉ A, and J_i ∉ A makes
  that line meet A at most once); the chapter reads better for part (2) of
  lem:pencil-d-polygon-normal (the explicit affine map) and for the base triangle of
  lem:pencil-d-polygons (P_0,…,P_d a basis); the cycle's placement (two cases vs one path with N =
  min(m, D)) a toss-up. It offered to bring the star and insertion proofs in line with the Lean at
  the close.
  The PI answered, verbatim: "Yes, we should definitely align the star and insertion proofs with
  the Lean. For the other informal proofs that were difficult to formalize in Lean, are those
  tracked somewhere? I think we'll need a cleanup phase after Phase 42 to address them."
  The coordinator then answered that they are tracked only in notes/Phase42g.md *Blockers* item 2,
  which the close compresses, and proposed: a tracking note notes/Cleanup42.md for a
  post-Phase-42 cleanup, queued right after Phase 42 and ahead of ORIGAMI "unless you want it
  elsewhere"; a standing rule that any recon or build whose Lean departs from the chapter's proof
  adds a row in the same commit; and that the cleanup's opening recon compare every green node of
  pencil-d.tex (42b–42f were never checked for this) with its Lean, not only the logged rows. The
  PI has not replied on the placement: record "ahead of ORIGAMI" as the coordinator's proposal,
  not the PI's decision.
  *Note (not the PI's text):* 42g aligned the two chapter proofs the same day; the tracker is
  `notes/Cleanup42.md` (its proof-route ledger, §2), queued as `CLEANUP-42` between PENCIL-D and
  ORIGAMI as the coordinator's proposal, and the standing rule is in §3 below.
- **PI, 2026-10-31 (42h's open):** asked "Phase 42h isn't open yet. 42g closed with the rest of
  PD-STEPS waiting on your go-ahead: the 12 red nodes of pencil-d.tex's -short section (open ears
  with three or more interior bodies). They split cleanly in two: 8 nodes for ears with four or more
  interior bodies at every d (two-stars, insertion, kernel-curve, stars-four, the ear-data
  definition and lemma, ear-data-open, thm:pencil-d-open-ear-four), and 4 nodes for the three-body
  ear at d = 4–6 (stars-three, glued-ends, planes-meet, thm:pencil-d-open-ear-three). The three-body
  theorem uses the four-body one, and it's SHORT-CORE's hand proof, the coverage's only new
  mathematics. What should 42h open as?", the PI answered "k ≥ 4 half first (Recommended)", whose
  option read: "8 nodes, Phase 40's open-ear factoring in Pᵈ at four or more interior bodies. Opus
  open commit, a pre-build recon against the carrier, then roughly 4–8 builds. The three-body case
  (4 nodes) stays mapped by section for its own sub-phase, which lets its recon build on the landed
  k ≥ 4 Lean." The other options put were "All of -short (12 nodes)" (one sub-phase, roughly 7–12
  builds) and "Three-body path scoped by recon" (open on all 12, the recon sizing the three-body half
  before any build, with the option to split it off then).
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so the
  estimate of roughly 4–8 builds is the coordinator's. "They split cleanly in two" holds: 42h's open
  parsed every `\uses` list of the section whole, and none of the eight uses one of the four
  (`notes/Phase42h.md` *Consistency read at the open*). One phrase needs a correction. "SHORT-CORE's
  hand proof, the coverage's only new mathematics" describes SHORT-CORE's whole step (§2.3 SHORT,
  §3 *Handed on from PD-RECON*), not the three-body theorem alone, and each half carries part of it.
  The eight carry S35, the every-`ρ` step at `k ≥ 4` in every `d` (`lem:pencil-d-stars-four`), with
  S20's factoring transcribed at `D` (`thm:pencil-d-open-ear-four`) and the tools both halves use
  (S1 and S22's two stars, S6's tangent lemma, S19's insertion, S20 and S38's ear data); the `k = 4,
  5` part of the track's `d = 4` deliverable is theirs. The four carry `k = 3` at `d = 4, 5, 6`
  (S28–S33; at `d = 4` also the track's first proof, S1–S21), where the every-`ρ` form fails once
  `κ ≥ 7 − d` (S26), so the step uses `G[V₁]`'s own `ρ`; the coverage needs that step only at
  `d = 4` (S53, `thm:pencil-d-chain-or-core`).
- **PI, 2026-10-31 (42h, after the recon):** two questions on the chapter's wording of 42h's
  nodes. First asked "42h's recon proved lem:pencil-d-two-stars (the lines through two points y,
  y' in P^d) with its parts (2) and (3) on the *forms on ⋀²K^{d+1}*, where the chapter states them
  in ⋀^{d−1}K^{d+1}. The chapter's own perfect pairing ⋀² × ⋀^{d−1} → K identifies the two. Part
  (2) in the Lean reads: the forms killing both stars are exactly the forms pulled back from
  ⋀²(K^{d+1}/⟨y,y'⟩). The chapter instead says the annihilator is y ∧ y' ∧ ⋀^{d−3}. Part (3) is
  proved only at the degree p = d − 3, as "a nonzero form whose radical contains A has dim A + 2
  ≤ dim V"; the chapter states it for every p ≥ 0. Both proofs that cite the lemma (stars-four,
  and the not-yet-open stars-three) use only that degree. Nothing is false. How should the node
  and its Lean be made to agree?", the PI answered "Restate in forms (Recommended)", whose option
  read: "Edit the node's parts (2) and (3) to what the Lean proves (forms on ⋀², part (3) at the
  degree used), with one sentence keeping the ⋀^{d−1} reading through the section's pairing.
  Lands in the Stars.lean build commit; no extra Lean or commits. The citing proofs get matching
  wording." The other option put was "Build the ⋀^{d−1} bridge" (keep the chapter, add 300+ lines
  of Lean, one or two extra commits).
  Then asked "The recon's Lean takes a different route from the chapter in three more 42h proofs,
  each logged for the post-Phase-42 cleanup (notes/Cleanup42.md). R-8, stars-four: the Lean works
  on forms throughout, with no ⋀^{d−3}, no quotient and no independence of y₁, y₃, and is
  shorter; its chapter proof also cites two-stars (2)/(3) in the ⋀^{d−1} wording. R-9, the kernel
  curve: the Lean uses rank on a curve where the chapter uses Cramer's rule over K(t) and power
  series. R-10, part (3) of the ear-data lemma: a coefficient in the scaling variables instead of
  a multihomogeneous component, a toss-up. In 42g you had the star and insertion proofs follow
  their Lean. Which, if any, should the chapter align to the Lean now, in the build commits?", the
  PI answered "Stars-four only (Recommended)", whose option read: "Rewrite stars-four's chapter
  proof to the Lean's shorter forms route in the Stars.lean build, which keeps it consistent with
  a forms-worded two-stars. R-9 and R-10 stay in the ledger for the cleanup." The other options put
  were "Stars-four and kernel curve", "All three" and "None now".
  *Note (not the PI's text):* the questions and the option wording are the coordinator's. One
  phrase of the first needs a correction: in the `⋀^{d−1}` wording both citing proofs also used
  part (3)'s injectivity at `p = d − 2` (from `y₁ ∧ y₃ ∧ w ∧ ζ = 0` to `w̄ ∧ ζ̄ = 0`); the forms
  wording needs no such step. The `Grade/Stars.lean` build carried both answers out: two-stars'
  parts (2) and (3) and the section's annihilator are on the forms on `⋀²`, the `⋀^{d−1}` reading
  kept in one sentence of the proof and in the section's notation; stars-four's proof follows its
  Lean and cites part (2) only (`notes/Cleanup42.md` R-7 and R-8 aligned); stars-three's proof
  cites the restated parts through the pairing, its last step reading the radical in `K^{d+1}`,
  its argument otherwise unchanged.
- **PI, 2026-10-31 (42i's open):** asked "Phase 42i isn't open yet. 42h closed with the last of
  PD-STEPS waiting on your go-ahead: the 4 red nodes of pencil-d.tex's -short-three, the open ear
  with three interior bodies at d = 4 to 6 (stars-three, glued-ends, planes-meet,
  thm:pencil-d-open-ear-three). The theorem builds on 42h's landed four-body Lean: 42h's close
  checked that its factoring applies at three bodies, leaving only the insertion condition. The
  chapter states the theorem for 4 ≤ d ≤ 6, but the coverage uses it only at d = 4. What should 42i
  open as?", the PI answered "All 4 nodes as written (Recommended)", whose option read: "The
  theorem at 4 ≤ d ≤ 6, as the chapter states it. An Opus open commit, a pre-build recon that
  spikes the four against the carrier on 42h's Lean, then roughly 3–6 builds. Closes PD-STEPS."
  The other options put were "Recon first, scope after" ("Open on all 4, but the recon sizes the
  stars-three proof (the hardest node, about 430 chapter lines) and comes back to you before any
  build, with the option to narrow to d = 4 then.") and "d = 4 only" ("Restate
  thm:pencil-d-open-ear-three and stars-three at d = 4, the only dimension the coverage uses. This
  changes chapter statements now, and d = 5, 6 would stay paper-only.").
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so the
  estimate of roughly 3–6 builds is the coordinator's. "About 430 chapter lines" was the
  coordinator's rough count of stars-three's environment (`pencil-d.tex` lines 2683–3111 at
  `59ceecee`); 42i's open corrects it. The lemma and its proof are lines 2682–2779 at that commit,
  98 lines, with a 9-line remark after them (lines 2781–2789) showing that `d + κ ≤ 6` cannot be
  dropped. The range ran on to glued-ends' label, through `-short-four`'s ear-data nodes and
  four-body theorem (lines 2791–3106, green). The four environments are 98 (stars-three), 106
  (glued-ends), 73 (planes-meet) and 113 lines (the theorem). "Leaving only the insertion
  condition" holds as a type-check. Whether that condition, `hins` as landed (every base datum and
  every `ρ`), can be met at three bodies is the recon's first question (`notes/Phase42i.md`
  *Blockers*). The chapter proves the condition only at the base data its first stage picks, and
  when `r ≤ 2` only for `G[V₁]`'s own `ρ`.
- **PI, 2026-10-31 (42i, stars-three):** asked "Stars-three (lem:pencil-d-stars-three) is now
  green, and its Lean proves a stronger lemma than the chapter states. It works on forms on ⋀², as
  stars-four's does, and takes only dim Π_a = dim Π_b = 3, d + κ ≤ 6, p_a ∈ Π_a and p_b ∈ Π_b. It
  drops three of the node's hypotheses: κ ≤ 1, p_a and p_b linearly independent, and d ≥ 4. The
  chapter's proof needs κ ≤ 1 and the independence only for its four-independent-points step,
  which the Lean replaces by one coordinate of y₁ ∨ y₃. The chapter is not wrong. In 42h you had
  stars-four's proof follow its Lean. What should the chapter do with stars-three?", the PI
  answered "Restate to the Lean (Recommended)", whose option read: "Drop the three hypotheses from
  stars-three's statement and rewrite its proof to the forms route, as stars-four's. The theorem's
  first stage then also drops the polynomial that keeps q_a − q_b off zero. Lands in the theorem's
  build commit, which edits that proof anyway; no extra commit. Ledger row R-13 becomes aligned."
  The other options put were "Proof only" ("Rewrite stars-three's proof to the forms route but keep
  the statement's hypotheses, so the Lean stays stronger than the node. Lands in the theorem's
  build commit.") and "Leave for the cleanup" ("Chapter unchanged now; R-13 stays open in
  notes/Cleanup42.md for the cleanup after Phase 42.").
  *Note (not the PI's text):* the question and the option text are the coordinator's words. The
  glued-ends commit recorded the answer and changed no chapter text; the restatement of
  stars-three's statement and proof, and the theorem's first stage without the first coordinate of
  `q_a − q_b`, land in the theorem's build commit (`notes/Phase42i.md` *Hand-off*), which turns
  `notes/Cleanup42.md` R-13 aligned.
- **PI, 2026-10-31 (42j's open):** asked "Phase 42j isn't open yet. 42i closed PD-STEPS, and the
  next layer is PD-COVERAGE: the 4 red nodes of pencil-d.tex. Two count chains
  (lem:pencil-d-chain-count, a new edge count, and thm:pencil-d-chain-or-core). The other two are
  the coverage in every dimension (thm:pencil-d-coverage, which puts all of PD-STEPS together) and
  the distinct statement (lem:pencil-d-distinct-statement, a short corollary). The design doc says
  the coverage's Lean needs forms of Phase 40's cut, cycle and planar-rigid reductions that return
  their bridge, cut-vertex or cycle data. What should 42j open as?", the PI answered "All 4 nodes
  as written (Recommended)", whose option read: "Close PD-COVERAGE. An Opus open commit, then a
  pre-build recon that spikes the coverage assembly against the landed steps and pins the
  data-returning reductions, then roughly 4–7 builds (my estimate). PD-REDUCTION would come next,
  at your word." The other options put were "Recon first, scope after" ("Open on all 4, but the
  recon sizes the coverage assembly and the reduction forms, then comes back to you before any
  build.") and "The counting nodes only" ("Open on chain-count and chain-or-core only (pure
  combinatorics, about 2–3 builds). The coverage and the distinct statement would wait for a later
  sub-phase.").
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so
  "roughly 4–7 builds" and "about 2–3 builds" are the coordinator's estimates, and "a short
  corollary" is the coordinator's reading. "Two count chains" means that two of the four nodes
  count chains. 42j's open checked the question against the chapter. Only chain-count counts:
  chain-or-core applies its bound, with COUNT-B's two core lemmas (`lem:pencil-d-chain-core`,
  `lem:pencil-d-core-positive-deficiency`), to find a long chain, a core, or deficiency zero in
  dimension three. "A new edge count" holds for its Lean (COUNT-C, not yet formalized): at `d = 3`
  only its `ℓ = 1` case exists, inside the proof of part (2) of `lem:pencil-x0-sparse-count`, under
  another hypothesis. "Puts all of PD-STEPS together" holds: the coverage's proof uses all eight of
  PD-STEPS's steps (the cut vertex, the chain of bridges, both contractions, the cycle and the
  three ear steps), and beside them PD-CARRIER's flat corollary and, through the embedding, Phase
  40's coverage. "A short corollary" holds: its proof cites two nodes, and its `d = 3` Lean,
  `x0Dist`, is one line. The design doc's phrase (§3, *Handed on from PD-RECON*) names the three
  lemmas, but the planar-rigid reduction's data is a maximal planar-rigid set, not a bridge, cut
  vertex or cycle; the coverage's proof re-derives that set's properties inline.
- **PI, 2026-11-04 (42k's open):** asked "Phase 42k isn't open yet. 42j closed PD-COVERAGE, and the
  next layer is PD-REDUCTION: the 8 red nodes of pencil-d.tex's sec:pencil-d-reduction, Phase 39's
  reduction in every dimension. Three are linear algebra (a hinge in two pencils, moving a
  realization by a linear map, moving one side of a cut edge). Four are the cases at a loop, on at
  most two bodies, at a cut edge and at parallel edges. The last is the theorem: every multigraph
  has a pencil realization at the deficiency rank in dimension d, and an adjacent-distinct one when
  simple. The induction itself, Graph.pencil_reduction, already takes the dimension as a
  parameter, and the d = 3 cases are about 1,160 Lean lines (Arms.lean, ArmsAssembly.lean). What
  should 42k open as?", the PI answered "All 8 nodes as written (Recommended)", whose option read:
  "Close PD-REDUCTION. An Opus open commit, then a pre-build recon that spikes the cases against
  Phase 39's d = 3 Lean and the landed carrier, then roughly 4–8 builds (my estimate). PD-HEAD (21
  nodes) would come next, at your word." The other options put were "Recon first, scope after"
  ("Open on all 8, but the recon sizes the cases and the linear algebra, then comes back to you
  before any build.") and "Linear algebra only" ("Open on the three linear-algebra nodes only
  (about 2–3 builds, my estimate). The four cases and the theorem would wait for a later
  sub-phase.").
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so
  "roughly 4–8 builds" and "about 2–3 builds" are the coordinator's estimates. 42k's open checked
  the rest against the source and the chapter. "Three are linear algebra" and the four cases hold
  (`lem:pencil-d-two-pencil-extension`, `-projective-transport`, `-cut-reposition`;
  `lem:pencil-d-loop-case`, `-base-case`, `-cut-case`, `-nonsimple-case`). The theorem as put
  leaves out three of the chapter's qualifiers (`thm:pencil-d-realization-theorem`): an infinite
  field, `d ≥ 3`, and every multigraph *with at least one body*. Of the eight, only the theorem
  assumes the infinite field, for the distinct statement it cites (through the coverage). "Already
  takes the dimension as a parameter" holds as the coordinator read the signature:
  `Graph.pencil_reduction` (`Molecular/Induction/ForestSurgery/Reduction.lean:803`) takes an
  arbitrary property and `n` with `hD : 6 ≤ bodyBarDim n`, where `bodyBarDim n = n(n + 1)/2`, so
  `n ≥ 3`; `n` enters only through the proper rigid subgraph of its contraction and split cases.
  The theorem's proof reads neither that subgraph nor the split case's body of degree two, so the
  reduction serves at `n = d` and at Phase 39's `n = 3` alike. "About 1,160 Lean lines" is the
  coordinator's `wc -l` of the two whole files (`Pencil/Arms.lean` 930 + `ArmsAssembly.lean` 233),
  and it does not hold as a measure of the `d = 3` cases. `Arms.lean`'s lines 352–604
  (`exists_reposition_cross_incidences_avoiding` and three dimension lemmas, 253 lines) serve only
  the conditioned pair's generic cut case (`Pair.lean`). Outside the two files are the `d = 3`
  nonsimple case (`hasPencilRealization_of_not_simple`, `Pencil/X0.lean` lines 68–335, 268 lines),
  the `d = 3` two-pencil lemma and its converse (`exists_extensor_two_pencils{,_iff}`,
  `Pencil/Statement.lean` lines 637–770, 134 lines) and the assembly (`Pencil/Pair2.lean`,
  `pencilPair_of_X0` in `X0.lean`). So the cases' `d = 3` Lean is about 1,310 lines, headers
  included, assembly aside. The adjacent-distinct base case has no direct `d = 3` Lean: there it
  comes from the generic conjunct (`pencilPair_of_ncard_le_two`, `Pair.lean`).
- **PI, 2026-11-04 (42l's open):** asked "Phase 42l isn't open yet. 42k closed PD-REDUCTION, and the
  last layer is PD-HEAD: 21 red nodes of pencil-d.tex. That's sec:pencil-d-nondegenerate (4: the
  definition, agreement at d = 3, invariance under linear maps, feasibility independent of d),
  sec:pencil-d-lift (6: a d = 3 parametrization, lifts of a P³ realization, lifts are
  nondegenerate, the general lift attains, one lift suffices, lifts restrict to a subgraph) and
  sec:pencil-d-generic (11: the reduction's cases for the generic conjunct, the generic theorem,
  and the headline cor:pencil-d-conditioned-pair). The d = 3 template is Phase 39's
  generic-conjunct Lean (Pair.lean 967, Pair2.lean 622, Steer.lean 592 lines). Closing PD-HEAD
  closes Phase 42, which is also where the main_results row is decided. What should 42l open
  as?", the PI answered "Nondegenerate + lift only", whose option read: "Open on the 10 nodes of
  -nondegenerate and -lift (roughly 3–5 builds, my estimate). The 11 generic nodes and the headline
  would wait for a later sub-phase." The other options put were "All 21 nodes as written
  (Recommended)" ("Close PD-HEAD and with it Phase 42. An Opus open commit, a pre-build recon that
  spikes the nodes against Phase 39's d = 3 generic Lean and the landed carrier, then roughly 6–10
  builds (my estimate), and the Phase 42 close.") and "Recon first, scope after" ("Open on all 21,
  but the recon sizes the lift and generic sections and comes back to you before any build.").
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so
  "roughly 3–5 builds" and "roughly 6–10 builds" are the coordinator's estimates, and the line
  counts are the coordinator's `wc -l` of the three whole files (they match at 42l's open). 42l's
  open checked the rest against the chapter and the source. The counts hold: 4, 6 and 11, the 21
  red nodes of the 62 from `sec:pencil-d-induction` on. The descriptions of `-nondegenerate` and
  `-lift` hold, with qualifiers they leave out. "Invariance under linear maps" is
  `lem:pencil-d-nondegenerate-maps`: the conditions are kept by an injective map and pulled back
  along one injective on each subspace, not kept by every linear map. The feasibility, one-lift
  and restriction lemmas assume an infinite field, and the restriction lemma assumes (T1) and (T2),
  which its consumers in `-generic` discharge. "Lifts are nondegenerate" is part (1) of
  `lem:pencil-d-lift-realization`; its parts (2) and (3) say that the lifts' normals and ranks
  depend only on the points and the maps `ζ`, and that rescaling and collineations keep the rank.
  "The reduction's cases" holds loosely: `thm:pencil-d-generic` is a strong induction of its own
  on the number of bodies, on the case split of the `d = 3` conditioned pair and generic step
  (`thm:pencil-conditioned-pair-nonempty`, `thm:pencil-generic-step`), not `Graph.pencil_reduction`.
  Of the section's nine lemmas six are its cases, and three (`lem:pencil-d-good-ear`, `-ear-extend`,
  `-ear-free`) find a pendant triangle or the ear and supply the ear case's condition. "Phase 39's generic-conjunct Lean" holds of the three files' origin, but they
  are not the `d = 3` Lean the ten transcribe. `Pencil/Pair.lean` (the conditioned pair at a loop,
  on at most two bodies and at a cut edge) and `Pair2.lean` (the pendant case and the assembly
  through the reduction) are the `d = 3` counterparts of `-generic`'s lift-small, lift-cut-edge and
  lift-pendant and of its assembly; no `d = 3` remark of the ten cites their nodes. `Steer.lean` is
  one of six files of the Lean of `lem:pencil-generic-steer`, the parametrization
  `lem:pencil-d-steer` transcribes through the polarity: `Chart.lean` 719, `Engine.lean` 646,
  `Reseed.lean` 400, `Steer.lean` 592, `Witness.lean` 199 and `MainComponent/GenericSteer.lean`
  825 lines. Its rank as a lower bound (`Steer.lean`, `Engine.lean`) and its part (b)
  (`GenericSteer.lean`) are the `d = 3` steps that one-witness (2) and the restriction lemma cite.
  The `d = 3` definitions are in `Pencil/Motive.lean` (`IsNondegPencilRealization`,
  `PencilNondegFeasible`, `HasGenericPencilRealization`, lines 132, 148, 157). The lift's four
  nodes, `maps` (1) and the feasibility lemma's projection have no `d = 3` Lean: at `d = 3` the
  only lift is the realization. "Where the main_results row is decided" holds (§3, PD-REDUCTION's
  entry). No node of the ten uses or `\cref`s a node of `-generic`, so the split is consistent;
  one sentence of `-lift`'s prose, after `def:pencil-d-lift`, points ahead to
  `lem:pencil-d-lift-no-rigid`, which proves it, and no proof of the ten uses it.
- **PI, 2026-11-04 (42l's close), the parametrization's auxiliary vectors:** on
  `notes/Cleanup42.md` R-22 (`lem:pencil-d-steer` stated five auxiliary vectors at every body, its
  Lean, `PencilSeed.ofGamma`, has six), the PI answered, verbatim: "Yes, let's make it say six at
  the close. I guess we should make the wording clear that there's some flexibility in the proof
  here and we decided to go with six in the formalization even though five actually suffice."
  *Note (not the PI's text):* the rest of the exchange was the coordinator's and is not recorded
  here. 42l's close restated the node to six vectors read at the places a fixed assignment leaves
  empty, three for each product, with a formalization note after the proof that five suffice (a
  body that is not a hub fills its own place) and that the formalization takes six; R-22 is
  aligned.
- **PI, 2026-11-05 (42m's open):** asked "Phase 42m isn't open yet. It would be PD-HEAD's second
  half, -generic: 11 red nodes of pencil-d.tex. Nine are lemmas: the generic conjunct's cases (few
  bodies, a cut edge, a pendant body, a pendant triangle, no planar-rigid set, the degree-2 ear) and
  three helpers that find the ear and supply its condition. The other two are thm:pencil-d-generic
  and the headline cor:pencil-d-conditioned-pair. 10 of the 11 use 42l's Lean. The d = 3 templates
  are Pair.lean (967 lines) and Pair2.lean (622). Closing 42m closes Phase 42, and that close is
  where Tier 0's main_results row gets decided. What should 42m open as?", the PI answered "All 11
  as written (Recommended)", whose option read: "An Opus open commit, then a pre-build recon that
  spikes all 11 against Phase 39's d = 3 Lean and 42l's Lean. Then roughly 4–7 builds (my estimate)
  and the close of 42m and Phase 42 together." The other options put were "Recon first, scope
  after" ("Open on all 11, but the recon sizes the section and comes back to you before any
  build.") and "Cases now, headline later" ("Open on the 9 lemmas only. thm:pencil-d-generic and
  the headline (Phase 42's close) wait for a further sub-phase.").
  *Note (not the PI's text):* the question and the option text are the coordinator's words, so
  "roughly 4–7 builds" is the coordinator's estimate, and the line counts are the coordinator's
  recollection of the figures in the 42l entry above, not re-counted in that session. 42m's open
  checked the rest against the chapter and the source. The counts hold: the eleven are the red
  nodes of `sec:pencil-d-generic`, the only red nodes of the 62 from `sec:pencil-d-induction` on
  and of the whole blueprint; nine are lemmas, six of them cases and three helpers, and the other
  two are the theorem and the headline. The cases' short names hold, with qualifiers they leave
  out: "few bodies" is `lem:pencil-d-lift-small`, which also takes a triangle and a disconnected
  multigraph; "a cut edge" (`-lift-cut-edge`) has two sides of at least two bodies; "a pendant
  body" (`-lift-pendant`) is a body of degree one whose neighbour has another; "no planar-rigid
  set" (`-lift-no-rigid`) also asks that the general configuration attain, which the coverage
  gives; "the degree-2 ear" (`-lift-ear`) is a body of degree two with non-adjacent hub neighbours,
  under `def_d(G − x) ≤ def_d(G)` and a hypothesis on the lifts of `G − x`. The cases are those of
  `thm:pencil-d-generic`'s own induction. "Three helpers that find the ear and supply its condition"
  compresses the 42l entry above: `lem:pencil-d-good-ear` finds the ear or a pendant triangle, so it
  serves the pendant-triangle case too; `-ear-free` supplies the ear's condition, and `-ear-extend`
  serves `-ear-free` alone. "10 of the 11 use 42l's Lean" holds, as 42l's open found: every node
  but `-good-ear` `\uses` a node of 42l, nine of 42l's ten between them (not
  `lem:pencil-d-nondegenerate-maps`); `-ear-extend` uses only the steer lemma, and the headline the
  definition and `-three`, with `thm:pencil-d-generic` in its proof. The line counts hold (`wc -l`
  at 42m's open: `Pencil/Pair.lean` 967, `Pair2.lean` 622), but the two files are the `d = 3` Lean
  of three of the six cases and of part of the assembly, not of all eleven: `Pair.lean` has the
  two-body and no-crossing-edge parts of `-lift-small` and `-lift-cut-edge`, and `Pair2.lean`
  `-lift-pendant` and the assembly's cut-edge step (`pencilPair_of_not_twoEdgeConnected`). The rest
  of `-generic`'s `d = 3` Lean is in `Pencil/MainComponent/`: `GenericTriangle.lean` 1009 (the
  triangle and the pendant triangle), `GenericBase.lean` 948 (no planar-rigid set), `GoodEar.lean`
  441, `GenericEar.lean` 593 (the one-body ear) and `Statements.lean` 183 (the generic step's case
  split and the conditioned pair). `-ear-extend` and `-ear-free` have no `d = 3` Lean, as at
  `d = 3` no lift is needed. "Where Tier 0's main_results row gets decided" holds (§3, *At Phase
  42's close*).

## 2. PD-RECON (42a)

**Routes**, as queued:
- **(R1) Induction on `d`.** The step `d−1 → d` starts from Result 13's base, the `P^{d−1}` pencil
  in a hyperplane, and adds one height in `L(q)`. Phase 40 is the step `2 → 3` from the flat base.
- **(R2) Direct.** Phase 40's induction, run once with `d − 2` heights.

Either way, Result 15 (by the sharp Result 16) limits the work for each graph to `3 ≤ d ≤ d*`, `d*` the least `d′` with `D_{d′} ≥ def_3(G) + 3`.

### 2.1 The step table (2026-10-29)

Four read-only recon passes (Claude Opus 5.5), one per slice of `main-component.tex` (A: lines
158–1370; B: 1371–3215; C: 3216–4864; D: 4865–5623 with `pencil.tex`), on one brief: for each
step, its uses of `d = 3` beyond `D = 6` and the flat base, and a verdict per route. Line numbers
are at `2168de79`. Notation: `def[D]` is `def:D-deficiency` at screw dimension `D` (the chapter's
`def₂ = def[3]`, `def₃ = def[6]`), `D_d = C(d+1, 2)`, `Π_v = span b_{N[v]}` (dimension 3).
**GEN** generalizes; **GEN|X** given obligation X (§2.3); **FAILS** fails as written in `Pᵈ`.

| # | Step (`main-component.tex` unless marked) | Its `d = 3` beyond `D` and the base | Verdict |
|---|---|---|---|
| 1 | Pictures, `L(q)`, main pictures (212–760) | none: planar data; the fibre is `L(q)^{d−2}`, same main pictures | GEN |
| 2 | `def:pencil-configuration`, `lem:pencil-condition-linear` (307, 468) | plane normal as a `4×4` determinant; "solving for `z_w`" (495–499) | GEN: `S → K³` is an isomorphism, so `S` is the graph of a map `K³ → K^{d−2}`; the configurations are `L(q)^{d−2}` (Result 13) |
| 3 | Rank carrier: `lem:pencil-config-point-join-rank`, `-rank-collineation`, `-rank-scale-shift` (387–563) | the polarity as a self-map of `Λ²K⁴`; Lean at `Fin 4`, `k := 2`; scalar `t` | GEN\|CARRIER (formal); scale-shift becomes `GL_{d−2}` and `Aff(q)^{d−2}` |
| 4 | `lem:pencil-x0-one-witness`, `-fibre-intersection` (670, 823) | none; the hinge is affine in each height, with a `Λ²Z` part quadratic in the heights at `d ≥ 4` | GEN: `L(q)^{d−2}` is linear, one polynomial section serves every height, the fibre lemma's Lean takes any submodule |
| 5 | Flat rank (886–1167) | the split `Λ²K⁴ = K³ × K³` | GEN: R2's flat rank `D_d(n−1) + 3 − dim L(q)`; R1's base `D_d(n−1) − def[D_{d−1}]` where `P^{d−1}` attains (both by hand; measured, T1, `Strata.md` Result 20) |
| 6 | Jackson–Jordán's equality (1169–1369) | none: planar, KT Theorem 5.6 at `d = 2` | GEN unchanged |
| 7 | Cut vertex, the shared scheme (1384–1564) | count only (`lem:deficiency-cut-vertex`, every `D`) | GEN: the height is used only as a vector |
| 8 | Chain of bridges (1566–1645) | count only | GEN |
| 9 | Contraction at an additive core, its corollary (1647–2139) | the collineation (row 3), one-witness (row 4), flat attainment (row 5) and `def:pencil-x0-attains`; the KT-layer pins are `k`- or `n`-general | GEN\|CARRIER: "rigid" is `def[D_d](H) = 0`; additivity stays planar, `def[3]`; second read below |
| 10 | Cycle `thm:pencil-x0-cycle` (2387) | the `K⁴` certificate `Y₀…Y₅` (2342) | GEN\|CERT: needs `λ ≥ min(m, D_d)` |
| 11 | Long ear `thm:pencil-x0-open-ear` (2439) | "five interior bodies give six hinges" (2191); the hexagon placement | GEN\|CERT, for `k ≥ D_d − 1` only (9 at `d = 4`) |
| 12 | (⋆) and the two-body ear `thm:pencil-x0-open-ear-two` (2534, 2896) | mathematically none: (⋆)'s `k + 1` holds at every `D` (`lem:block-rank-ear`); every Lean pin is `P³` (`Fin 4`, one height, the hexagon) | GEN\|CARRIER at `k = 2` (a flat certificate in every `d`); `3 ≤ k ≤ D_d − 2` given CERT's open ears; second read below |
| 13 | Short ears `k = 3, 4` (2960, 3081) and their line geometry (2601–2804) | the Klein pairing into `Λ⁴K⁴ = K`; four points' six joins span `Λ²K⁴`; two stars of codimension 1 | **FAILS** for `d ≥ 4`; the step itself unclear; its range grows to `3 ≤ k ≤ D_d − 2` (SHORT) |
| 14 | One-body ear (3341–3491) | one affine function `D(z)` and its zero line (3346–3348) | **FAILS** for `d ≥ 5`, and at `d = 4` when `a, b` share a neighbour in `V₁` (ONE-EAR) |
| 15 | Two-body ear at non-adjacent ends (3498–3627) | two hyperplanes of `K⁴` meet in a line; a tetrahedron | inherits 14; insertion plausible at `d = 4`, unclear at `d ≥ 5` (ONE-EAR) |
| 16 | Split-off (3629–3957) | `δ ≥ 5`, a count; collinearity only | GEN: `δ_D ≥ D − 1` |
| 17 | Sparse estimates (3959–4313) | `v₃ = 2v₂ − d_G` uses `6 = 2·3`; Lean pins fix `n = 3` | GEN, restated at `D`: the consumers need only "`v₂ ≤ 0` gives `v_D ≤ 0`", one line at every `D ≥ 3` |
| 18 | Coverage, Theorem S (4314–4864) | `s₆ → s_D`, every `D ≥ 6` | GEN\|rows 11–15: "no chain with three or more interior bodies" needs every `k ≥ 3`; the `k = 1, 2` orbit cells are load-bearing |
| 19 | `pencil.tex`'s reduction, bare and distinct conjuncts | counts in `K⁴` only (P440); the self-duality is unused (P115–215) | GEN\|CARRIER; two-pencil extension gains a third clause `dim(Π_u ∩ Π_v) ≥ 2`, met at every consumer |
| 20 | Phase 39's definitions (`pencil.tex` P64, P89) | a per-body *point*: the pencil only at `d = 3`, at `d ≥ 4` Result 12's type `(0, B)` | restate (CARRIER) |
| 21 | Nondegeneracy (P818, M4933) | two "at most three" bounds from 3-spaces of `K⁴`; not self-dual | unclear: no canonical `Pᵈ` lift (the PI) |
| 22 | Route B, the generic conjunct (M5216, M5333) | `K⁴` triple cross product (M5248); `p_x` on `n_a^⊥ ∩ n_b^⊥` (M5371) | **FAILS**: steer for `d ≥ 4`, one-ear for `d ≥ 5` (GENERIC); separable, as bare and distinct never consume it |

Checked by the coordinator against the text or by hand: the passages of rows 13, 14 and 22; the
codimension `C(d−1, 2)` of two stars in `Λ²K^{d+1}` (1 only at `d = 3`); two general 3-spaces of
`K^{d+1}` meet in dimension `5 − d`; row 5's flat rank at `d = 3`; and that `def[3] = def[D′]` for
one `D′ > 3` forces a tree-quotient optimum, so `def[3] = def[D]` at every `D ≥ 3` (row 5: the flat
class does not change with `d`). `lem:deficiency-antitone` (every `d ≤ d′`, connected `G`) is
formalized. The rest is the agents' reading, cited by row.

**Second read of rows 9 and 12** (2026-10-29, the PI's default 5; two read-only recons, Claude
Opus 5.5, briefed to refute). Neither found a gap.
- *Row 9* holds under R2 at every `d ≥ 4`, alike at `d = 4` and `d ≥ 5`. The step consumes `H`
  and `G/H` attaining, each at its own general configuration, and no special locus. Every closed
  condition in it (the lifting systems `M(t)`, `M(0)`, `L(q)`) is planar and acts on each height
  separately; only the two rank conditions couple the heights, and both are open. Row 14 differs:
  its incidence `b_x ∈ Π_a ∩ Π_b` is closed and couples the heights. `def[D]` enters only through
  `H`'s standing hypotheses, `rigidContract_deficiency_eq` and `H`'s target, all `n`-general in
  Lean, and the count closes. The limit at `t = 0` is not a pencil configuration of `G/H` at `r`,
  but the step never needs one. Checked by the reader exactly over `GF(2⁶¹ − 1)` on 6 graphs at
  `d = 4, 5`, cores `D`-rigid but not 6-rigid included, with a non-additive control (measured,
  script not retained).
- *Row 12* holds at every `d ≥ 2` for `k = 2`. With `k ≥ 2`, the ear only fixes `x₁`'s and `x_k`'s
  heights given their picture points, so `G`'s configurations restrict onto `G[V₁]`'s. At height
  zero the points lie in a 3-space whose `Λ²` embeds, so the `k = 2` certificate needs no hexagon.
  For `3 ≤ k ≤ D − 2` the step is the long ear's height-finding with CERT's open ears, proved only
  at `d ≤ 6` (§2.3 CERT). Also, by hand, checked here: `m` parts inside an ear force `m + 1`
  crossings, so `def[D](G) ≤ def[D](G[V₁]) + max(0, k + 1 − D)`. For `k ≤ D − 1` the step's
  hypothesis is therefore an equality, and for `2 ≤ k ≤ D − 2` it is the coverage's merged test.

### 2.2 Verdict on the routes

**Neither route closes as written; the step structure is R2's.** Every step reads Phase 40's
induction on `|V|` at a fixed `d` with all `d − 2` heights general. R1 as "fix `z¹…z^{d−3}` from a
`P^{d−1}` witness and add one height" breaks contraction, whose heights must move along its curve
(B; the curve moves the picture, so this holds at `d = 3` too, and R2 runs it per height, §2.1's
second read), and does not help the one-body ear: every configuration of `G` restricted to `V₁`
lies on the incidence locus, whatever the base (C). What R1 contributes is a **base row**: where `P^{d−1}`
attains at `G`, its base has rank `D_d(n−1) − def[D_{d−1}](G)` (row 5), so `G` attains in `Pᵈ`
whenever `def[D_{d−1}](G) = def[D_d](G)`. That is Result 15 at `d′ = d − 1`; the class grows with
`d` and contains R2's flat class `def[3] = def[D_d]`. The recon's proposal, for the PI: R2's
induction with R1's base row, inside an outer induction on `d`. The PI took R2's induction with
R1's base row, the outer induction left to Tier 2 (§1).

**The pattern behind the failures.** In `P³` the planes of two bodies always share a line; in `Pᵈ`
two 3-spaces of `K^{d+1}` meet in dimension `5 − d`. A step that deletes a body `x` and keeps its
two neighbours' planes relaxes a closed condition at `d ≥ 5` (`b_x ∈ Π_a ∩ Π_b`), so "the smaller
graph attains generally" no longer reaches `G` (rows 14, 15, 22). The short ears fail for a related
reason: the joins through two points have codimension `C(d−1, 2)`, not 1 (row 13).

**Where `d = 4` stands.** Row 14 fails only when the ends share a neighbour in `V₁`, row 15's
insertion is plausible (`Λ²K⁵` is the whole screw space), row 22's one-ear works given steer; row
13 is blocked as written. By Results 15–16 a `P⁴` theorem gives every `d` at `def[3](G) ≤ 2`,
Result 17's `def[3] ≤ 1` one step further.

### 2.3 Obligations (stable codes)

- **CERT** (rows 10–12): at each `d`, a closed `m`-gon of affine points with independent
  consecutive joins for `m ≤ D_d`, the long ear at `k = D_d − 1` with its ends at height zero,
  and row 12's open ears: `k + 1` independent joins, heights zero at `a, x₁, x_k, b`. **Holds at
  `d ≤ 6`, over every field** (T2, `Strata.md` Result 21). The `D`-gon is a construction in every
  `d`: B's Euler circuit at even `d`, a matching and detours at odd `d`, checked at `d = 3, 5`. Left
  for PD-STEPS: a uniform construction for `m < D` and the open ears (or, at the cycle, KT, since a
  cycle's pencil condition is empty). Row 12's second read (§2.1) sizes the open ears at `d ≥ 7`.
  A certificate at `d′` stays one at every `d ≥ d′` (embed the heights; `Λ²` of an injective map
  is injective), so only `D_{d−1} ≤ k + 1 ≤ D_d − 1` is new at `d`. **42d: proved by hand at
  every `d ≥ 3`, over every field with `|K| ≥ 4`** (CERT's R1, `notes/attacks/cert/` workbook
  S1–S8; review 1 concurs; closed 2026-10-30), which settles what this bullet left for PD-STEPS.
  Trails in the complete graph
  on an affine basis with first and last edges at height zero give every `k + 1 ∈ [4, D − 1]` at
  `d = 3, 4, 6`. At odd `d` parity caps them at `D − (d−1)/2` edges, so the top values need
  detours, as the `D`-gon's do (the reader's search, measured, script not retained).
- **SHORT** (row 13): ears with `3 ≤ k ≤ D_d − 2` and `def[D](G[V₁]) > def[D](G)`. Re-inserting
  `x₂` adds only joins in `star(y₁) + star(y₃)`, so the step needs X3: at general ear data, `W`
  containing both stars is `Λ²K^{d+1}`. It is needed only where `def[D](G'') = def[D](G)` and
  `2d − 1 ≤ dim W ≤ D − 1` (the danger cells); elsewhere the `d`-general insertion lemma settles
  the step. **X3 holds for `k ≥ C(d−1, 2) + 3`** (6 at `d = 4`, 9 at `d = 5`) at every graph.
  The stars have codimension `C(d−1, 2)`, and the joins `y₄ y₅, …, y_k p_b` of `G''`'s ear lie in
  `W`; they span the quotient at one ear datum, hence at a general one. There `y₄, …, y_{k−1}` are
  free and `y_k` any point of `Π_b`, so a linear map onto `K^{d+1}/⟨y₁, y₃⟩` places CERT's closed
  `C(d−1, 2)`-gon of `P^{d−2}` (Result 21: the triangle at `d = 4`, the hexagon at `d = 5`) with
  its last two points over `y_k` and `p_b`. At `d = 3` this is the chapter's tetrahedron. **Left,
  SHORT-CORE:** `3 ≤ k ≤ C(d−1, 2) + 2` (3–5 at `d = 4`, 3–8 at `d = 5`), where `ρ`'s image in
  that quotient must supply the rest; the chapter's `k = 3` case split on `ρ` is the `d = 3` model.
  T3 (§2.4) found no obstruction on 198 danger cells. **SHORT-CORE: closed 2026-10-30, by its
  attack track** (`notes/attacks/short-core/`; status `state.md`, results by workbook S-number).
  `d = 4`, `k = 3, 4, 5` is proved by hand (S1–S21, S35; three readers), with base data chosen
  general (S21); `k ≥ 4` in every `d` for every `ρ` (S35), so the `P³` step's every-`ρ` insertion
  hypothesis transcribes there; `k = 3` at `d = 5, 6` (S28–S33). At `k = 3` the every-`ρ` form
  fails once `κ ≥ 7 − d` (S26), so the step must use `G[V₁]`'s own `ρ`. From `d = 5` on no graph
  past rows 1–5 needs the `k = 3` short row (S52–S53, given CERT's open ears), so `k = 3` at
  `d ≥ 7` (G1) was parked, to revive only if CERT's open ears fail there (S56); they do not
  (CERT S6, S9), and G1 is retired on the PI's word (2026-10-30).
- **ONE-EAR** (rows 14–15): either a motive that asks `G[V₁]` to attain on the locus where `Π_a`
  and `Π_b` meet above a general `q_x`, or another step for `k = 1, 2` at non-adjacent ends, plus
  a `Pᵈ` insertion lemma (at `d ≥ 5` every reachable hinge lies in `Λ²(A+B)`, of dimension ≤ 10).
  **T4 sized it** (§2.4; `Strata.md` Results 23, 25): the first option stands wherever the `d = 3`
  steps' merged hypothesis **M**, `def[3](G[V₁]; a, b) + 2 ≤ def[3](G[V₁])`, holds, at every cell
  measured, `d = 3..6`, and fails only where M fails, as at `d = 3`. T5 (§2.4) confined its role
  in the coverage at `D ≥ 10` to row 14 on ONE-CLASS, and ONE-CLASS is Phase 40's (below), so
  **the coverage never needs ONE-EAR**. It remains GENERIC's (row 22's one-ear step). Its open
  parts, for an attack at `d = 5` when GENERIC opens:
  - **The motive:** `G[V₁]` attains at a general configuration of `G[V₁]` plus the ear
    `a − x − b`, restricted to `V₁`. At `d = 3` this is `lem:pencil-one-ear-base`; at `d = 4`
    without a shared neighbour the incidence is free, as two planes of `P⁴` meet in one point.
    New at `d ≥ 5`, and at `d = 4` with a shared neighbour. At `k = 2` every configuration of
    `G₁` lies on the locus, so `G₁` attaining and the motive are two open conditions on one
    irreducible space, and meet.
  - **The insertion:** `dim(ρ + Λ) ≥ min(s + 1, dim(ρ + Λ²(A+B)))`, the `Pᵈ` form of
    `lem:pencil-insertion-two`, and **X2**: where M holds, `W ⊉ Λ²(A+B)` unless `W = Λ²`. X2 is
    free where `Π_a + Π_b = K^{d+1}`, so `Λ²(A+B)` is everything: at `d = 3`, where M gives
    `Π_a ≠ Π_b`, and at `d = 4` when `Π_a ∩ Π_b = ⟨y⟩`. Both are measured only beyond that.
  - **`(⋆)` at `k = 1` with `def[D](G[V₁]) > def[D](G)`: not needed.** Theorem S holds at every
    `D ≥ 6` (T5, §2.4), so the coverage uses a one-body chain only where row 14's
    `def[D](G[V₁]) ≤ def[D](G)` holds, or splits it off. Measured anyway at 46 cells (T4), with
    `dim(ρ + Λ) = min(dim ρ + 2, D)`.
- **ONE-CLASS** (T5, §2.4): the graphs past rows 1–5 with `def[D](G) = 0`, only one-body chains
  and no core at `D`, the only ones where the coverage at `D ≥ 10` could need ONE-EAR. **Settled
  `[PROVED]`** (this session, Claude Opus 5.5, at the PI's call, §1; `Strata.md` Result 27):
  each has `def[6](G) = 0`, so Phase 40's `P³` witness embeds (Result 15). The lemma: let `G` be
  sparse, of minimum degree two, with no two bodies of degree two adjacent, and `D ≥ 6`. If
  `def[6](G) > 0`, a set `W` of least `s_3` among those of two or more bodies with `def[D]` zero
  is a core at `D`.
  - *A set below `V`.* Let `P` attain `def[6](G) > 0`. Refining a part by a partition changes
    `P`'s value by that partition's value in the part (`lem:separated-partition-value`), so each
    part has `def[6]` zero, so `def[D]` zero (`lem:deficiency-antitone`). The singletons have
    value `6(n − 1) − 5|E| < 0`, since no two bodies of degree two are adjacent gives `5|E| ≥ 6n`
    (the count in `lem:pencil-x0-sparse-count` (2)). So some part `Z` has `|Z| ≥ 2`, and `Z ≠ V`.
    As `v_6(P) = 2v_3(P) − e(P) > 0`, `v_3(P) ≥ 1`, and `lem:deficiency-singleton-bound` gives
    `s_3(Z) ≤ s_3(V) − v_3(P) < s_3(V)`.
  - *The core.* `s_3(W) ≤ s_3(Z) < s_3(V)`, so `W ≠ V`. If some `X ⊇ W` had `s_3(X) < s_3(W)`,
    one of least size would have `s_3(Q) ≥ s_3(W)` whenever `W ⊆ Q ⊊ X`, so `def[D](G[X]) = 0`
    (`lem:deficiency-core-bound` (1), read at `D` as in T5), against the choice of `W`. So
    `s_3(W) ≤ s_3(X)` for every `X ⊇ W`: no body outside `W` has two neighbours in it
    (`lem:deficiency-add-body`), and `lem:deficiency-additive-core` (2) gives the additivity.

  The second half also shows that `G` has a core at `D` exactly when a set of least `s_3` among
  those of `def[D]` zero can be taken proper. The lemma first posed here (ONE-CLASS empty at
  `D ≥ 15`, an unshared chain at `D = 10`) is not needed, and is not what holds: cells with no
  core occur at every `D` measured, all with `def[3] ≤ 2`, so outside the content range at
  `d ≥ 5`. Checked by `oneclass.py` (§2.4).
- **CARRIER** (rows 3, 9, 12, 19–21): PD-STATE's, **done at 42b's close** (2026-10-30,
  `notes/Phase42b.md`). The point-based `HasPencilPanelRealization` is the wrong object at
  `d ≥ 4`: at `k ≥ 3` the hinges at a body pass through one point and need share no line
  (`rem:pencil-d-point-type`). The all-`d` polarity is `complementIso` (`Molecular/Meet.lean`), so
  rows 9 and 12 needed only conjugation through it; rows 19 and 21 were not re-read (PD-REDUCTION's
  and GENERIC's). **Verdict, checked against the definition bodies at 42b's open** (Claude Opus
  5.5; the two surprises by `lake lean` witnesses, scratch, not retained): read literally, the dual
  form fails both ways. (W1) On the containment carrier the encoding "normals on each closed
  neighbourhood span ≤ 3" is strictly weaker than Phase 39's at `d = 3`: two bodies, three
  parallel edges, one panel, hinges `e₁e₂`, `e₁e₃`, `e₂e₃` with no common point. (W2) On the meet
  carrier parallel edges share one hinge, so the double edge cannot reach rank `D`, as Phase 39's
  bare conjunct does. What agrees is the dual form with each body's 3-space `Π_v ∋ b_v` as data,
  every hinge at `v` through `Π_v^⊥`: Phase 39's definition at `k = 2` (`Π_v = q_v^⊥`), the meet
  form its adjacent-distinct case. The PI took it (§1, option (a)); it is
  `def:pencil-d-realization`.
- **GENERIC** (row 22): route B in `Pᵈ`, an irreducible parametrization of the nondegenerate
  realizations, and the one-ear step at `d ≥ 5`. D's candidate witness against the good-ear lemma
  supplying a common neighbour: `C₆` with the chord `14` and `y` joined to `2, 5` (by hand,
  feasibility settled by 42d's NONDEG S11: it is feasible). It has `def[3] = 0` (Result 22), so
  its rank is Result 17's; the question it raises is GENERIC's alone. **42d:** under C2-same, the
  carrier is the lifts of a `P³` realization (motive `RL_d`), every arm of the reduction lifts, and
  the one-ear step reduces to one obligation, (W), proved at every `W₀`-ear (S34–S36); NONDEG
  closed at review 2, 2026-10-30 (`notes/attacks/nondeg/`). Left: the coverage (A) and the write-up.

### 2.4 Proposed tests (T1–T5 run)

- **T1** (row 5): at `d = 4` on the `--d4` population, the flat rank `10(n−1) + 3 − dim L(q)` and
  R1's base `10(n−1) − def[6]`. **Run** at `d = 4, 5, 6` (`Strata.md` Result 20): both formulas
  hold; R1's base is at the `Pᵈ` target on 30 of 36 simple graphs at `d = 4`, missing only cycles
  and `C11ear`.
- **T2** (CERT): the certificates at `d = 4, 5, 6`, by exact rank. **Run** at `d = 3..6`, over
  every field (Result 21; §2.3).
- **T3** (SHORT): at `d = 4`, ears with `3 ≤ k ≤ 8` and `def[10](G[V₁]) > def[10](G)`: does a
  general datum give `W ⊇ star(y₁) + star(y₃)` with `W ≠ Λ²`, and does (⋆) hold? **Run** at
  `d = 3, 4, 5` (`Strata.md` Result 24; `--short`, seeds 1–3, the cells seed-independent), on
  danger cells only (§2.3), two per family, `d` and `k`, `n ≤ 40`. `G[V₁]` is a cycle, or a theta
  with `a, b` its hubs, inside two paths, inside one, or a hub and a path body, or a necklace of
  diamonds, where a pencil condition binds at every diamond body. Every deficiency is certified by
  a partition and a generic rank (the cells at `d = 4, 5` have `n ≥ 17`, past the DP cap). At all
  72 cells at `d = 4` and 126 at `d = 5`,
  `G[V₁]` and `G''` attain, `W` contains neither star, each star meets the rest of `W` in the
  general-position dimension, and `x₂` at a general point gains the dimension (⋆) needs; (⋆) also
  holds at a general ear datum of `G`. Modulo the stars, `ρ`'s image has dimension
  `min(dim ρ, C(d−1, 2))`, the joins' `min(k − 3, C(d−1, 2))`, and `W`'s is everything. The 24
  cells at `d = 3` assert the chapter's theorem. So X3 stands, and the step that moves `x₁` and
  `x₃` is not needed on this population; §2.3 bounds what is left.
- **T4** (ONE-EAR): at `d = 4, 5`, the rank of `G[V₁]` on `G`'s configurations, one-body chains
  whose ends share a neighbour; at `d = 5, 6`, `dim(ρ + Λ²(A+B))` against `3 + f − def[D](G)`.
  **First half run** (`Strata.md` Result 23; `--oneear`, seeds 1–3, the cells seed-independent).
  The ear is `a − x − b` on theta graphs, `G₁ = G − x`, and a configuration of `G` restricted to
  `V₁` is a general point of the incidence locus. On `θ(2, 2, k)` (`k = 4..10`, the ends share
  one neighbour) and the control `θ(2, 3, k)` (`k = 4..9`, none), where the step's merged
  hypothesis holds, `G₁` attains there at all 26 cells. The locus is proper: `dim(Π_a ∩ Π_b)` is 2
  on it against 1 at `G₁`'s own configuration on `θ(2, 2, k)`, and on `θ(2, 3, k)` 1 against 0 at
  `d = 5` (1 and 1 at `d = 4`, where the incidence costs nothing). The step's other hypothesis
  read at `D`, `def[D](G₁) ≤ def[D](G)`, fails at `d = 4` on `θ(2, 2, 9)` and `θ(2, 3, 8)`
  (`G₁ = C₁₁`): there `(⋆)` at `k = 1` asks `dim(ρ + Λ) ≥ 3`, not 2, the second half's question.
  On `θ(2, 2, 2, k)` (`k = 5..10`, two shared neighbours `y, w`; the merged hypothesis fails under
  the cap) `G₁` attains at 11 of 12 cells and misses at `k = 10`, `d = 4`: 119 against 120, a
  target `G₁`'s own configuration certifies. **The miss is forced.** Where `b_x, b_y, b_w` are
  independent, `Π_a` and `Π_b` (each 3-dimensional, both containing them) coincide, so the cycle
  `a y b w` has its four hinges in the 3-dimensional `Λ²Π_a`. A dependency among them, with
  `k`-path coefficients solving the long cycle's equation, is a nonzero motion assignment of `G₁`
  (`Strata.md` Result 1) wherever the path's hinges span `Λ²K^{d+1}` (so `k ≥ D`), and `G₁` ranks at most
  `D(n₁ − 1) − 1`. Both conditions are open on `G`'s irreducible configuration space and hold at
  the seeded point (the driver checks both, exactly, and lists the cell), so the bound holds on a dense subset of the locus.
  **Second half run** (`Strata.md` Result 25; `--orbit`, seeds 1–3, the rows seed-independent).
  The orbit cells: open ears with `k = 1, 2` interior bodies at non-adjacent ends and
  `def[D](G[V₁]) > def[D](G)`, where row 12 does not apply, on the content range at `d = 3..6` (the old range `def[3] ≥ d − 2`; ibid.).
  The population is T3's six families, `n ≤ 40`, every deficiency certified, M certified per cell.
  - `k = 1`: 46 cells, Result 23's two `d = 4` cells among them, all with M. `G[V₁]` attains on
    the locus at every one, `d = 6` included, and `(⋆)` holds: `dim(ρ + Λ) = min(dim ρ + 2, D)`,
    so `ρ` supplies the `need − 2 = f − def[D](G)` that the `d = 3` hypothesis
    `def(G̃[V₁]) ≤ def(G̃)` makes at most zero.
  - `k = 2`: 69 cells with `def[D](G₁) = def[D](G)`, so `(⋆)` needs `s + 1`, `s = dim W` at
    `G₁`'s configuration. 16 are danger cells at `d = 5, 6` with M: `10 ≤ s ≤ D − 1`, so
    `W` could hold `Λ²(A+B)`. At every cell `G₁` and `G[V₁]` attain on the locus and a general
    insertion reaches `min(s + 1, c)`, `c = dim(ρ + Λ²(A+B))`. At all 62 with M, `W ⊉ Λ²(A+B)`
    and the insertion gains `(⋆)`'s one dimension, so the route goes through.
  - The 7 cells without M, at every `d` from 3 to 6, are necklaces whose ends lie in two diamonds
    joined by one edge. Each diamond's points lie in one 3-space, the edge's ends lie in both, and
    `y` makes three, so the locus forces `Π_a = Π_b` (`dim Λ²(A+B) = 3`). There `c = 3 < 4 =
    need` and the route fails, at `d = 3` as at `d = 6`; `G` attains at its own configuration.
- **T5** (coverage): which rows of the coverage carry the graphs at `D = 10, 15`. C's hand count:
  `K₄` with every edge subdivided twice takes the orbit cell at `D = 6` and row 12 at `D = 10`.
  **Run** (`Strata.md` Result 26; `--coverage`, exact combinatorics, seed-independent), with two
  arguments by hand (this session, Claude Opus 5.5; `HARNESS.md`: claimed proved, read the proof
  before building on it).
  - **Theorem S at `D` `[PROVED]`.** The proof of `thm:pencil-x0-theorem-s` holds at every
    `D ≥ 6` with "rigid" read as `def[D] = 0` and "usable" read at `D`: `k ≥ 3`; `k = 2` with
    `m = f`, or ends apart and M; `k = 1` with `m = f` or `m + D − 1 ≤ f`. Here
    `f = def[D](G[V₁])` and `m = def[D](G[V₁]; a, b)`. The constants move as follows.
    `lem:deficiency-one-body-chain` (2) gives `m + D − 1 ≤ f` unless `x` lies in a `D`-rigid set:
    its `10 − 6 = 4` becomes `2(D − 1) − D = D − 2`, and an edge from `x` to another part costs
    `D − 1 > D − 2`. `lem:deficiency-two-body-chain` holds at `D ≥ 6`, since a tight set is rigid
    at 6 and hence at `D` (`lem:deficiency-antitone`). The 4-cycle is `D`-rigid at `D ≥ 4`.
    `lem:pencil-x0-sparse-count` (2) gives `s_D(V − x) = Dn − (D − 1)|E| − 2 < 0` from
    `5|E| ≥ 6n`. `lem:deficiency-core-bound` needs only that a value of at most zero at `d = 2`
    is at most zero at `D ≥ 3`. `-merge-rigid`, `-add-body` and `-ear-merge` hold at every `D`,
    and the additivity is planar. So a graph past rows 1–5 has a chain usable at `D` or a core at
    `D`. It uses a one-body chain only through `m = f`, which gives `f ≤ def[D](G)`, or through
    the split-off. **ONE-EAR's third part is never needed.**
  - **Where ONE-EAR can be load-bearing, `D ≥ 10` `[PROVED]`.** Call a row GEN when its `Pᵈ` step
    needs only formal work (§2.1's GEN rows, CERT, CARRIER, SHORT's X3 range, row 14 at `d = 4`
    without a shared neighbour). For a set `W` of core bodies and whole paths,
    `s_D(W) = ΣL − D·c`, with `ΣL` the paths' lengths and `c` the cycle rank. Let a graph past
    rows 1–5 have no GEN row. If `def[D](G) > 0`, it has no `D`-rigid set, since Theorem S's
    maximal one would be a core. Then every one-body chain splits off by (2). And `s_D(V) ≥ 1`
    with `c ≥ e/3 + 1` (core bodies of degree 3 or more, `e` core edges) forces a path longer
    than `D/3`, so a chain with `k ≥ 3`. If `def[D](G) = 0` and every chain has `k ≤ 2`, then a
    two-body chain has `s_D(V₁) ≤ e(3 − D/3) − 3 < 0`. So a `D`-rigid set avoids `x₁`, and
    Theorem S's argument with `X₀ = {x₁}` gives a core. **So a graph with no GEN row has a chain
    with `k ≥ 3`, or `def[D](G) = 0` and only one-body chains.** Given SHORT, row 15 is never
    needed at `D ≥ 10`, and row 14 only on that class, call it **ONE-CLASS**: `def[D](G) = 0`,
    every chain one-body, and no core.
  - **Measured.** The population is subdivisions of ten cores of minimum degree 3 (`θ₃`, `θ₄`,
    two small multigraphs, `K₄`, `W₄`, the prism, `K₃,₃`, the cube, Petersen), each core edge a
    path of 1–4 edges, simple, sparse and in the old content range `def[3] ≥ d − 2`. That is every length vector up to
    isomorphism on the five smallest cores and 60 drawn on the others: 1077, 1059, 1021 and 957
    cells at `d = 3..6`. At `d = 4, 5, 6` every cell has a GEN row, so no cell needs SHORT-CORE or
    ONE-EAR. A core is present at every one, and is the only GEN row at 20, 9 and 6. So the cover
    rests on row 9, and the second read of rows 9 and 12 (§1; landed, §2.1) weighs more. A one-body box (paths
    of 1–2 edges) gives 231, 180 and 131 cells at `d = 4, 5, 6`, all with `def[D](G) = 0` and
    every chain one-body, and each has a GEN row. At `d = 5, 6` each has a core, its only GEN row
    (row 14 the alternative), so ONE-CLASS is not met there. At `d = 4`, 228 have a core. The other
    three are in ONE-CLASS: `K₃,₃` and two Petersen subdivisions, `def[3] = 2`. Row 14 carries
    each at ends that share no neighbour, and so does R1's base row. At `d = 3`, 8 cells have only
    `k = 1, 2` ear rows (7 only row 15's), C's `K₄` among them; it takes row 12 and a core from
    `d = 4`. Past the box, Petersen with every edge a 4-path at `d = 4`, or a 6-path at `d = 5`,
    has only SHORT-CORE's rows (`k = 3`, `k = 5`): `def[D](G) = 0` and no core (by hand, every
    proper subgraph has `ΣL > D·c`, so no proper set is `D`-rigid). So the coverage needs
    SHORT-CORE, and on this population ONE-EAR nowhere.
- **ONE-CLASS** (the PI's call after T5, §1; `Strata.md` Result 27; `oneclass.py`, exact, no
  draw). Proved by hand (§2.3) and checked at `D = 6, 10, 15, 21`. On T5's ten cores and every
  core of nauty's on 4–8 bodies with at most 12 edges, paths of 1–2 edges (279 and 13 738 cells),
  `def[6] > 0` never occurs: it needs a quotient with under `6/5` edges per part past the first,
  a ring of rigid blobs. The 523 cells with no core all have `def[3] ≤ 2`. On three necklaces of
  diamonds and `K₄ − e` (432 cells, 151 with `def[6] > 0`) the proof's set is a core at every
  cell and `D`. **So with T5, a graph past rows
  1–5 at `D ≥ 10` has a GEN row (the embedding of Phase 40 at `def[6] = def[D]` counted, Result
  15) or a chain with `k ≥ 3`, and the coverage's only new mathematics is SHORT-CORE.**

### 2.5 Where the dimension bites: two frames (2026-10-29)

This session (Claude Opus 5.5) read §2.1–§2.2 against `Strata.md` Results 15–19 with the PI. The
question: is `d = 4` to PENCIL-D what `d = 3` was to KT? Not in KT's sense. KT's proof is uniform
in `d`: its geometry, two panels meeting in a `(d−2)`-flat, is the same in every `d`, and `d = 3`
is the worked case (Lemma 6.10; §6.4.2, p. 692: *"The proof strategy is exactly the same as
`d = 3`"*). The pencil's `Π_v` stays 3-dimensional while `K^{d+1}` grows, so incidences that are
free in `P³` become conditions. That gives two kinds of threshold:

- **The steps' thresholds, 4 and 5.** At `d = 4` the short ears and route B's steer fail (rows 13
  and 22: two stars have codimension `C(d−1, 2)`). At `d = 5` the one-body ear and route B's
  one-ear fail outright (rows 14 and 22: `Π_a ∩ Π_b` has dimension `5 − d`). So `d = 4` is where the
  `P³` argument first breaks, not where it breaks in its general form: a `d = 4` ONE-EAR may use the
  point `Π_a ∩ Π_b`, which is gone at `d ≥ 5`. T4 (`d = 5, 6`) asks whether 5 is the last
  threshold. Rows 13, 15 and 22 are where Phase 40 found new mathematics at `d = 3` (SHORT, ORBIT
  and route B; ROADMAP §40).
- **The graph's threshold, the least `d′` with `D_{d′} ≥ def[3](G) + 3`** (the first form was `2 + def[3](G)`; the sharp lemma's, §3 item 2). Inside the outer induction on `d` (§2.2), `G` attains
  at `d` from `P^{d−1}` whenever `def[3](G) + 3 ≤ D_{d−1} = C(d, 2)`. Then
  the sharp Result 16 makes `def[D_{d−1}] = def[D_d] = def_∞`. So the work at `d` is the graphs with
  `def[3](G) ≥ C(d,2) − 2` (≥ 4 at `d = 4`, ≥ 8 at `d = 5`). That class is nonempty at every `d`, so no
  fixed `d` suffices; a `P⁴` theorem gives every `d` at `def[3] ≤ 7`. (This was first written as
  `def[3] ≥ d − 2`, a superset at every `d ≥ 3`; the figures below were drawn on it.) Such a `G` has a partition with
  `e(P) ≤ (3|P| − 3 − def[3])/2`, a quotient of average degree below 3 and rich in ears, which is
  where rows 13–15 sit.

**The evidence where the conjecture has content**, read off `strata.py --pd --seed 1`. Of the 36
simple capped graphs, 24 have `def[3] ≤ 1` and are settled at every `d` by Result 17. The cells at
`d ≥ 4` with `def[3] ≥ d − 2` (the old, wider range) are 47, on 18 graphs (12 capped, 6 past the cap). Result 19's 41
leaves out each graph's top cell, `d = 2 + def[3]`, which also carries content.
- **Six are cycles.** Every body has degree 2, so the pencil condition is empty (three points span
  a plane), and these cells are KT's case.
- **The other twelve** are thetas, cycles with triangle ears, subdivided `K₄`, `K₃,₃` and Petersen,
  and `ring5`. In all but `ring5` the condition binds at 2 to 10 bodies, and `ring5`'s only content
  cell is `d = 4`.
- **What none of them has, in that range:** row 14's configuration (a one-body ear whose
  non-adjacent ends share a neighbour), route B's two hubs with three common neighbours, or a
  condition at every body at `d ≥ 5`.
- **Measured since** (`strata.py --content`, seeds 1–3; `Strata.md` Result 22): 38 more content
  cells, on 15 graphs that carry all three between them, every one at its target. Up to `d = 6`
  these are `θ(2, 2, k)` (`k = 4..10`, `def[3] = k − 2` under the cap), `θ(2, 2, 2, k)`
  (`k = 5..10`, `def[3] = k − 3`) and the diamond rings at `m = 6, 7`. That makes 85 content cells,
  none below target. So far the failing rows fail as proof steps only: every graph built to carry
  their configurations attains.

**Recommendations**, for the PI (§4):
- **Measure the statement where the proof breaks**, before any attack track (**done**: every
  cell matched, above):
  - `θ(2, 2, k)` (paths of 2, 2 and `k` edges between two hubs): row 14's configuration,
    `def[3] ≥ k − 2` by the singleton partition, `n = k + 3`.
  - `θ(2, 2, 2, k)`: route B's, `def[3] ≥ k − 3`.
  - Diamond rings at `m = 6, 7`: a condition at every body, `def[3] ≥ m − 3`, certified by reaching
    `D(n−1)` as `ring5` is.
  - D's candidate witness (§2.3, GENERIC).

  A shortfall redirects the phase. A match is the first evidence where the failing rows bite.
- **Run T3–T5 at each `d` only on graphs with `def[3] ≥ d − 2`** (the instruction as run, on the old, wider range; the content range is now `def[3] ≥ C(d,2) − 2`, T3's cells all lie in it, and T4's and T5's "content range" counts include graphs the embedding now settles), and run T3 at `d = 5` as well.
- **Attack each obligation at its own threshold:** SHORT at `d = 4`, ONE-EAR at `d = 5`, each
  checked one dimension up. `d = 4` stays the first milestone (every `d` at `def[3] ≤ 2`), but its
  ONE-EAR case must not lean on `Π_a ∩ Π_b ≠ 0`. (Since Result 27 the coverage needs no ONE-EAR,
  §2.3; it stays GENERIC's.)

## 3. Layers (stable codes)

**Standing rule for every remaining layer** (`-short`, PD-COVERAGE, PD-REDUCTION, PD-HEAD; in
force since 42g's `-long`, from the PI's 42g answer, §1): a recon or build whose Lean departs from
the chapter's proof adds a row to the proof-route ledger of `notes/Cleanup42.md` (§2) in the same
commit, and a commit that aligns a row sets its status there. A carrier encoding of the chapter's
own object (an indexing, a restriction to `V(G)`) is not a departure: such a row, once raised, is
marked `no departure` (R-6). The post-Phase-42 cleanup acts on the ledger (that note, §3).

- **PD-RECON** (42a, **closed 2026-10-30**, `notes/Phase42a.md`): settle R1 or R2 on paper, or
  refute with a certificate (§2). Verdict: R2's steps with the embedding as base row (§1, §2.2);
  the coverage's new mathematics, SHORT-CORE, proved by hand at `d = 4` (§2.3).
- **PD-STATE** (42b, **closed 2026-10-30**, `notes/Phase42b.md`): the `Pᵈ` statement layer,
  formalized in `Pencil/Grade/`, agreeing with Phase 39's `P³` definitions. Its dep-graph is
  `blueprint/src/chapter/pencil-d.tex`, 17 nodes: the carrier definitions (an extensor through a
  subspace, pencil realizations in dimension `d` with each body's 3-space as data, their rank and
  adjacent-distinct forms), the `d = 3` agreement, the dual form's bridge (independent adjacent
  normals give the meet form, and configurations over admissible pictures are pencil
  realizations), and CARRIER's restatements (configurations, attaining, the collineation, the
  scale-shift, one witness, the magnified rank, join independence). Nondegeneracy's lift is
  GENERIC's (§4).
- **PD-STABLE** (**42c**, opened and **closed 2026-10-30** at the PI's word, §1;
  `notes/Phase42c.md`): Results 15–17, formally, as `pencil-d.tex` §`sec:pencil-d-stable` (9
  nodes, all green), which is authoritative for the statements. `def[D_d]` is Lean's
  `G.deficiency d`, so `def[3]` is `G.deficiency 2` and `def[6]` is `G.deficiency 3`; the Lean
  encoding (grade `k = d − 1`, `m = d − 2` heights, the deficiency's `n` a parameter) is
  `notes/Phase42b.md` *Architectural choices*. Verdicts:
  1. *The embedding, at every `d′ ≤ d`* (Result 15; the route, §1). `ι` inserts zeros before the
     last coordinate and `φ` is the screw map it induces. On a connected `G` any injective `φ`
     adds `(D_d − D_{d′})(|V| − 1)` to the rank (`lem:screw-embedding-rank`, through the constant
     motions rather than a complement). The statement form holds at a fixed deficiency parameter
     (`lem:pencil-d-embed-realization`), and the configuration form from `d′ = 2`
     (`Graph.X0AttainsGrade.of_le`). Its `d′ = 3` case is the form PD-COVERAGE consumes,
     `def[6](G) = def[D](G)`, and settles ONE-CLASS (Result 27); its `d′ = 4` case takes Tier 1 to
     every `d`. FRICTION's `normalsJoin` map lemma landed with it (`exteriorPower_map_normalsJoin`).
  2. *The deficiency lemma* (Result 16, sharp form; `lem:deficiency-stable`): on a **connected**
     `G` (corrected at the open: two bodies and no edge have `def[D] = D`), `def[3](G) + 3 ≤ D_{d′}`
     and `d′ ≤ d` give `def[D_{d′}](G) = def[D_d](G)`; the first form, `2 + def[3](G) ≤ d′`, is
     its "in particular".
  3. *`Pᵈ` at `def[3] ≤ 3`* (Result 17 widened; Tier 0; `thm:pencil-d-deficiency-two-le-three`):
     Phase 40 at `d′ = 3` with items 1–2 (`def[3] + 3 ≤ 6 = C(4, 2)`), which covers `def[3] = 0`
     too. `Graph.x0AttainsGrade_of_deficiency_two_le_three` and
     `Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three` use the three standard
     axioms.
- **PD-ALL** (**42d**, opened and **closed 2026-10-30** at the PI's word, §1; `notes/Phase42d.md`):
  an informal proof at every `d ≥ 3` of the conditioned pair's three conjuncts, as red nodes in the
  sections of `pencil-d.tex` from `sec:pencil-d-induction` to `sec:pencil-d-generic`, which are
  authoritative; headline `cor:pencil-d-conditioned-pair`. Verdicts:
  1. *The coverage* (`thm:pencil-d-coverage`): R2's steps at every `d`, the embedding from `d = 3`
     where `def[6] = def[D]`, and otherwise a long chain or a core by the chain count
     (`lem:pencil-d-chain-count`, `thm:pencil-d-chain-or-core`). Its ear steps: SHORT-CORE's
     (`k ≥ 4` at every `d`; `k = 3` at `4 ≤ d ≤ 6`, needed only at `d = 4`) and CERT's (cycles and
     `k ≥ D − 1`; closed at review 1, `notes/attacks/cert/`).
  2. *The reduction* (`thm:pencil-d-realization-theorem`): Phase 39's in `Pᵈ`; a hinge in two
     pencils needs `dim(Π_u ∩ Π_v) ≥ 2`, so a cut edge moves one side (`lem:pencil-d-cut-reposition`).
  3. *The generic conjunct* (`thm:pencil-d-generic`): NONDEG's C2-same (the PI's, §1; closed at
     review 2, `notes/attacks/nondeg/`), feasible in `Pᵈ` exactly when in `P³`; proved through the
     lifts of `P³` realizations, with (W) at a minimal planar-rigid set (`lem:pencil-d-ear-free`).
  COUNT-A and COUNT-B formalized the counting at every `D` (11 green nodes, `sec:pencil-d-deficiency`).
  The split-off and the ear step that assumes `def_d(G[V₁]) ≤ def_d(G)`, which no coverage step
  uses, were cut at 42f's open (the PI, §1). Two fresh
  reads checked the coverage and W10's generic conjunct; the close's end-to-end re-read found no gap.
- **PD-CARRIER** (**42e**, opened and **closed 2026-10-30** at the PI's word, §1;
  `notes/Phase42e.md`): Phase 40b–40d in `Pᵈ`, the first layer formalizing PD-ALL's write-up. The
  four nodes of `pencil-d.tex` §`sec:pencil-d-induction` and §`sec:pencil-d-flat` are green,
  formalized as written: `lem:pencil-d-condition-linear` (`Pencil/Grade/ConditionLinear.lean`) and
  `thm:pencil-d-flat-rank`, `cor:pencil-d-flat-attains`, `cor:pencil-d-jj-flat`
  (`Grade/Flat.lean`). Verdicts: the Lean holds at every `m`, so at every `d ≥ 2`, since no proof
  uses `d ≥ 3` (the nodes keep the chapter's `d ≥ 3`); `σ_v` is a `def` (`gradeSigma`) and `Π_v` its
  range, as PD-STEPS reads both (`def:pencil-d-ear-data`, `lem:pencil-d-planes-meet`); the flat rank
  is the plane rank plus the zero heights' (`padHeights` at no height). It edited no file a deferral
  below names. `rem:pencil-d-flat-class` is a remark, not a dep-graph node, so it was no target.
- **PD-STEPS**, **PD-COVERAGE**: Phase 40e–40m in `Pᵈ`, on R2's steps (§1), formalizing PD-ALL's
  write-up after PD-CARRIER. **PD-STEPS's first sub-phase, 42f, opened and closed 2026-10-30** at
  the PI's word (§1; `notes/Phase42f.md`): `-cut` and `-contract`, six nodes (Phase 40e/40f/40k in
  `Pᵈ`), all green, formalized as written: `lem:pencil-d-lifting-restrict`, `thm:pencil-d-cut` and
  `thm:pencil-d-bridge` (`Pencil/Grade/Cut.lean`), `lem:pencil-contract-additive-kernel`,
  `thm:pencil-d-contract-additive` and `cor:pencil-d-contract-rigid`
  (`Grade/ContractAdditive.lean`). Verdicts: the Lean holds at every `m` (the nodes keep `d ≥ 3`);
  the restriction of `m` heights is `Graph.liftingRestrict` at `α × Fin m`, no new definition; the
  kernel lemma's lower bound needs only admissibility, so it holds at any admissible `q`. It edited
  no file a deferral below names. The open cut `-splitoff` and `-ear-deficiency` (the PI, §1).
  **PD-STEPS's second sub-phase, 42g, opened 2026-10-30 and closed 2026-10-31** at the PI's word
  (§1; `notes/Phase42g.md`): `-long`, seven nodes (Phase 40's cycle and long-ear steps in `Pᵈ`, on
  CERT's closed polygons with independent joins), all green: `lem:pencil-d-polygon-normal`,
  `-polygon-star`, `-polygon-insert`, `lem:pencil-d-polygons` and `-polygon-collapse`
  (`Pencil/Grade/Polygon.lean`), `thm:pencil-d-cycle` and `thm:pencil-d-open-ear-long`
  (`Grade/Chain.lean`). Verdicts: the Lean holds at every `m`; a closed polygon is a function
  `Fin n → K^{d+1}`, with no definition and no basis of `⋀²` (2 × 2-minor functionals); the
  collapse is index-level; `|K| ≥ 4` is `4 ≤ ENat.card K`. At the PI's word the star's and the
  insertion's proofs follow their Lean (§1); the other route differences are `notes/Cleanup42.md`'s
  ledger (R-3 to R-5 open, R-6 no departure). Its open found that no `-long` node uses a `-short`
  one. It edited no file a deferral below names.
  **PD-STEPS's third sub-phase, 42h, opened and closed 2026-10-31** at the PI's word (§1;
  `notes/Phase42h.md`): the half of `sec:pencil-d-short` for open ears with four or more interior
  bodies, in every `d`. Codes: `-short` stays the section's, and its halves are **`-short-four`**,
  eight nodes (`lem:pencil-d-two-stars`, `lem:pencil-d-insertion`, `lem:pencil-d-kernel-curve`,
  `lem:pencil-d-stars-four`, `def:pencil-d-ear-data`, `lem:pencil-d-ear-data`,
  `lem:pencil-d-ear-data-open`, `thm:pencil-d-open-ear-four`; 42h, all green), and
  **`-short-three`**, four nodes (`lem:pencil-d-stars-three`, `lem:pencil-d-glued-ends`,
  `lem:pencil-d-planes-meet`, `thm:pencil-d-open-ear-three`; the three-body ear at `d = 4` to `6`;
  42i, all green), named after their theorems. 42h's Lean is three new files:
  `Pencil/Grade/Stars.lean` (the linear algebra), `Grade/EarData.lean` (the ear data) and
  `Grade/Short.lean` (the factoring through `G″`, `Graph.X0AttainsGrade.of_openEar_splitOff`, and
  the theorem). Verdicts: the Lean holds at every `m`; annihilators are read on the forms on `⋀²`
  (the chapter's pairing), so no exterior power past `⋀²` is used; at the PI's word two-stars is
  stated so and stars-four's proof follows its Lean (§1); the other route differences are
  `notes/Cleanup42.md`'s ledger (R-9 to R-12 open). It edited no file a deferral below names.
  `-short-three`'s proofs use `-short-four`'s theorem and five of its lemmas, and no `-short-four`
  node uses a `-short-three` one. The factoring applies at three interior bodies with
  `splitOff_ear_succAbove` at `k = 0`, leaving only its insertion hypothesis (a type-check at 42h's
  close, `notes/Phase42h.md` *Hand-off*).
  **PD-STEPS's fourth and last sub-phase, 42i, opened and closed 2026-10-31** at the PI's word
  (§1; `notes/Phase42i.md`): `-short-three`, the four nodes as the chapter states them, all green,
  the theorem at `d = 4` to `6`. Verdicts: the insertion hypothesis 42h's factoring leaves, over
  every base datum and every `ρ`, cannot be met at three bodies (the recon's kernel-checked
  counterexample at every `m ≥ 2` takes `la = lb` and `ρ` the joins meeting `Π_a`), where the
  chapter proves the condition only at its first stage's base data and, when `r ≤ 2`, at
  `G[V₁]`'s own `ρ`. So `Grade/Short.lean` gained a variant that takes it only there,
  `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`, of which 42h's factoring is a corollary. The
  rest is four new files, `Grade/StarsThree.lean`, `Grade/PlanesMeet.lean`,
  `Grade/GluedEnds.lean` and `Grade/ShortThree.lean`, their Lean at every `m` but the theorem's
  (`2 ≤ m ≤ 4`). Stars-three is on forms, as stars-four, and at the PI's word its statement and
  proof follow its Lean (§1; R-13 aligned), so the theorem's first stage needs no independence of
  `p_a`, `p_b`. The other route differences are `notes/Cleanup42.md`'s ledger (R-14 to R-16 open):
  when `r ≤ 2` the theorem's Lean bounds `dim ρ` by a common member of the closed neighbourhoods
  of `a` and `b`, or by glued-ends, with no component or path step. Of the files a deferral below
  names it edited only `Grade/Stars.lean`, which took `starGrade_smul`. PD-STEPS is complete.
  **PD-COVERAGE, as 42j, opened and closed 2026-10-31** at the PI's word (§1;
  `notes/Phase42j.md`): `-chains` and `-coverage`, the four nodes as the chapter states them, all
  green. Verdicts: the reductions of Phase 40 return their data (a chain of bridges, a cut vertex,
  a cycle, a maximal planar-rigid set) from public forms in `MainComponent/`, each `d = 3` lemma
  now their corollary, its name and signature kept; COUNT-C counts the chains' interior bodies,
  which partition the bodies of degree two, not edge segments (`notes/Cleanup42.md` R-17 open);
  the ear steps take a chain's fields; the distinct statement is a plain theorem, with no
  dimension-`d` `X0Dist`. Its recon spiked all four complete, and three builds landed them: the
  data forms (unpinned), `Grade/Chains.lean` and `Grade/Coverage.lean`. The coverage holds at
  every `m ≥ 1`, as the chapter's `d ≥ 3`, and the chain count without `d ≥ 3` or `ℓ ≥ 1`, which
  its other hypotheses force. It edited no file a deferral below names. Theorem S's fold goes to
  CLEANUP-42, as it reverses an import. PD-COVERAGE is complete, and with it the induction.
  **Handed on from PD-RECON** (42a's close; SHORT-CORE's workbook S56 has the detail):
  - *PD-STEPS, the short-ear step (row 13).* At `d = 4`, `k = 3, 4, 5`: the `P³` factoring
    (`Graph.X0Attains.of_openEar_splitOff`) with `D = 10`, its insertion hypothesis taken at base
    data with (P) `p_a`, `p_b` independent and (B) `la ≠ lb` or `ρ ⊆ Λ²Π_a` (S19–S21), SHORT-CORE at
    those base data (S1–S18, S35). At `k ≥ 4` in every `Pᵈ` the every-`ρ` insertion holds (S35), so
    the factoring transcribes with `D` for 6 (written out at `d = 4` only, S20). At `k = 3`,
    `d = 5, 6`: S28–S33. At `k = 3`, `d ≥ 7`: not needed (S53), given CERT's open ears.
  - *PD-STEPS, the sparse estimates (row 17).* `lem:deficiency-core-bound` at every `D ≥ 3`, read
    with "rigid" as `def[D] = 0` (S52 (iv)); formalized at every `D` by COUNT-A
    (`lem:deficiency-core-bound-d`, `pencil-d.tex` `sec:pencil-d-deficiency`).
  - *PD-COVERAGE.* Theorem S at `D` (§2.4 T5); ONE-CLASS (§2.3); and S53: from `d = 5` on, a graph
    past rows 1–5 with a chain of two or three interior bodies has a chain with `k ≥ 4` or a core
    at `D`, so the coverage there needs neither the `k = 3` short row nor row 15. Theorem S at `D`,
    ONE-CLASS and S52 are formalized at every `D` by COUNT-B (`thm:pencil-d-theorem-s`,
    `lem:pencil-d-core-positive-deficiency`, `lem:pencil-d-chain-core`, `pencil-d.tex`
    `sec:pencil-d-deficiency`, `Pencil/Grade/TheoremS.lean`); S53's chain count (COUNT-C) by 42j
    (`lem:pencil-d-chain-count`, `Grade/Chains.lean`).
    Its Theorem S duplicates Phase 40's `n = 3` proof (`Graph.IsX0Graph.exists_additiveCore`), which
    can become its `n = 3` case once the coverage reads `Graph.ChainUsable` as `ChainUsableAt 3`
    (left to CLEANUP-42 by 42j's recon, as the fold reverses an import; `notes/Cleanup42.md` §3).
    The coverage's informal proof is 42d's `thm:pencil-d-coverage` (W9; a fresh read found it holds).
    Its Lean needs forms of `lem:pencil-x0-cut-reduces`, `-cycle-reduces` and
    `-planar-rigid-reduces` that return the bridge, cut-vertex or cycle data, not only
    `G.X0Reduces G.X0Below`: landed by 42j's build 1, with the maximal planar-rigid set's data
    (`notes/Phase42j.md` *Current state*).
  **Deferred to them from PD-STATE**, each optional until a consumer needs it: Phase 40's `k = 2`
  collineation (`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`) re-proved
  as the grade lemma at `k := 2`, and its scale-shift
  (`Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts`) as the grade one at one
  height, `T = t`, through the bridge to `pencilConfigPoint`; the grade scale-shift's `t • id`
  case at every `m` (not a one-line add, for the same bridge); and the hinge form of join
  independence (the hinges `C(b_u, b_w)` rather than the joins, through the complement
  isomorphism), for the cycle and long-ear steps (rows 10–11) (**discharged by 42g**:
  `card_le_finrank_of_linearIndependent_normalsJoin`, `Grade/Chain.lean`). Each makes a `P³` file import
  `Pencil/Grade/`, which 42b's additive commits avoided. **Deferred to them from PD-STABLE**, each
  with the next commit that edits the file it names (a new declaration there rebuilds most of
  `Molecular/`): FRICTION's moves of `exteriorPower_map_normalsJoin` to `PanelLayer.lean`, beside
  `normalsJoin` (and with it, from 42g, the four `normalsJoin` lemmas of `Grade/Polygon.lean`, and
  from 42h the four of `Grade/Stars.lean` and `Grade/Short.lean`'s `complementScrew`, beside
  `panelSupportExtensor`),
  and of `BodyHingeFramework.map` and the zero-hinge motion lemmas to
  `RigidityMatrix/Basic.lean` and `GenericityDevice.lean`; and FRICTION's open `contragredientEquiv`
  in `Meet.lean`, which `Grade/Collineation.lean`'s inline contragredient would then call.
  **Deferred to them from PD-CARRIER**, with the next commit that edits `Grade/Configuration.lean`
  or `Grade/Carrier.lean` (alone, the fold rebuilds the `Grade/` stack): FRICTION's duplication of
  `gradeSigma` (`Grade/ConditionLinear.lean`), the map that
  `finrank_span_pencilConfigPointGrade_closedNbhd_le` builds inline in `Configuration.lean`, and of
  that file's private `pictureProj`, which ConditionLinear's "only if" rebuilds as a local
  `LinearMap.funLeft`. The fold: `gradeSigma` beside `gradeMk` in `Carrier.lean`, the inline map
  restated as it, `pictureProj` public; and, from 42g, `pencilConfigPointGrade_ofPoints`
  (`Grade/Chain.lean`) beside `pencilConfigPointGrade_eq_gradeMk` in `Carrier.lean` (FRICTION).
  **Deferred to them from PD-STEPS (42f)**, with the next commit that edits
  `MainComponent/ContractAdditive.lean` (alone, the fold rebuilds that file's 12 importers):
  FRICTION's duplication of the kernel argument at an additive core.
  `Graph.X0Attains.of_additiveContract` proves inline (`hlow0`, `hup0`, `honto`) what
  `Graph.finrank_ker_contractLiftingMatrix_zero_eq_and_map_eq` (`Grade/ContractAdditive.lean`)
  states. The lemma is planar and sits downstream, in `Grade/`, so the fold moves it, unchanged,
  into `MainComponent/ContractAdditive.lean` before the `d = 3` theorem, which then calls it, and
  `Grade/ContractAdditive.lean` imports `MainComponent.ContractAdditive`; no `P³` file imports
  `Grade/`. Every dependency of the lemma is already in that file's imports: a scratch copy
  compiled against it alone at 42f's close. **Deferred to them from PD-STEPS (42h)**, with the next
  commit that edits `MainComponent/Cut.lean`: FRICTION's move of the four `pathVertex` lemmas of
  `Grade/Stars.lean` (`pathVertex_add_smul`, `pathVertex_succ_castSucc`, `pathVertex_eq_of_val_eq`,
  `pathVertex_zero_single`) beside `pathVertex`, and of the three of `Grade/Short.lean`
  (`pathVertex_comp_succAbove_one`, `pathVertex_smul_comp`, `pathVertex_map`), the first with or
  after the `Fin.succAbove` values it uses. With the next commit that edits the file each names,
  FRICTION's other 42h home debts: `coe_succAbove_one` and `coe_succAbove_two`, as one
  `Fin.val_succAbove`, to the mirror `Mathlib/Data/Fin/Basic.lean` (whose edit rebuilds
  `Grade/Polygon.lean` and the files after it); and `span_range_smul_eq`, a mirror candidate, at a
  cleanup round. (`starGrade_smul` moved to `Grade/Stars.lean` with 42i's stars-three.)
  **Deferred to them from PD-STEPS (42i)**, each with the next commit that edits the file it
  names: FRICTION's glued-ends helpers (`Graph.mem_closedNbhd_comm` to `Pencil/Motive.lean`; the
  two-body contraction lemmas to `MainComponent/ContractCurve.lean`;
  `Graph.liftingPlanesDiff_eq_top_of_notMem` to `Grade/PlanesMeet.lean`), and `gradePlanarProj`
  into the PD-CARRIER fold of the picture projection. At a cleanup round, FRICTION's fold of
  `exists_insertion_earDataGrade_three` (`Grade/ShortThree.lean`), which repeats
  `of_openEar_four`'s inline tail (`Grade/Short.lean`) at three bodies: one insertion lemma for the
  ear of `G″` with `n + 2` interior bodies, called from both steps.
- **PD-REDUCTION**, **PD-HEAD**: Phase 39's reduction in `Pᵈ`; the headline `PencilPair`, and the
  flag strata as corollaries. Their informal proofs are 42d's `sec:pencil-d-reduction` and, for
  the generic conjunct, `sec:pencil-d-nondegenerate` to `sec:pencil-d-generic`.
  **PD-REDUCTION, as 42k, opened and closed 2026-11-04** at the PI's word (§1;
  `notes/Phase42k.md`): `-reduction`, the eight nodes as the chapter states them, all green.
  Verdicts: its recon spiked all eight on the landed carrier from Phase 39's `d = 3` Lean
  (`Pencil/Arms.lean`, `ArmsAssembly.lean`, `X0.lean`, `Pair2.lean`), transcribed to grade `k`
  with subspaces for points; new are `C_B` (`perpExtensor`) with the two-pencil lemma, and the base
  case's adjacent-distinct form. Three builds landed them: `Grade/TwoPencil.lean`, `Grade/Arms.lean`
  and `Grade/Reduction.lean`. The linear algebra and the loop hold at every grade, the cases at
  every `m`, and the theorem at `1 ≤ m`, the chapter's `d ≥ 3`:
  `Graph.graded_pencil_realization_theorem`, `Graph.pencil_reduction` at `n = m + 2`, whose two
  conjuncts are the headline's first two (PD-HEAD). The base and nonsimple cases count rows as the
  `d = 3` Lean does, where the chapter counts motions (`notes/Cleanup42.md` R-18, R-19, open). It
  edited no file a deferral above names. The fold of the `d = 3` cases into its graded ones goes
  to CLEANUP-42, as it reverses imports (`notes/Cleanup42.md` §3). PD-REDUCTION is complete.
  **Deferred to PD-HEAD and after from PD-REDUCTION (42k)**, each with the next commit that edits
  the file it names (FRICTION's open 42k entries): `exists_smul_extensor_eq_of_mem_span_range_grade`
  to `Meet.lean` (with `contragredientEquiv`), `ExtensorInPanel.smul` to
  `RigidityMatrix/Basic.lean`, `dotPerp_map_eq` to `Grade/Realization.lean`, and
  `finrank_span_rigidityRows_of_single_edge` to `GenericityDevice.lean` (with `ArmsAssembly.lean`'s
  inline count); at a cleanup round, the mirror candidates `finrank_span_pair_eq_two`,
  `exists_mem_linearIndependent_pair` and `exists_pair_of_ncard_le_two_of_edgeSet_nonempty`.
  **PD-HEAD's first half, as 42l, opened and closed 2026-11-04** at the PI's word (§1;
  `notes/Phase42l.md`): `-nondegenerate` (4) and `-lift` (6), the ten nodes as the chapter states
  them, all green. PD-HEAD stays the layer's code, and its halves are named by their sections:
  `-nondegenerate` with `-lift` (42l) and `-generic` (11 nodes, `thm:pencil-d-generic` and the
  headline among them; no letter), which opens at the PI's word and whose close is Phase 42's; ten
  of its eleven nodes use one of the ten. Verdicts: its recon spiked all ten on the landed carrier,
  reusing the `d = 3` Lean's polarity, `IsNondegPencilRealization`, the chart
  (`pencilChartPoint`, `pencilChartNormal`, `exists_pencilSeed_of_nondeg_of_selectors`),
  `cross₃Poly`, the polynomial section and the rank polynomial; the lift and the feasibility
  lemma's projection are new. Four builds landed them: `Grade/Nondegenerate.lean` (the definition,
  three, maps), `Grade/Feasible.lean` (feasibility, with the polynomial-function and Zariski-open
  API), `Grade/Lift.lean` (steer, the lift, lifts are realizations, attaining) and
  `Grade/LiftWitness.lean` (one lift suffices, transfer). No pin is weaker than its node. Three
  route differences stay open for the cleanup (`notes/Cleanup42.md` R-20, R-21, R-23: feasibility's
  map by forms vanishing on the subspaces, with no quadric; one lift through the polynomial section;
  transfer's open set by the rank polynomial at each `λ`); R-22, the parametrization's sixth
  auxiliary vector, is aligned at the PI's word (§1). No build edited a file a deferral above names.
  **Deferred to `-generic` and after from 42l**, each with the next commit that edits the file it
  names (FRICTION's open 42l entry): the `dotPerp` lemmas of `Grade/Feasible.lean` (`dotPerp_sup`,
  `dotPerp_inf`, `dotPerp_antitone`, `dotPerp_top`, `finrank_dotPerp_add`,
  `finrank_dotPerp_span_singleton_of_ne_zero`) to `Grade/Realization.lean` beside
  `finrank_dotPerp`, with 42k's `dotPerp_map_eq`; at a cleanup round, the mirror candidate
  `finrank_map_of_injOn` (`Grade/Nondegenerate.lean`).
  **PD-HEAD's second half, as 42m, opened 2026-11-05** at the PI's word (§1; `notes/Phase42m.md`):
  `-generic` (11), the eleven nodes as the chapter states them. They are the blueprint's last red
  nodes, so 42m's close is Phase 42's. The open's consistency read passed all eleven, their 46
  outside dependencies green (53 with the `\cref`s), nine of them 42l's nodes. The open added
  findings for the recon (that note's *Blockers*): Phase 39's `Pair.lean` and `Pair2.lean` carry
  three of the six cases, and the rest of the `d = 3` Lean is five files of `MainComponent/`; the
  good ear's `d = 3` Lean returns the body alone, its other parts read off the proof; the ear's
  condition joins two nodes through `HoldsGenerally`, which depends on the selectors; `-ear-free`
  re-runs two steps of `-lift-no-rigid`'s proof, which itself uses a step of one-witness's proof,
  not its statement; and `-lift-cut-edge` `\cref`s the fibre-intersection lemma without `\uses`.
  **Its recon** (2026-11-05, design pass; `notes/Phase42m.md` *Current state* and *Decisions made*)
  pinned the eleven signatures, each kernel-checked, and spiked `-lift-small` (1), `-lift-pendant`
  and `-lift-ear` complete, with the remark after `def:pencil-d-lift-attains` and the theorem's
  induction and the headline on the other lemmas' statements (the headline a three-conjunct
  theorem). Each case is `lift_transfer` and then `liftAttains_of_holdsGenerally`; the ear's
  condition is one predicate at the same selectors on both sides, and the good ear returns `W₀`
  (`Graph.IsPencilGoodEar`); `dim L̃`'s least value is exposed as a lemma. Phase 39's reposition at a
  cut edge does not transcribe (it fixes neither end's normal); the glue is new, with the other
  unspiked new math in `-lift-no-rigid`, `-ear-extend` and `-ear-free`. No pin is weaker than its
  node (two unused hypotheses dropped; `[Nonempty α]` at two bodies, ambient). Seven builds:
  `Grade/LiftSmall.lean`, `LiftCases.lean`, `LiftCutEdge.lean`, `GoodEar.lean`, `LiftNoRigid.lean`,
  `EarFree.lean`, `Generic.lean`. Departures: `notes/Cleanup42.md` R-24 to R-27, open.
  **At Phase 42's close**, Tier 0 joins `formalization.yaml`'s
  `main_results` and `alignment` unless the headline subsumes it, with a closed non-vacuity witness
  in `CombinatorialRigidity/Nonvacuity.lean` (`PHASE-BOUNDARIES.md`); 42c's intermediate close
  added no row, as Phase 40's sub-phases did not, and no later sub-phase close has. The
  coverage (42j) subsumes Tier 0: `Graph.x0AttainsGrade_of_deficiency_two_le_three` is
  `Graph.IsX0Graph.x0AttainsGrade` with `def₂ ≤ 3` added, so Tier 0's distinct form also follows
  from the coverage (by `Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`).

**The red nodes by layer** (42e's open, by section of `pencil-d.tex`; a letter is minted only as
a sub-phase opens). From `sec:pencil-d-induction` on the chapter has 62 dep-graph nodes, 11 of them
red (recounted at 42l's close and again at 42m's open; the first red node is
`lem:pencil-d-lift-small`): 65 at 42e's
open, all red, 4 green at its close, 3 cut at 42f's open (the PI, §1), 6 green at 42f's close, 7
at 42g's, 8 at 42h's, 4 at 42i's, 4 at 42j's, 8 at 42k's and 10 at 42l's. The count of 66 put to
the PI at 42e's open (§1) included `rem:pencil-d-flat-class`, a remark, which the dependency graph
does not draw (it draws definitions, lemmas, propositions, theorems and corollaries).
- PD-CARRIER (42e, closed, all green): `-induction` (1) and `-flat` (3); 4.
- PD-STEPS: `-cut` (3) and `-contract` (3), 42f, closed, all green; `-long` (7), 42g, closed, all
  green; `-short` (12), as `-short-four` (8), 42h, closed, all green, and `-short-three` (4), 42i,
  closed, all green; 25, all green.
  `thm:pencil-d-splitoff`, `thm:pencil-d-open-ear-deficiency` and `lem:pencil-d-polygon-ear`, with
  their sections `-splitoff` and `-ear-deficiency`, had no consumer in the coverage and were cut at
  42f's open (the PI, §1).
- PD-COVERAGE: `-chains` (2; `lem:pencil-d-chain-count` is COUNT-C) and `-coverage` (2, with
  `lem:pencil-d-distinct-statement`, the coverage read as a realization); 4, as 42j, closed, all
  green.
- PD-REDUCTION: `-reduction` (8), Phase 39's reduction; 8, as 42k, closed, all green.
- PD-HEAD: `-nondegenerate` (4) and `-lift` (6), as 42l, closed, all green; `-generic` (11, ending
  in the headline `cor:pencil-d-conditioned-pair`), as 42m, open, all red; 21, the generic conjunct
  and the headline, the largest layer.

PD-STATE and PD-STABLE do not depend on the route, so they ran beside PD-RECON (§1's defaults).
PD-STATE opened and closed as 42b on 2026-10-30, and PD-STABLE as 42c the same day.

## 4. Open questions

The PI's planning defaults (§1) answer most of the calls put at the open. A session follows them
unless a finding argues otherwise:
- `d = 4` first, as Tier 1 of three. SHORT is attacked at `d = 4` and ONE-EAR at `d = 5`, as
  attack tracks once T3 and T4 size them (§2.5). Both have: SHORT's attack was SHORT-CORE, `k = 3,
  4, 5` at `d = 4`. ONE-EAR (the motive, the insertion and X2 at `d = 5`) has left the coverage
  (Result 27, §2.3), so it waits for GENERIC. SHORT-CORE's scope does not shrink at `d = 4`: its
  targets never occur at `def[3] ≤ 3`, and at every danger cell `def_3(G) ≥ 2d − 3` (SHORT-CORE's
  review 2, workbook S50). The track closed 2026-10-30 with `d = 4` proved by hand (§2.3).
- The headline ships the bare and distinct conjuncts first, GENERIC after (row 22). Nondegeneracy
  enters `PencilPair` only in the generic conjunct (`Pencil/Motive.lean`), so with row 22's reading
  its `Pᵈ` lift is deferred with it.
- The carrier in dual form (CARRIER). Checked at 42b's open: it agrees with Phase 39's
  definitions once each body's 3-space is data (§2.3), the reading the PI took (§1).
- PD-STATE and PD-STABLE open beside the research once T1 and T2 land: they did, as 42b and 42c,
  both closed 2026-10-30.
- The generic conjunct at every `d` (rows 21–22): settled at 42d, C2-same (the PI's, §1), proved
  on paper (§3 PD-ALL).

Settled by the PI (§1): the route. R2's steps with Result 15's embedding as the base row; an outer
induction on `d` is Tier 2's question, entering if at all through CERT's open ears at `d ≥ 7`.
The carrier: each body's 3-space as data (§2.3 CARRIER, option (a)). 42d: PD-ALL, opened and closed (§1, §3). SHORT-CORE closed 2026-10-30 (§2.3), and the sharp deficiency range
`def[3] + 3 ≤ D′` (tight on cycles) is settled: Tier 0 widened to `def[3] ≤ 3` (§1), §2.5's content range
restated `def[3] ≥ C(d,2) − 2` and Tier 1's reach `def[3] ≤ 7` (the dated note under §1's planning entry).

Settled by the table: Phase 39's reduction is `d`-general for the bare and distinct conjuncts,
given CARRIER (row 19). Settled by the PI's call (§1) and Result 27: ONE-CLASS, not ONE-EAR. Its
lemma is proved, so the coverage at `d ≥ 4` needs SHORT-CORE and no ONE-EAR (§2.3–2.4).
