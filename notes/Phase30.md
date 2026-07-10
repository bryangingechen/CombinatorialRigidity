# Phase 30 — Algebraic-independence relaxation (RELAX) (work log)

**Status:** in progress (opened 2026-07-09).

## Current state

Phase just opened; no investigation has run yet. The phase mints the
second codename off ROADMAP's post-program queue (**RELAX**) — the one
genuine *math* track there: investigate whether the molecular-conjecture
proof can weaken or avoid its reliance on **algebraic independence** of
the inductive seed's panel coordinates. The planning input is
`notes/AlgebraicIndependence.md`: **§2** (the product-route candidate,
~70% at `d=3`, UNVERIFIED) is the starting hypothesis; **§3** (the usage
tracker) is the checklist of sites. The next concrete step is the R1
recon below.

## Architectural choices made up front

- **Investigation phase, not a build phase.** The first deliverable is
  a **recon verdict**, not Lean. No blueprint chapter opens at phase
  open (the dep-graph is fully green — there are no red/deferred target
  nodes, so the phase-open red-node consistency gate is vacuous). If R1
  goes green, the follow-on refactor is a **structural-edit-mode**
  change (restate existing green nodes as the alg-independence content
  is deleted), planned then — not now.
- **The live site is at general grade.** §2's hypothesis was written at
  `d=3` (pre-Phase-23); since then the footnote-6 seed-rank transfer
  landed at general grade (`case_III_nested_rank_lower_all_k`, Phase 23a
  Leaf 4, on the live A2/A5 spine), still consuming
  `AlgebraicIndependent ℚ q`. So the recon sequence is: settle (a)+(b)
  at `d=3` first (the pinned R1 question), then §2's risk (c) — whether
  the product route closes at general `d`, i.e. whether the family of
  subgraphs the argument touches stays finite uniformly — as its own
  question. §3 rows 106/107(b) are already resolved NOT-sites; site
  107(a) is the only live one.

## Investigation checklist

- [ ] **R1 — the §2 product-route recon at `d=3`**: confirm residual
  risks **(a)** and **(b)** against the landed Lean. (a): is the seed
  `q` genuinely free at the Claim-6.11 composition — the candidates
  `p₁,p₂,p₃` and Claim 6.12's geometry are *derived* from `q`, so `q`
  must also satisfy the candidate general-position conditions; fold
  those into the product and confirm **no circularity**. (b): does the
  nested IH hand over `G_v`'s rank polynomial to multiply in — i.e.
  does `exists_rankPolynomial_of_rigidOn` compose with the nested-IH
  rigid seed for `G_v` in usable form? Deliverable: a grounded
  go/no-go verdict (with the Lean names of the composition points).
- [ ] *(conditional on R1 green)* **R2 — the general-`d` question**
  (§2 risk (c) / §3 site 107(a)): does the product route lift to the
  general-grade consumer `case_III_nested_rank_lower_all_k`, or does
  the touched-subgraph family grow with `d` so that KT's
  alg-independence hammer is genuinely needed there?
- [ ] *(conditional on the recons)* **the refactor**: product-route the
  kernel and *delete* the alg-independence content (the
  `AlgebraicIndependent ℚ` motive conjunct, the transcendental-seed
  producers, the mirror leaves) — scoped into slices only after R1/R2
  verdicts fix the reachable extent.

## Blockers / open questions

- None at open. (R1's verdict is itself the open question.)

## Hand-off / next phase

**Next concrete step: dispatch the R1 recon** — confirm
`notes/AlgebraicIndependence.md` §2's residual risks **(a)** (seed
freedom at the Claim-6.11 composition, no candidate/seed circularity)
and **(b)** (the nested IH delivers `G_v`'s rank polynomial in usable
form) at `d=3`, against the landed Lean
(`Molecular/AlgebraicInduction/CaseIII/`, the device producers
`exists_rankPolynomial_of_rigidOn` / `MvPolynomial.exists_eval_ne_zero`,
and the consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`).
Read-only; verdict in the return message. R2 and any refactor are
scoped only after that verdict.

## Decisions made during this phase

- (none yet)
