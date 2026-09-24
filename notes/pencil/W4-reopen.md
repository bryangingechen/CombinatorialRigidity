# W4 reopened — hand-off for the next session (2026-09-23)

**Read this first, then `notes/Phase39.md` *Status*, then `notes/pencil/workbook/W4.md`'s
header and the sections named below.** Written at the end of attack gr10 session 1 at the PI's
request, against the tree at `b0d76407` (master) + `3773c022` (branch `attack-gr10`). Lean
pointers are by declaration name; Lean unchanged since `084ee4ff`. Revised after
`/review-attack gr10` and its close commit `3d769296` (2026-09-23): the worktree and merge notes, T0's gr10 items (done), and T2's optional char-2 leg. Revised again by the T0 commit (T0 marked DONE; the worktree bullet made path-free).

**The decision (user, 2026-09-23, verbatim):** *"OK, I'd like to reopen W4."* — and on where to
run it: *"I'll probably run it in this same worktree as the smark agent is still proceeding in
the main one."*

**Gate G0 — SETTLED (user, 2026-09-23): a staged lift.** Asked whether the 2026-08-05 Lean hold is
lifted for the whole **W4 build** item or only for T1's wrapper, the agent recommended lifting it
now for (i) T1's W4 wrapper (a new declaration carrying (K-res), and any other unsettled piece, as
hypotheses; no `sorry`; no edit to smark's consumer) and (ii) **W4-L4b**
(`exists_degree_two_of_co1_rigid`, a pure graph lemma, pinned and spike-elaborated, independent of
(K-res) and (α)), keeping **W4-L1/L2/L3′/L5 parked** until T1 (question (b), the residual L7a
sibling re-traced against the 2026-09-16 `hK`) and T2 (placement step or kernel) report, then
one more call. The user said: *"OK, sounds good."* Record this verbatim in T0's adjudication entry
and in `notes/Phase39.md` *Blockers* (hold lifts are recorded per item).

## Where you are working

- The gr10 worktree, branch `attack-gr10` (branched at `b0d76407`; the gr10
  session-1 commits plus `3d769296`, the review-1 close).
  The **smark attack is running in the main checkout** on `master`. Never touch
  `notes/attacks/smark/` or `notes/pencil/workbook/attack-smark.md`.
- Files both lines are likely to edit: `notes/Phase39.md`, `ROADMAP.md`,
  `notes/harness/incidents.md`. Keep edits there small and anchored; expect a trivial merge.
  Before starting, `git log --oneline master -5`: at T0 master was two smark-only commits (s14)
  ahead and the branch was **not** rebased (rebase vs merge commit is the PI's call, below).
- **Merge (user, 2026-09-23):** `attack-gr10` merges into master at a moment when the smark
  agent is between sessions (e.g. after this session's T0/T1 commits) — never under a running
  smark session. Master has since moved (smark s14), so this is **no longer a fast-forward**.
  Master's new commits touch only smark files, so the merge is textually clean. Either
  `git rebase master` in this worktree first (the branch is unpushed), or merge with a merge
  commit: the PI's call. A rebase rewrites the SHAs this file cites (`3773c022`, `3d769296`):
  repoint them in the same step.
- Commit rules: `CLAUDE.md` *Working* (author identity, `-F` for messages with backticks,
  no local paths).

## Why reopen (the mathematical reason the 2026-09-03 directive asks for)

W4 was parked on 2026-08-02 (route 3, packaging (b), "recorded as a decision, not built", because
its one remaining kernel **(K-res)** "and the pinned `hK` share their crux";
`notes/pencil/adjudications.md` § *Relocated 2026-09-03*). Since then:

1. **smark's `hK` side is closed informally.** smark `state.md`: "Case (iii), `hK`, all `m` —
   closed modulo O9 (written, S16(vi))". O9 (descent to a `K`-point) is not open: S16(vi) is
   proven-informally given irreducibility, irreducibility on `hK`'s arm is Case 1 (S17(vii)(b)),
   proved by S19; review 4 re-derived S19 end to end and S16(vi) (workbook S23(iv)), and S21(v)
   was confirmed at S24(ii). smark's four open pieces (O7e-b(a)–(c), O7e-c) are all `hbareSplit`,
   case (iii), `m ≤ 4` — the infeasible arm, which never occurs at a residual (residuals are
   feasible by (K-res)'s own hypothesis).
2. **(K-res) as written is stale.** `W4.md` § *widened kernels* *Step 4* states it in the
   pre-2026-09-16 shape of `hK`: no induction hypothesis, chart-form conclusion (∃ selector, seed,
   independent `pencilRow`s). Since checklist item 5, `hK` takes the IH and concludes
   `HasGenericPencilRealization K 3 G` directly (`notes/Phase39-design.md` § *Kernel restatement
   (2026-09-16)*). R2 uses exactly the IH and the split-off antecedent as certificates, so the
   stale form cannot even receive R2's argument.
3. **The grid route's criterion for residuals is refuted (method, not target):** (RS-5) fails at
   `R20` (gap map row §(K-res)/(RS-5); `python3 notes/gapmap.py --row '§(K-res)/(RS-5)'`). The
   same method-vs-target split gr10 just drew for characteristic 2 (workbook
   `attack-gr10.md` S4).

## What is already closed on W4 (do not redo)

From `W4.md`'s header and sections: route 3 packaging (b) adjudicated; (T) proved (§(SAFE-RES)
*Step TF5*); (E-loc) refuted and shown unnecessary (§widened kernels *Steps EL4–EL6*); (E-pair)
proved (*Steps PR1–PR6*, *GW1–GW6*) and (V) with it. The build is decomposed with gates
N8/N9/N10/N10b passed: `notes/Phase39-design.md` §§ *W4 decomposition recon (2026-07-30)* and
*W4-L4 identification recon (2026-07-30)*; leaf sequence in `notes/Phase39.md`'s **W4 build**
checklist item (W4-L4b `exists_degree_two_of_co1_rigid` first, then W4-L1/L2/L3′/L5; residual
carry `hnoGood'`, non-vacuous by a `|V| = 19` witness, so branch 4 needs content).

## Open on W4

- **(K-res)** — the kernel, restated (T1) and then attacked (T3).
- **The (α) obligation** — `W4.md` § *The (α) obligation — `hcontract` must un-coincide at
  parallel classes (2026-09-16, OPEN)*: under the third `PencilPair` conjunct the contraction
  assembly must deliver adjacent-distinct points when `G` is simple, but the IH at `G/H` is
  necessarily coincident at parallel classes. Expected a placement step; "nothing has been
  checked"; cost not priced.
- **The build** itself (T4).

## Tasks, in order

**T0 — record the reopening — DONE (2026-09-23, the T0 commit).** `notes/pencil/adjudications.md`
§ *2026-09-23* (the decision, the three reasons, G0 and the three further calls, verbatim where
the user's words are known); `notes/Phase39.md` *Status* header, *Current state* (lead sentence,
the W4 sentence), the checklist preamble and the **W4 build** item (staged), *Blockers* (hold lift;
the (K-res) bullet), *Hand-off* and *Decisions made* (one line; the note rebalanced to stay under
its line cap); the ROADMAP Status cell; `W4.md`'s header; the `Phase39-design.md` arc index. The
gr10 sentences on those surfaces were kept; the gap map's (K-grid) row is untouched (gr10 brief
§A4). N1 is not commissioned; T2 carries the one characteristic-2 population that bears on a
live decision.

**T1 — design pass: (K-res) restated against today's `hK`, landed as a carried hypothesis.**
A `/coordinate-phase 39` recon or design commit (not an attack; there is no consumer yet —
producing one is the point). Starting draft, to be *checked*, not trusted:

```lean
(hKres : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
  G.TwoEdgeConnected → PencilNondegFeasible K G →
  G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
  (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
  (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
  HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
  HasGenericPencilRealization K 3 G)
```

i.e. `hK` of `pencilPair_of_splitOff_of_habitat` token for token with `hnoRigid` ↦
`PencilNondegFeasible K G`. Questions the pass must settle from the route-3(b) call site, not
from prose:
- (a) **Habitat antecedent** — left to this pass by the user (2026-09-23: "design pass
  decides"; the agent's suggested default was residuals only, matching packaging (b)). With no `∃ H, H.IsProperRigidSubgraph G 3` antecedent the
  statement also covers `hK`'s feasible habitat (packaging (a) in disguise); the minimal honest
  form restricts to residuals. Which does the dispatch supply? Are `f(V(G)) ≤ 4` and
  triangle-freeness available there for free (`W4.md` *Step 4* says they may be added)?
- (b) **The antecedent's source.** Under `hK`'s current consumer the split-off antecedent comes
  from the IH at `G.splitOff`, whose simplicity uses `hnoRigid`
  (`Graph.splitOff_simple_of_noRigid_of_card`). At a residual that step is the L7a sibling's
  (S3)/(S4)/(S5), supplied by (T) + (V) of §(SAFE-RES′). Re-trace it against the 2026-09-16
  structure of `pencilPair_of_splitOff_of_habitat` — the old L7a leaf shape predates the IH.
- (c) **Where it lives.** A new declaration (a W4 wrapper taking `hKres` and the other W4 leaves
  as hypotheses and producing `hcontract`'s statement), with **no edit** to
  `pencilPair_of_splitOff_of_habitat` or `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
  (smark's consumer). Lean: the wrapper and W4-L4b only (G0).
- (d) **Blueprint.** Forward mode: a red node for (K-res) and the wrapper in `pencil.tex`, pinned
  by `\lean{...}` in the same commit (`blueprint/CLAUDE.md`).

**T2 — (α) recon (read-only, or a docs + driver commit).** Question: at the contracted witness
the assembly starts from, which pairs coincide (exactly the parallel classes of `G/H`?), and can
un-contracting separate them while holding the rank? Deliverable: a verdict "placement step" or
"kernel", with a committed, seeded, exact driver (`HARNESS.md` *Reproducibility*) over a named
population — e.g. the residual pool behind `W4.md`'s witnesses (`W19`, `S29`, `T32`, `R20`, the
255 residual inhabitants `W4.md`'s sweeps ran on, censused as (RS-12) in `grid.md` §(K-res)). Templates to try first (`W4.md` *What would change
this* (ii)): `hasPencilRealization_of_not_twoEdgeConnected_core` and the distinctness clause of
`exists_reposition_cross_incidences`. Independent of smark; can run alongside T1.
*Optional char-2 leg (from the gr10 review, 2026-09-23):* gr10's evidence covers no residual,
because every gr10 shape has no proper rigid subgraph, so T1's `hKres` inherits no
characteristic-2 evidence. If the field binder matters to T1, run
`notes/attacks/gr10/drivers/char2chart.py`'s row construction on this same pool with target
`6(|V|−1) − def₃` in place of the hard-coded `6(|V|−1)`: a new mode, committed and seeded, where
the driver asserts the bridge's shape hypotheses per shape and reports failures.

**T3 — the (K-res) attack, after T1 lands the Lean declaration.** Create `notes/attacks/kres/`
per `notes/attacks/README.md`: a brief transcribing the T1 declaration's hypotheses one per line,
both sides, diffed against it (`HARNESS.md` *Evidence*, the consumer-diff rule — the reason to
wait for T1). Session-1 question: **does R2's proof of `hK` transfer to residuals, and if not, at
which use of `hnoRigid` does it break?** Inputs from smark, all closed (read, do not trust:
`HARNESS.md` "a `PROVED` tag is a claim by its author"): S14(iii), S16(vi), S17(v) and (vii)(b),
S19, S21(v). Reviewed: S19 and S16(vi) (S23(iv)), S21(v) (S24(ii)); **S14(iii)'s review status
not confirmed**. Where it most likely breaks: S19's three-way domain split and the strict
habitat count S19(viii), both derived under no proper rigid subgraph; `W4.md` adds that residuals
sit wholesale in the `dim R_a = 1` stratum (§widened kernels *Step 2*). Name: **`kres`**
(user, 2026-09-23). The PI approves the brief before session 1. Run it in its own worktree.

**T4 — the rest of the W4 build, when the PI commissions it.** Ordinary `/coordinate-phase 39`
work from the checklist's W4 build item; independent of smark and of (K-res), which the wrapper
carries as a hypothesis.

## Do not

- Edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` or the headline theorem.
- Write the (K-res) brief before T1's Lean declaration exists.
- Treat `W4.md`'s (K-res) statement or its cost estimates as current; both predate 2026-09-16.
- Ask smark for anything; the only optional request is a wording fix in its state line ("`hK`
  closed; O9 written, re-derived at review 4"), at its own pace, via the PI.
