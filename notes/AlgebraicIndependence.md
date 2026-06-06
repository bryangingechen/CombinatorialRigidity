# Algebraic independence — usage tracker + relaxation TODO

**Purpose.** A standing, cross-cutting note that (1) records the **relaxation
question** — can the molecular-conjecture proof *avoid or weaken* its reliance on
algebraic independence of the inductive realization's coordinates — and (2) **tracks
every place** the program leans on that property, so a future relaxation phase can
revisit them systematically. This is a deferred-TODO ledger, not a phase log; append
to the usage table as later phases introduce new uses.

**Decision context (2026-06-06).** Phase 22d's KT-Claim-6.11 kernel (KT eq. (6.22) /
footnote 6) needs "*the inductively-fixed generic seed `q` attains the
IH/matroid-predicted rank* for nested subgraphs." The footnote-6 recon
(`notes/Phase22d.md` *Footnote-6 kernel recon*) found this is **genuinely-new
analytic content** — the project has zero `AlgebraicIndependent` machinery. The user
chose to **build the algebraic-independence route directly to fully green** (the
certain path; it is KT's actual argument), rather than gamble on the product-route
relaxation below. **So the relaxation is deferred, not on the critical path** — but
it is genuinely interesting and possibly substantially cheaper, hence this tracker.

## 1. What algebraic independence buys KT, and what we strictly need

KT's standing inductive choice (footnote 6, p. 685): at each inductive step the
realization `q` is taken with **panel coordinates algebraically independent over ℚ**.
An algebraically-independent point lies off the zero locus of *every* nonzero
rational polynomial, so `q` is automatically a non-root of *every* subgraph's rank
polynomial — hence one fixed generic `q` simultaneously attains the maximal rank for
*unboundedly many* subgraphs that arise later in the argument. This is the "generic
attains max, and this seed is generic" hammer behind eq. (6.22) and eq. (6.18).

What the proof *strictly needs* at any given use is weaker: that the **one** seed
in hand is a non-root of the **finitely many** rank polynomials that **particular**
argument touches.

## 2. The relaxation candidate — the "product-route" (avoid alg-independence at `d=3`)

**Insight (coordinator, 2026-06-06; ~70% at `d=3`, UNVERIFIED).** Our formalization
may not need algebraic independence, because the seed is *not* fixed up front the way
KT fixes it — 22c's `PanelHingeFramework.case_II_placement_eq612` takes the inductive
realization as a **hypothesis parameter**, so the seed `q` can be **chosen at the
Claim-6.11 composition**. At `d=3`, that composition touches only **finitely many**
subgraphs (`G_v^{ab}` and `G_v = G_v^{ab} − ab`). Each has a nonzero rank polynomial
(the device producer `exists_rankPolynomial_of_rigidOn`, built from each one's rigid
IH seed); their **product** (times the general-position polynomials the candidate
geometry needs) is nonzero (`MvPolynomial` over a field is a domain). The **existing**
device producer `MvPolynomial.exists_eval_ne_zero` then yields a single `q` that is a
non-root of the product — hence of each factor — and the **existing** device consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` certifies full rank at
that `q` for both `G_v^{ab}` (eq. (6.18)) and `G_v` (eq. (6.22)).

If it holds, the Claim-6.11 kernel **dissolves**: no `AlgebraicIndependent` /
transcendence machinery, no `non-root-from-alg-independence` brick, no seed-genericity
motive strengthening — just "product of finitely many nonzero polynomials is nonzero"
+ the existing producer/consumer. It also matches how Cases I/II *already* pick their
realization via the device (as a non-root of the rank polynomial).

**Residual risks (why it's ~70%, not certain):**
- **(a) Is `q` genuinely free at composition?** Stratum 1 takes it as a hypothesis,
  so plausibly yes — but the candidates `p₁,p₂,p₃` and Claim 6.12's geometry are
  *derived* from `q`, so `q` must also satisfy the candidate general-position
  conditions. Those are *more non-root conditions* — fold them into the product
  (fine, still finite), but confirm no circularity (the candidates depend on `q`,
  whose choice depends on the candidates' polynomials).
- **(b) Does the nested IH hand us `G_v`'s rank polynomial to multiply in?** Need to
  invoke the device producer on `G_v` from its nested-IH rigid seed; `exists_rankPolynomial_of_rigidOn`
  builds the polynomial from a rigid seed, so this should compose — confirm the
  nested IH delivers a rigid seed for `G_v` in usable form.
- **(c) General `d` may force alg-independence back (see §3).** As `d` grows
  (Lemma 6.13, the length-`d` chain `v₀…v_d`, Phase 23), the family of subgraphs the
  argument touches may grow with `d`. If it is unbounded *uniformly in `d`*, "finite
  product" no longer closes a single statement and KT's algebraic-independence hammer
  (or a uniform-genericity argument) is genuinely needed. The product-route may be a
  **`d=3`-only** relaxation that Phase 23 pays back.

**To investigate (the relaxation phase):** a focused recon/spike confirming (a)+(b)
at `d=3`, then — if green — refactor the Claim-6.11 kernel to the product-route and
*delete* the `non-root-from-alg-independence` content. Decide separately whether the
general-`d` use (§3) can also be product-routed or genuinely needs alg-independence.

## 3. Usage tracker — where the program relies on algebraic independence

**Standing instruction (per the user, 2026-06-06): append a row whenever a new
algebraic-independence use is introduced into the molecular program.** "Relaxable?" =
does the §2 product-route (or another weakening) plausibly apply.

**Scan finding (2026-06-06).** A scan of the molecular Lean + blueprint for
algebraic-independence sites found: **the formalization has avoided algebraic
independence entirely so far** (grep: *zero* `AlgebraicIndependent`/transcendence
usage tree-wide). KT's inductive realization is "generic nonparallel" = algebraically
independent over ℚ, and KT leans on it pervasively — notably **Claim 6.4/6.9** (the
genericity device, Phases 21b/22a/22b), where KT justifies the rank-transport *via*
algebraic independence (see the `CaseI.lean:483`/`:1399` docstrings). **Yet the
project discharged the device and Claim 6.4 *without* it** — using the existence /
Zariski-genericity device (∃ a non-root of a nonzero polynomial) + general position
(`IsGeneralPosition`, pairwise-normal transversality). So those are *not* current
sites; they are the **precedent** that the existence formulation suffices. The
**Phase-22d kernel is the FIRST place the existence formulation falls short** —
footnote 6 needs "*this* given seed attains the rank", not "*∃* a good seed" — which
is exactly why algebraic independence becomes necessary there (absent the §2
relaxation). This track record makes the product-route relaxation a *continuation of
a proven strategy*, not a gamble.

| Where | What alg-independence is (would be) used for | Status | Relaxable? |
|---|---|---|---|
| Genericity device / **Claim 6.4/6.9** (Phases 21b, 22a, 22b) | KT transports rank across the collapse/generic step via alg-independence | **AVOIDED** — formalized via the existence/Zariski device + GP; green. *Not a site — the precedent.* | already avoided |
| **Phase 22d kernel** — KT Claim 6.11, eq. (6.22)/(6.18), footnote 6 (`lem:case-III-seed-rank-bridge`) | the inductively-fixed seed `q` attains the IH/matroid-predicted rank of nested subgraphs (`G_v^{ab}`, `G_v`) — so a redundant `ab`-row exists | **first forced site; being built** via the alg-independence route — leaf (i) `AlgebraicIndependent.aeval_ne_zero` ✓ landed (mirror; the `aeval` form, not the misnamed `eval`); (ii) seed-alg-indep invariant + (iii) the kernel bridge next | **candidate: §2 product-route** (~70% at `d=3`) — finitely many subgraphs, `q` chosen at composition |
| **Phase 23** — KT Lemma 6.13, general `d` (the length-`d` chain) | same footnote-6 transfer along the chain `v₀…v_d` | future (planned) | **uncertain** — family may grow with `d` (§2 risk (c)); product-route may not suffice |

(KT makes algebraic independence a single *global* inductive-seed choice, so the
forced sites are really one underlying need — "this seed attains the rank" —
surfacing at each point the *existence* device cannot reach; the table tracks those
surfacings the formalization must discharge, plus the avoided precedents.)

## 4. Status / how to use

- The alg-independence route is the **chosen path to green** (2026-06-06); this note
  does **not** block it.
- The Phase-22d kernel sub-phase builds (i)+(ii)+(iii) directly. Leaf (i)
  (`AlgebraicIndependent.aeval_ne_zero`, mirror) landed 2026-06-06; (ii)+(iii) next
  (`notes/Phase22d.md` *Hand-off* + *Lemma checklist*).
- The **relaxation phase** (deferred, unlettered — minted when its turn comes) takes
  §2 as its starting hypothesis and §3 as its checklist of sites to revisit.
- Keep §3 current: any new "this seed attains the rank" use is a new row.

Cross-refs: `notes/Phase22d.md` (*Footnote-6 kernel recon*, *Kernel-route decision*);
`notes/Phase22-realization-design.md` §1.30–§1.31; KT §6.4.1 (eq. (6.22), footnote 6),
§6.4.2 (Lemma 6.13).
