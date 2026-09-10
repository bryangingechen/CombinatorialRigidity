# PENCIL — informal mathematics workbook (kernel-(K) arc)

**One section per file.** This workbook was a single 41 343-line file until
2026-09-09, when `notes/Harness-structure.md` slice 12 split it section for
section, with **no change to any section's text**. **The file path is now the
durable anchor**: the hand-maintained line-range index this file used to
carry had drifted on **19 of its 20 rows** (+10 to +493 lines), which a path
cannot do.

**To find a claim, ask the ledger rather than grepping:**
`python3 notes/ledger.py --label '(BE-216)'` — also `--brief L1 L2 ...`,
`--frontier`, `--cited-by`, `--status PROVED`, `--delta <ref>`. It indexes
every claim in the corpus and reports the status the claim's own prose
states. It is an INDEX: the owning section stays authoritative for what a
claim means.

**Nine `##` headings are not sections** — six `TERMINATION check (E1/E2/E3)`
plus `Riders`, `Shelf effect` and `Secondary deliverable` are sub-parts of
the direction write-up they sit inside, so the split kept them with their
parent section rather than orphaning them into files of their own.

**Scope.** This workbook carries the **live kernel-(K) arc**: the escape
uniformity kernel `hK` and its descendants, plus the (K-bare) stub. The
**W4 (`hcontract`) residual arc** — `hnoGood'` vacuity, (SAFE-RES)/(SAFE-RES′),
and the routes-1/3 kernel widening ((K-res), (E)/(E-loc)/(T)/(V)) — was split
out to **`notes/pencil/workbook/W4.md`** on 2026-08-05: all three of its
sections are closed as arguments and W4 itself is parked by the route-3(b)
adjudication, but they stay at full detail there as the eventual W4 build's
input. The *Shared dictionary* (`dictionary.md`) and *State of (K)* map (`gapmap.md`) in this directory serve both files.

**Purpose.** Informal proofs under development for the kernels and branch
arms Phase 39 (PENCIL) carries as hypotheses. This is the **staging ground
before blueprint transcription**: nothing here is formalization-committed, no
`\lean{...}` pin points at it, and a section may be rewritten wholesale when
the argument changes. Once a section reaches *proven-informally* and the
coordinator commissions its build, its content moves to
`blueprint/src/chapter/pencil.tex` (with a `notes/BlueprintExposition.md`
entry when it earns a detailed exposition) and the section here shrinks to a
pointer.

**Discipline.**

- Each section reads as the **current state of the argument**, revised in
  place. Git is the changelog; do not keep superseded reasoning inline (the
  `notes/CLAUDE.md` rule for phase notes applies here too).
- Each section carries an explicit **confidence verdict**, one of:
  *proven-informally* / *true-modulo-named-gap* / *open* / *refuted*, plus a
  **"what would change this"** line naming the observation that would move
  the verdict.
- Landed Lean facts are cited by declaration name; claims that are *not*
  landed are flagged as such at the point of use. `PencilNondegFeasible` has
  no combinatorial characterization — whenever an argument needs a
  feasibility fact, say whether it is landed-**sufficient**
  (`hcard ∧ triangle-free`, L6b; the spanning-`C₃` witness, L7c-3),
  landed-**necessary** (`hcard`; no-2-hub-triangle), or **middle zone**
  (undecided by landed lemmas).

- **Labels are registered, not invented.** Before minting any label, read
  `notes/pencil/labels.md` and follow its four-clause rule: grep the registry
  for the token, never write a bare parenthesized token for a *Step*, qualify
  every cross-section citation with its owner (`§(K-slide-comb) (C6)`), and do
  not rename existing labels. Add your row in the same commit that mints the
  label. That file also carries the reserved namespaces for in-flight parallel
  dispatches.

**Recon verdict history lives elsewhere.** The dated recon record — what was
asked, what method was used, what was refuted — is
`notes/Phase39-design.md`; the one-line decisions are `notes/Phase39.md`
*Decisions made*. This file carries only the mathematics, in its current
state.

## Section index — navigation

**Navigation only.** `gapmap.md` is and remains the single mathematical entry
point; this table says which file owns which section. The *file* column
replaced a *lines* column at the 2026-09-09 split, for the reason above. The
*tag* column is the section's prefix for **new** labels
(`notes/pencil/labels.md` clause L1); statuses are one-word pointers to the
section's own verdict block and the gap-map row, which stay authoritative.

**The 36 `§(K-bare-ext)` direction continuations are one file each under
`bare-ext/`**, named by direction code, alongside the base `K-bare-ext.md`.
They are not listed individually — `python3 notes/ledger.py --label` resolves
any of their claims to its file.

| § | file | status (owner: the section's verdict block) | tag |
|---|---|---|---|
| *Shared dictionary* + test shapes `W19`/`S29` | `dictionary.md` | serves **both** workbooks | `SD-` |
| ***State of (K)* — the gap map** | `gapmap.md` | **the entry point; a pass updates it in place** | — |
| §(K-tight) | `K-tight.md` | criterion proven-informally; **(K-tight) open — the phase's hardest item** | `KT-` |
| §(K-pitch) | `K-pitch.md` | (T1)–(T5) proven-informally; closed at `ℓ = 3`; uniform form open | `PT-` |
| §(K-slide) | `K-slide.md` | (S1) proven-informally; settled per member | `SL-` |
| §(K-slide-cl) | `K-slide-cl.md` | reduction proven; **refuted as stated**; the `∃Σ` form open | `SC-` |
| §(K-slide-comb) | `K-slide-comb.md` | **refuted as a class statement**; (C6)/(C7) proven-informally | `SB-` |
| §(K-flank) | `K-flank.md` | per shape, not a uniform gap; half 2 proven-informally | `FL-` |
| §(K-pure) | `K-pure.md` | direction C **refuted**; (PC-Z)/(PC-OBS) proven-informally; **(K-chord)** the successor | `PC-` |
| §(K-Λ) | `K-Λ.md` | **refuted as an independent gap**; (Λ1) an identity; **(OUT)** lives here; item (vii) **REALIZED**, floor-classified | `Λ` |
| §(K-dom) | `K-dom.md` | dominance holds at every probed habitat; **C1 not a route**; (D2) gains its mechanism from §(K-ann); since *Steps D8–D14* (direction DSAT) **C2's satisfiability trace is run — UNSAT off the class, SAT on it** | `DM-` |
| §(K-σ) | `K-σ.md` | **route σ a CANDIDATE** — the one live candidate; its *Field scope* is settled by §(K-clos), and two of its refutations reverse there | `σ` |
| §(K-clos) | `K-clos.md` | the field question **settled** ((AC-1)/(AC-7)); **(AC-6) refuted as a class statement**, open only on the tight stratum | `AC-` |
| §(K-ann) | `K-ann.md` | the **recipe** ((ANH-2)/(ANH-3)) and (ANH-1)/(ANH-4) proven; the residue is **(ANH-R1)**, relocation #4 — since Steps A10–A13 (direction R) **one-point-decidable per shape, discharged at every probed triple, pointwise REFUTED** ((ANH-12)); since Steps A14–A17 (direction Q) the M2 "upgrade" is **struck as redundant** ((ANH-16)), the bare-cycle stratum is governed by **one universal irreducible degree-12 polynomial** ((ANH-14)), and the residue is **chart-to-frame dominance, no rank condition left** | `ANH-` |
| §(K-out) | `K-out.md` | (OUT)'s hypothesis **measured**: **(OC-3)** proves it is never automatic (no counting route); availability pointwise; **(OC-7)** a harness defect, its necessity clause **refuted** ((OC-14)); since Steps O9–O12 (direction O) the combinatorial half is **proven** ((OC-10), items 1–2 struck) and residue **(OC-8)** is a **containment** question — at degree-3 hubs the bad locus is the explicit panel line `C₀`; since Steps O13–O18 (direction OCON) **(OC-8) reshaped**: the hard-stratum qualifier is free ((OC-17)); since Steps O19–O24 (direction ZNEQ) chart irreducibility (CIRR) discharges input (b), and (OC-19) input (a) `Z ≠ ∅` itself **factors**: a necessary-for-`hK` half **dominated** by §(K-grid) (GR-10), and a target-rank half whose failure is a codimension-2 Schubert jump, measured 138/138 witnesses — **OPEN as a class-uniform statement, NOT an independent gap**; since Steps O37–O41 (direction OQRANK) the (a₁) grid route is settled graded — mechanism completed, naive form refuted at 27/174 (the (OC-42) WALL + a second confinement), hunted form GREEN: input (a) at 174/174 classes per-class-generic, zero (K-tight)-event rulings | `OC-` |
| §(K-ind) | `K-ind.md` | **refuted as a route** | `IN-` |
| §(K-Δ) | `K-Δ.md` | **NO HIT — the lead is discharged** | `DL-` |
| §(K-bare-ext) | `K-bare-ext.md` | **the `∀`-seed form REFUTED (tier T1, exact + cap-free); `hbareSplit` untouched**; the §(K-tight) calculus **transports** (192/192) and its `def = 0` scope is measured; the dependent stratum **complete** at `corank(G′) ≤ 3` | `BE-` |
| §(K-ins) | 13854–14329 | **new, 2026-09-08, direction BINSERT — option B for `hbareSplit`, the insertion calculus, is SPENT**: its chain has no un-run link (link 1 landed 2026-08-02, link 2 **is** (BE-2)) and **BOTH KT-inherited routes are REFUTED at `corank(G′) = 3`** — route A by KBARE-FALSIFY, **route B here** ((INS-3), cap-free at the same 8 seeds, route B being route A at the chain's other end on the `ρ`-pullback, (INS-1)/(INS-2)); mechanism a **chain-end panel collapse** ((INS-4), `dim 3`/rank 1 at 8/8 hits vs `dim 5`/rank 4 at 19/19 controls), permitted **structurally** by `¬ PencilNondegFeasible` ((INS-8)); refutation **confined to `index = 2`** ((INS-5)). **Since Steps INS8–INS15 (direction INSJOINT, ordinal 90) the last endpoint is EXCLUDED**: the joint sweep's own two-vertex-deleted `U′` obeys `need′ − need = dim U′ − dim U` against `U ⊆ U′`, so the deficit is **preserved** and `rank⟨U′, Λ²Π̂⟩ = 2 < 3 = need′` at 8/8 ((INS-9)–(INS-12)) — **option B is SPENT OUTRIGHT**, link 2 **not** re-opened ((INS-16)), and the recorded `≥ 2` threshold was route A's `need` ((INS-15)). `hbareSplit` **UNTOUCHED**, tier T1 throughout | `INS-` |
| §(K-grid) | `notes/pencil/workbook/grid.md` | **reduction proven** — (AC-6)'s tight-stratum residual reduces via a long chain of proven results on `G°` to the single open gap **(GR-15)**; the min-max form, the uniform `g ≤ 1` cap, the bounded-deviation selection form and the growth law's bounded-shift-correction reading are all refuted; (b′)'s `n`-free constant `≤ 12` is a **THEOREM** ((GR-89); its clause (GR-R1) proven by GFLIP's selection theorem (GR-99), Steps G116–G119) and **the constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum** (Steps G120–G124, direction GCHEAP: (GR-C2)'s every-step form PROVEN for `n < 6|δ|` via the lone-dart capacity (GR-100)/(GR-101), its per-configuration form REFUTED from `n_hub = 12` by an explicit witness (GR-103), the boundary exact both ways; residual now **(GR-104)(i)**, the price form — since Steps G125–G129 (direction GPRICE) a **theorem at `2k = 2`, every `n`, modulo the minted balance law (GR-108) alone**, via the reversal-set normal form (GR-106) and the reachability theorem (GR-107); (GR-108) measured 1 431/1 431 with the `n ≤ 6` sub-cell exhaustive, the refutation hunt EMPTY to `n = 18` under disclosed caps, the residual (GR-108) + the `2k ∈ {4, 6}` `O ⊄ M` corner; since Steps G130–G134 (direction GBLAW) the exchange calculus (GR-108)'s pinned proof shape calls for is **PROVEN** ((GR-110)–(GR-112): arc-transversal normal form, recombination connectivity, the escape lemma — no fine move crosses the balance layer, so **(GR-108) ⟸ existential escape**, measured 0 failures at 1 099 swept pairs), universal escape REFUTED at an explicit `n = 16` witness that defeats both new mechanisms; at *Steps G135–G148* **(GR-108) is FALSE from `n = 12` and (GR-104)(i) at `2k = 2` is FALSE** ((GR-122)/(GR-123)) — but **the ledger consumes neither**: its (b′) term is a **difference of minima** ((GR-127)), the `min_M` reading is PROVEN ((GR-126)), and the live successor is the new statement *is the ledger gap ever `≥ 3`?*) (the necklace family, (GR-43), proves the shift-metric layer unbounded) while the `d_fg = d_adm` law is verified EXHAUSTIVELY on the whole `n_hub ≤ 6` habitat stratum ((GR-58)), its stronger per-matching variant REFUTED ((GR-59)); the parity layer is exactly `d_par(M) = w_M` with the Hall/SDR step automatic ((GR-44)), and **route-ledger entry 5 is PROVEN in both halves ((GR-49)–(GR-54)): balance existence is a degree-constrained-orientation theorem, discharging the named input (X)** — the (GR-45)–(GR-48) move-calculus apparatus is subsumed, not contradicted; since Steps G80–G85 (direction YLOC) **input (Y)'s pinned GBAL-localization route is DEMOTED BY WITNESS** — full goodness is not a function of the degree data at a proper chunk ((GR-62)), the coordinator's predicted break point REFUTED as stated and located two links earlier ((GR-63)) — leaving a colouring-free collision bound on `d_fg` ((GR-64)) and a coordinate-free fit identity ((GR-65)) as the positive residue; input (Y) stays OPEN, **E3 (ARMED by GBAL) does not fire**; since Steps G86–G91 (direction BALB) **(b′)'s PRICE half is PROVEN outright ((GR-68)) and its imbalance ceiling is a THEOREM at `n_hub ≤ 6`, FALSE from `n_hub = 8` at an exact boundary ((GR-69))** — its availability half reduces to one clause (GR-70), exhaustive on the stratum's landed T1 instance but REFUTED there from `n_hub = 8`, repaired at price 0 by a named successor; **(b′) stays OPEN, NOT a HIT**; no flank found; class uniformity untouched | `GR-` |
| §(K-res) | `notes/pencil/workbook/grid.md` (end of file) | **new, 2026-08-28, direction RESGRID — the residual-habitat transport audit**: the §(K-grid) geometry transports verbatim ((RS-1)–(RS-4)), the (K-res) grid residual is **(RS-5)** ((GR-15)'s criterion, quantifier widened past the tight class), **proven per-shape** at `W19`/`S29`/`NT21c3`; the tight bookkeeping ((GR-16)(iv)/(GR-17)(d)/(GR-18)(i), then (GR-21)/(GR-22)/(GR-25)/(GR-32) and the `D = 0` program) does **not** transport; the deficient fringe is **refuted with a mechanism** ((RS-6), θ(2,3,7)) | `RS-` |
| §(K-frame) | `K-frame.md` | residue **(FR-R1) PROVEN** since Steps FR7–FR11 (direction PEX); the bare-cycle stratum is finite (22 iso classes / 76 sites / 1976 labelled) and exhaustively enumerated; since Steps FR12–FR15 (direction FRES) **(FR-4)'s named gap is CLOSED** — the discharge is unconditional on the whole bare-cycle stratum ((FR-17)) | `FR-` |
| §(K-chart) | `K-chart.md` | **new, 2026-08-19, direction CIRR — a HIT.** The pencil chart of `G′` is a proven, irreducible, ℚ-rational variety (a tower of affine-linear fibres), the constant-fibre-dimension clause identified as `IsNondegPencilRealization` conjunct 3, and all four consumers (§(K-out) (OC-19), §(K-slide) (S1)(e), §(K-dom) (D4), §(K-ann) (ANH-9)(ii)) audited clean; one correction to §(K-frame) *Step FR13*'s hypothesis list (girth ≥ 4, not ≥ 3, for nonemptiness) | `CH-` |
| §(K-mech) | `K-mech.md` | **both §(K-pure) *P8* anomalies mechanised** in one calculus (the load space `Ω`); **6v11e RESCUED** ((MX-7)) — the slide device closes it after all; the σ rider settled NO ((MX-8)); the `\|V°\| ≤ 6` predictor measured complete-and-sound ((MX-9)) | `MX-` |
