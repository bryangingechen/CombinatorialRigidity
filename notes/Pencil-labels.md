# PENCIL — label registry and minting rule

**What this is.** The single index of every **label token** in use across the
Phase-39 (PENCIL) doc set, plus the rule that governs minting new ones. It is
an *index*, not mathematics: every row points at the section that owns the
label, and **that section (and the workbook's *State of (K)* map) is
authoritative for what the label means and what its status is**. Nothing here
states a verdict; the status column is a one-word pointer.

**Who reads it.** Anyone about to *mint* a label (mandatory — see the rule
below) and anyone unsure what a bare `(C6)`-style token refers to.

**Files in scope.** `notes/Pencil-informal.md` (the (K) workbook),
`notes/Pencil-W4-informal.md` (the W4 residual workbook),
`notes/Pencil-strategy.md`, `notes/Pencil-fanout.md`, `notes/Phase39.md`,
`notes/Phase39-design.md`.

## Why this file exists — the measured diagnosis

Six recorded confusion incidents motivated the 2026-08-05 reorganization pass.
Sorting them by cause:

- **Naming (3):** the (C6)/(C7) collision that needed coordinator fixup
  `86d77894`; the hand-written disambiguation `notes/Phase39.md` still carries
  for §(SAFE-RES)'s (C7)/(C8) vs §(K-slide-comb)'s same-numbered labels; and
  the 2026-08-05 broad recon picking `U1`–`U3` *specifically to dodge* the
  workbook's `(C6)`/`(C7)`.
- **Canonical home (3):** dispatch-log F12's claim propagating to eleven
  places; (OUT) landing in the strategy doc instead of the workbook (moved in
  `390a1a1f`); the route-σ arc written out three times in the phase note
  (collapsed in `9d6ab712`).

**None of the six was caused by file length.** This matters for how the set is
organized: length is a *context-budget* problem (addressed by the navigation
indexes in the workbook and the design doc), and it is a different problem from
the one that produced the incidents.

**The refined diagnosis.** The working hypothesis going in was *"sections mint
labels independently, so cross-section collisions are structurally
inevitable."* That is half right, and the half it gets wrong changes the fix:

1. **Independent minting is not sufficient to cause a collision.** Three label
   families are minted independently and have **never** collided across the
   7,438 lines of the two workbooks: `Λ0a`–`Λ0i`/`Λ1`/`Λ2`/`Λ3` (§(K-Λ)),
   `σ1`–`σ7` (§(K-σ)), `PC1`/`PC2`/`PC3`/`PC5`/`PC6`/`PC-Z`/`PC-OBS`
   (§(K-pure)) — together with the `K-…` gap names and `OUT`/`SAFE-RES`. What
   they have in common is a **topic tag inside the token**.
2. **Every bare single-letter family has collided.** `C`, `D`, `M`, `N`, `P`,
   `R`, `T`, `W`, `F` — see the collision table below. The token carries no
   owner, so the reader cannot resolve it and the next author cannot see that
   the letter is taken.
3. **A file boundary does not help.** The (C6)/(C7) incident was *already* a
   cross-**file** collision: §(SAFE-RES)'s (C7)/(C8) live in
   `Pencil-W4-informal.md`, §(K-slide-comb)'s (C6)/(C7) in
   `Pencil-informal.md`, and the strategy doc's C1/C2/C3 in a third file.
   Splitting the W4 arc into its own file on 2026-08-05 did not prevent the
   collision — it is why the phase note needs a hand-written disambiguation.
   **The namespace has to be in the citation token, because the filesystem is
   invisible at the point of reference.**
4. **A third failure mode, not previously named: step numbers and claim labels
   share one namespace.** §(K-slide-cl) writes `(C2)` for *Step C2* and `(C1)`
   for a claim stated in Step C1; §(K-dom) has Steps D0–D7 *and* claims
   (D1)–(D4); §(K-pure) has Steps P0–P9 while §(K-Λ) mints driver blocks
   (P1)–(P7); §(K-σ) has both a Step σ5 and a claim (σ5). Even a
   well-prefixed section is ambiguous to itself here.

So the fix is a **token-level namespace plus a consulted registry**, not a
physical reorganization.

## The minting rule

Four clauses. They are cheap; clause 1 is the one that actually prevents the
next collision.

- **(L1) Uniqueness, checked against this file.** Before minting a label, grep
  this registry for the token. If it is taken, **prefix it with your section's
  tag** (the *tag* column below) — e.g. a new claim in §(K-dom) becomes
  `(DM-5)`, not `(D5)`. Add the row **in the same commit that mints the
  label**. A label that is not in this registry does not exist.
- **(L2) Never label a step.** Steps are cited with the word *Step* —
  *Step 3a*, *Step σ5*, *Step D2* — and are **never** written as a bare
  parenthesized token. `(D2)` always means the claim; *Step D2* always means
  the step. This retires failure mode 4 without renaming anything.
- **(L3) Cross-section citations are qualified.** Inside its owning section a
  label may be written bare. **Anywhere else** — another section, another file,
  `Phase39.md`, a commit message, a dispatch prompt — write the owner:
  `§(K-slide-comb) (C6)`, `§(SAFE-RES) (C7)`, `strategy §4 C1`. This is the
  only clause that applies to the *existing* corpus.
- **(L4) Grandfathering — do not rename.** Every label below predates this
  file and carries up to ~40 cross-references; renaming would churn far more
  than it buys, and this pass renamed **nothing**. Collisions among existing
  labels are resolved by (L3), not by renumbering.
- **(L5) Direction codes are topic-tagged and multi-letter** *(user call,
  2026-08-07; binds from the fifth fan-out on)*. A fan-out direction is named
  by a short mnemonic token — `PEX`, `TCOL` — never by a bare single letter,
  and the token is verified **0-hit as a raw substring** (not merely as a
  whole token) across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` before it is
  reserved. Two measurements forced this. *(a)* Four fan-outs plus the
  harness round consumed A/B/C (×2), S1–S4, T/R/M, G/Q/O and E/J; of the
  fourteen unused single letters exactly **two** were 0-hit across the pencil
  doc set, so the pool was one fan-out from exhaustion. *(b)* Bare
  single-letter direction codes have already produced two recorded hazards —
  `(E)` doubling as §(SAFE-RES)'s gap token, and the A/B/C date-ambiguity
  below — which is this file's own measured diagnosis (bare single-letter
  families collide; topic-tagged ones have not) firing on the direction
  letters themselves. The substring half of the check is not pedantry: the
  third fan-out already had to replace an `m2` driver name whose token was a
  substring of existing prose, and `PAT` was rejected here for the same
  reason (46 substring hits inside "path" / "pattern" / "compatible").
  **The single-letter era is grandfathered under (L4)** — nothing is
  renamed, and every one of those letters stays dated wherever it is
  written, per the hazard note at the end of this section.

## Reserved namespaces — the three incoming parallel dispatches

Reserved 2026-08-05 for the three-way fan-out of `notes/Pencil-fanout.md`, so
that three concurrent read-only passes cannot collide with each other or with
anything above. Each prefix was verified **0-hit** across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` at reservation time, as was each section name.

**All three directions have LANDED** (2026-08-06) and that reservation table is
released: `AC-`/`§(K-clos)` (C), `ANH-`/`§(K-ann)` (A) and `OC-`/`§(K-out)`
(B, the (viii) measurement plus (OUT)'s combinatorial half) are live entries of
the registry below, not reservations. A reservation is released by **moving** its
row into the registry in the landing commit — never by deleting it — which is
what each of the three landing commits did. The mechanics below stay because
they bind the *next* parallel dispatch, not because one is in flight.

**Reserved 2026-08-06 for the SECOND fan-out — directions T / R / M**
(`notes/Pencil-fanout.md` §"Second fan-out"; letters chosen precisely to avoid
the A/B/C date-ambiguity below). Each token verified **0-hit** across `*.md`,
`*.tex`, `*.lean`, `*.py`, `*.m2` at reservation time. T and R *extend* live
sections, so their reservations are the unclaimed tails of those sections'
existing families — the owning section stays authoritative. **All three directions
LANDED** (2026-08-06) and the reservation table is released, each row moved into
the registry below: `GR-`/§(K-grid) (T — minted nothing in §(K-clos), so
(AC-10)+/Z9+ return to that section's unclaimed tail), `MX-`/§(K-mech) (M —
minted nothing in §(K-pure), as required), and (ANH-9)–(ANH-12)/Steps A10–A13
(R — landed as a §(K-ann) continuation; §(K-rig) was never opened and `RG-` was
never minted, so both return to the pool).

**Reserved 2026-08-06 for the THIRD fan-out — directions G / Q / O**
(`notes/Pencil-fanout.md` §"Third fan-out"; letters dated — A/B/C and T/R/M
are taken above; G/Q/O chosen off the collision table's bare-token rows).
Each token verified **0-hit** across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` at reservation time (`outerwide.m2` replaced a first candidate whose
token was a substring of existing prose). All three directions *extend* live
sections, so the reservations are the unclaimed tails of the owning families
— the owning section stays authoritative. Dispatch is **serial** (O → Q → G,
a user adjudication), which does not relax the reservation discipline:

**All three directions have LANDED** (2026-08-06) and the reservation table
is released, each row moved into the registry below: O as (OC-10)–(OC-16),
Steps O9–O12, `outerwide.py` + `outerwide.m2` (§(K-out)'s row); Q as
(ANH-13)–(ANH-16), Steps A14–A17, `anhr1.py` + `anhr1.m2`'s
(ANH-Q0)–(ANH-Q4) (§(K-ann)'s row); G as (GR-7)–(GR-11) + (GR-4′),
Steps G8–G13, `gridwit.py` (§(K-grid)'s row — `gridwit.m2` was never needed
and **§(K-pack)** / `PK-` return to the pool unopened).

**Reserved 2026-08-06 for the FOURTH fan-out — directions E / J**
(`notes/Pencil-fanout.md` §"Fourth fan-out"; letters dated — A/B/C (×2),
S1–S4, T/R/M and G/Q/O are taken above; E/J chosen off the collision
table's bare-token rows). One recorded hazard, not a rename (L4): **(E)**
bare remains §(SAFE-RES)'s gap token in the W4 workbook — the direction is
always written *direction E*, dated where ambiguity is possible. Each
reserved token below verified **0-hit** across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` at reservation time, except §(K-pack)/`PK-`, which is
**re-reserved from the pool** (returned unopened by direction G), and the
`GR-`/`G`-step tails, which are the unclaimed tails of §(K-grid)'s live
families — the owning section stays authoritative. Dispatch is **serial**
(E → J), which does not relax the reservation discipline:

**Both directions have LANDED and the reservation table is released**, each
row moved into the registry below: E (2026-08-07) as (GR-12)–(GR-15), Steps
G14–G18, `packmm.py` (§(K-grid)'s row — `packmm.m2` was never needed and
**§(K-pack)** / `PK-` return to the pool unopened, for the second time);
J (2026-08-07) as the new section **§(K-frame)**, tag `FR-` — (FR-1)–(FR-7),
(FR-R1), Steps FR0–FR6, M2 blocks (FR-M0)–(FR-M3), `framedom.py` +
`framedom.m2` (its `m2` leaf WAS needed, unlike E's).

**Reserved 2026-08-07 for the FIFTH fan-out — directions PEX / TCOL**
(`notes/Pencil-fanout.md` §"Fifth fan-out"). **The first fan-out under (L5)**:
the codes are topic-tagged mnemonics (`PEX` = pattern-existence, `TCOL` =
tight-stratum colouring), not letters, and each was verified **0-hit as a raw
substring** across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation
time — as were both driver names. Both directions *extend* live sections, so
their label reservations are the unclaimed tails of those sections' existing
families and the owning section stays authoritative. Dispatch is **serial**
(PEX → TCOL), which does not relax the reservation discipline:

**Both directions have LANDED and the reservation table is released**, each
row moved into the registry below: PEX (2026-08-07) as (FR-8)–(FR-14), Steps
FR7–FR11, `w4/patexist.py` (§(K-frame)'s row — `m2/patexist.m2` was never
needed and **§(K-pat)** / `PAT-` return to the pool unopened); TCOL
(2026-08-07) as (GR-16)–(GR-20), Steps G19–G23, `w4/gridcol.py` (§(K-grid)'s
row — `m2/gridcol.m2` was never needed and **§(K-pack)** / `PK-` return to
the pool unopened, for the **fourth** time — returned unopened by directions
G, E and now TCOL).

`PAT-` as a *label prefix* is 0-hit and reserved; the bare word `PAT` was
rejected as a **direction code** under (L5)'s substring check, which is a
distinct test from a prefixed label's — recorded so the two are not confused.

**One naming hazard the second fan-out created, recorded rather than renamed
(L4).** The **direction letters A/B/C are re-used** between the 2026-08-05 fan-out
(A = §(K-flank), B = §(K-Λ), C = §(K-pure)) and the 2026-08-06 one
(A = §(K-ann), B = §(K-out), C = §(K-clos)) — so "direction B" is ambiguous
across the corpus and **must be dated wherever it is written**. The *section*
names never collide, which is why they, not the letters, are the durable
reference.

One thing direction A's landing exercised, worth recording because it is the
first time a *reserved* dispatch hit clause L1 from the inside: the draft minted
bare `(R1)`/`(R2)` for its two residual inputs — a **three-way** collision (the
*Shared dictionary*, the opening recon questions, and `Pencil-strategy.md`
§4.6's six refutations), which the reserved prefix does not by itself prevent
because the draft reached for a bare letter. They landed as **(ANH-R1)** /
**(ANH-R2)**, the "append a letter" form sanctioned below, and the promoted
*Shared dictionary* fact landed as **(SD-6)** rather than `(R6)` for the same
reason. **A reserved prefix protects a dispatch from its siblings, not from the
existing corpus; clause L1 still binds inside a reservation.**

Binding on a reserved dispatch: **use your prefix for every label you mint**, including
sub-claims and driver blocks; cite everything you did not mint in the qualified
form (L3); and if you open a section, use the reserved name so the coordinator
can land three returns serially without a rename. A dispatch that needs a
second prefix (e.g. a driver-block family distinct from its claims) appends a
letter — `ANH-M1`, `ANH-M2` — rather than reaching for a bare letter.

Existing gap names, statuses and section verdicts are **not** in a reserved
dispatch's namespace: moving a status is a coordinator action, per the fan-out
landing checklist.

## Registry — `notes/Pencil-informal.md` (the (K) workbook)

Status keywords are pointers to the owning section's verdict block and the
*State of (K)* map, which remain authoritative.

| owning section | tag | labels in use | what the family is | status (see owner) |
|---|---|---|---|---|
| *Shared dictionary* | `SD-` | (R1)–(R5) *(grandfathered)*; **(SD-6)** | elementary rigid-graph facts used by **both** workbooks: min degree, size bound, short cycles, `hcard` restated, feasible triangles pendant, **branch length `≤ 5`** (= §(K-ann)'s (ANH-8), promoted here 2026-08-06; `SD-` because `(R6)` is taken by `Pencil-strategy.md` §4.6) | settled |
| §(K-tight) | `KT-` | (K-move) *(named here)*; Steps 0–5 | the carrier escape criterion, KT pp. 684–691 re-pin | criterion proven-informally; (K-tight) open |
| §(K-pitch) | `PT-` | (T1)–(T5); (K-wit), (K-pitch-∞) *(named here)*; Steps 0–6 | motion-side transfer, sign law, placement quartic, Λ-compression | (T1)–(T5) proven-informally; uniform form open |
| §(K-slide) | `SL-` | (S1)–(S5); **(W1)–(W4)**; (K-slide-cl) *(named here)*; Steps 1–5 | the slide-in transfer theorem; **(W1)–(W4) are the four conditions of the `ε = 0` limit line system** | (S1) proven-informally |
| §(K-slide-cl) | `SC-` | Steps C0–C5, and a claim **(C1)** stated in Step C1 | the tetrahedral collapse; (C1) = *rows independent ⟺ every class is a forest* | reduction proven; statement refuted as stated; `∃Σ` form open |
| §(K-slide-comb) | `SB-` | **(C6)**, **(C7)**, (C8); Steps D0–D5 | the combinatorial residue; (C6) = the packing half, (C7) = the repaired length-4 entry | (C6)/(C7) proven-informally; section refuted as a class statement |
| §(K-flank) | `FL-` | **(F1)**; Steps F0–F7 | adversarial rank test at the uncovered flanks | half 2 proven-informally per shape |
| §(K-pure) | `PC-` ✓ | (PC1), (PC2), (PC3), (PC5), (PC6), (PC-Z), (PC-OBS); (K-chord) *(named here)*; Steps P0–P9 | the pure condition of the limit carrier | (PC-Z)/(PC-OBS) proven-informally; direction C refuted |
| §(K-Λ) | `Λ` ✓ | (Λ0), (Λ0a)–(Λ0i), (Λ0′), (Λ0f′), (Λ1), (Λ2), (Λ3), **(OUT)**; **driver blocks (M1)–(M4)** (`lambda1.m2`) and **(P1)–(P7)** (`lambda0.m2`) | the Λ-compression's quadric; (OUT) = the outer-line criterion, *Step 5a* | (Λ1) an identity over the function field; (K-Λ) refuted as an independent gap |
| §(K-dom) | `DM-` | **(D1)**–(D4); Steps D0–D7 | the dominance spike, differential of `H ↦ V_bc` | (D1)–(D3) proven; C1 refuted as a route |
| §(K-σ) | `σ` ✓ | (σ1)–(σ7); Steps σ0–σ6, σ4b; hunt pools H4/H5 | the polarity as a symmetry of the split; **route σ** | (σ7) proven; route σ a CANDIDATE (its field scope settled by §(K-clos)) |
| §(K-clos) | `AC-` ✓ | (AC-1)–**(AC-9)**; Steps Z0–Z8; driver blocks AC-C0/AC-E/AC-S/AC-U/AC-X/AC-Q/AC-R2/AC-F/AC-2c/AC-P (`closure.py`) | the over-`ℂ̄` question: the polarity's field scope, the σ-fixed grid locus, the `⋆`-eigen decoupling, the route-σ collapse, the char-0 descent | (AC-6) **refuted** as a class statement, open on the tight stratum; the rest proven-informally. **(AC-9)** (minted 2026-08-06, re-baselining slice S2): every σ-fixed body of degree `≥ 3` carries a coincident hinge line — **proven** by pigeonhole against *Step Z3*'s two-ruling-lines cap, measured 0/64 by the composite guard; it **qualifies (AC-3)** without weakening it |
| §(K-ann) | `ANH-` ✓ | (ANH-1)–(ANH-8); the two residual inputs **(ANH-R1)**, **(ANH-R2)**; Steps A1–A9; driver modes `--stress`/`--rate`/`--supp`/`--recipe`/`--census`/`--validate` (`annih.py`); **since 2026-08-06 (direction R)** (ANH-9)–(ANH-12), Steps A10–A13, and driver modes `--census`/`--bad`/`--comb`/`--validate` (`shrink.py`); **since 2026-08-06 (direction Q)** (ANH-13)–(ANH-16), Steps A14–A17, driver modes `--types`/`--reduce`/`--size`/`--frame`/`--witness`/`--validate` (`anhr1.py`) and M2 blocks (ANH-Q0)–(ANH-Q4) (`anhr1.m2`) | the annihilator as a self-stress of the contracted framework `H/P`: the reciprocity identity, the named move, the `k = 4` Tay circuit, the one-bracket recipe. **(ANH-8) is promoted to the *Shared dictionary* as (SD-6)** — that is the only copy | (ANH-1)–(ANH-6), (ANH-8) proven / proven-informally; (ANH-7) true-modulo-named-gap; **(ANH-R1) open** |
| §(K-out) | `OC-` ✓ | (OC-1)–**(OC-16)**; Steps O1–O12; the **pools** POOL-C / POOL-G / POOL-S / POOL-B and (since direction O, 2026-08-06) POOL-CW / POOL-A / POOL-W / POOL-SL; driver modes `--comb`/`--pool`/`--shapes`/`--build` (`outerline.py`) and `--wide`/`--adv`/`--wrench`/`--slide` (`outerwide.py`) + `outerwide.m2` | (OUT)'s hypothesis measured: the exact hinge-rate reading, the ambient-generic map, the never-automatic negative, the constructed silent point, the two pool distributions, the sampler defect, and the residual | **(OC-3)** proven-informally and load-bearing; (OC-1) proven-informally; (OC-2)/(OC-5)/(OC-6)/(OC-7) measured; (OC-4) exhibited; **(OC-8) open**. **(OC-7) is a harness item**, `notes/scripts/README.md` *Harness debt* 4 — **CLEARED 2026-08-06** by the re-baselining round, whose slice S2 also minted **(OC-9)** here (the FIELD half of the coincident-hinge guard's adversarial test: the guard rejects 58/357 and its rejection set strictly contains the two-end diagnostic's 39) |
| §(K-ind) | `IN-` | (I0)–(I4); Steps I0–I6 | numerical invariant along the generating moves | refuted as a route; (I3) a positive by-product |
| §(K-Δ) | `DL-` | **(M1)**, **(M2)**, **(M3)**; (N1), (N2) | the Δ-matroid literature hunt: (M1)–(M3) are the **three hypothesis tests**, (N1)/(N2) the two readings bought | NO HIT; discharged |
| §(K-bare-ext) | `BE-` | (K-bare-ext) | the (K-bare) stub | open, nothing being developed |
| §(K-mech) | `MX-` ✓ | (MX-1)–(MX-9); driver modes `--flex`/`--wide`/`--inc`/`--sigma`/`--sweep` (`mech.py`) | the mechanisms of the residual (W2)/(W4) anomalies: the realizable-load space `Ω`, α-confinement, pole-cluster loads, the welded flex, the 6v11e rescue, the σ rider | (MX-1)/(MX-2) proven; (MX-3)–(MX-7) proven-informally; (MX-8) settled-NO in the probed family; (MX-9) measured |
| §(K-grid) | `GR-` ✓ | (GR-1)–(GR-6); Steps G0–G7; driver blocks GR-D1–GR-D5 (`grid.py`); **since 2026-08-06 (direction G)** (GR-7)–(GR-11) + the primed successor **(GR-4′)** (recorded under (GR-4) as its repaired form, per L4 no-renaming), Steps G8–G13, driver modes `--formula`/`--treetriple`/`--wide`/`--validate` (`gridwit.py`); **since 2026-08-07 (direction E)** (GR-12)–(GR-15), Steps G14–G18, driver modes `--restate`/`--hard`/`--sep`/`--exemplar`/`--validate` (`packmm.py`); **since 2026-08-07 (direction TCOL)** (GR-16)–(GR-20), Steps G19–G23, driver modes `--branch`/`--runs`/`--pack`/`--hier`/`--wide`/`--validate` (`w4/gridcol.py`; `m2/gridcol.m2` not needed) | the tight-stratum residual of (AC-6): eigen-blocks as conic direction networks / generalized-spline systems, the counting obstruction families ((GR-3); unified as **(GR-8)** sub-multigraph cycle spaces), chart-image membership, the 907-shape census, the interpolation factorization (GR-7), the tree-triple certificate theorem (GR-9), the merged residual (GR-10), the ε-adic fallback (GR-11), the branch-level reduction to the hub multigraph (GR-16), the circuit run law (GR-17), the 6-spanning-tree packing statement (GR-18), the collapse-order hierarchy (GR-19) | reduction proven; (GR-2) a proven refutation of the former (AC-6) close-route sentence; **(GR-4) refuted-as-stated, repaired as (GR-4′), off the critical path; (GR-9) proven; (GR-12)/(GR-13)/(GR-14) proven-informally — the (GR-10) min-max REFUTED as posed, (GR-10) itself open (exhaustively certified where swept); (GR-16)–(GR-19) proven — the branch reduction, circuit run law, 6-tree packing and collapse hierarchy — collapse order 4 measured at all 18 habitat separators; residual = (GR-15), OPEN, no flank found** |
| §(K-frame) | `FR-` ✓ | (FR-1)–(FR-7); the residual input **(FR-R1)**; Steps FR0–FR6; driver modes `--rulings`/`--pattern`/`--transport`/`--outer`/`--validate` (`framedom.py`) and M2 blocks (FR-M0)–(FR-M3) (`framedom.m2`); **since 2026-08-07 (direction PEX)** (FR-8)–(FR-14), Steps FR7–FR11, driver modes `--frame`/`--recipe`/`--strat`/`--kill`/`--validate`/`--recon` (`w4/patexist.py`; `m2/patexist.m2` not needed) | the shared chart-to-frame dominance residue of §(K-out) (OC-16) / §(K-ann) (ANH-14): the minimal non-containment lemma, the ruling decomposition and determinant law at grid points, the `G′`-regridding transport, the 1904-site pattern battery, the θ(3,4,5) constructed witnesses, and (since PEX) the bare-cycle stratum's finiteness + exhaustive enumeration | (FR-1)/(FR-2)/(FR-3) proven / proven-informally; (FR-4) true-modulo-named-gap; (FR-5) measured (each certificate a per-site proof); (FR-6) exact per point; **(FR-R1) PROVEN** (Steps FR7–FR11, direction PEX) — (FR-4)'s named gap is the sole rider |

Gap names used arc-wide and owned by the *State of (K)* map: **(K-tight)**,
(K-move), (K-pitch), (K-pitch-∞), (K-wit), (K-Λ), (K-slide), (K-slide-cl),
(K-slide-comb), (K-chord), (K-flank), (K-dom), (K-σ), **(K-clos)**, **(K-ann)**,
**(K-out)**, (K-ind), (K-Δ), (K-bare)/(K-bare-ext), and **(K-res)** (owned by the
W4 workbook, below). These are already tagged and collision-free; keep the `K-`
form for any new gap. ((K-clos) was landed 2026-08-06 with its registry row but
was missed from this sentence; added here with (K-ann) and (K-out).)

## Registry — `notes/Pencil-W4-informal.md` (the W4 residual workbook)

| owning section | tag | labels in use | what the family is |
|---|---|---|---|
| §`hnoGood'` vacuity | `NG-` | **(C1)–(C6)** | structure of a maximal cluster's contraction: (C1) simplicity is free, (C2) outside degrees preserved, (C3) boundary attachment points are hubs, (C4) `hcard` fails only at `v*`, (C5) no triangle through `v*`, (C6) the boundary-hub budget |
| §(SAFE-RES) | `SR-` | **(C7)**, **(C8)**; (SAFE-RES), (SAFE-RES′); **(E)**, **(T)**, **(V)** | (C7) every ear through `T` has ≥ 6 interior vertices; (C8) the dichotomy at a maximal cluster; (E)/(T)/(V) the three gaps of (SAFE-RES′) |
| §widened kernels (routes 1/3) | `WK-` | (E-loc); **(K-res)** | the routes-1/3 kernel widening; (K-res) is the widened kernel carried as a byte-identical sibling of `hK` |

## Registry — `notes/Pencil-strategy.md`, `Phase39.md`, `Phase39-design.md`

| owner | labels in use | what the family is |
|---|---|---|
| strategy §4 | **C1**, **C2**, **C3** | the three candidate stronger inductive invariants (C1 = dominance of the `V_bc` map, run and struck) |
| strategy §4.6 | **U1**, **U2**, **U3** | the three ranked live class-uniformity successors |
| `Phase39.md` / design doc | **R1**, **R2**, **R3** | the three **opening recon questions** (statement/satisfiability, truth sanity, which KT case breaks) |
| `Phase39.md` / design doc | W0–W5; L0–L7 (+ `L5-cut-*`, `L6a`–`L6d`, `L7a`–`L7c`) | the phase's **work packages** and their **leaves**; **W4 = `hcontract`** |
| `notes/scripts/w4/hybrid_gates.py` | **N8**, **N9**, **N10**, **N10b** | the W4 numeric gates |
| `notes/dispatch-log.md` | **F5**, **F6**, **F9**, **F11**, **F12**, … | coordinator dispatch-exception rows |

## Collision table — bare tokens that are ambiguous today

Resolve every one of these by (L3): write the owner. Listed because each is a
token a reader will meet bare in the existing corpus.

| bare token | meaning 1 | meaning 2 | meaning 3 |
|---|---|---|---|
| **(C1)–(C6)** | §(K-slide-cl) *Steps* C0–C5 (+ claim (C1)) | W4 §`hnoGood'` cluster claims (C1)–(C6) | strategy §4 candidate invariants C1/C2/C3 |
| **(C7)**, (C8) | §(K-slide-comb) (C7) — the length-4 menu repair | W4 §(SAFE-RES) (C7)/(C8) — ear length / cluster dichotomy | — |
| **(D1)–(D4)** | §(K-dom) claims | §(K-dom) *Steps* D0–D7 | §(K-slide-comb) *Steps* D0–D5 |
| **(M1)–(M4)** | §(K-Λ) `lambda1.m2` driver blocks | §(K-Δ) the three hypothesis tests | — |
| **(P1)–(P7)** | §(K-Λ) `lambda0.m2` driver blocks | §(K-pure) *Steps* P0–P9 | — |
| **(R1)–(R6)** | *Shared dictionary* rigid-graph facts (R1)–(R5) | R1/R2/R3 the opening recon questions | `Pencil-strategy.md` §4.6's six refutations (R1)–(R6) — **and (ANH-R1)/(ANH-R2)**, §(K-ann)'s two residual inputs, which are *prefixed precisely to stay out of this row* |
| **(T)** | §(K-pitch) (T1)–(T5) transfer claims | W4 §(SAFE-RES) (T) — triangle-freeness | — |
| **(W1)–(W4)** | §(K-slide) limit-system conditions | the phase's **work packages** W0–W5 (**W4 = `hcontract`**) | — |
| **(N1), (N2)** | §(K-Δ) the two readings | N8/N9/N10/N10b the W4 gates | — |
| **(F1)** | §(K-flank) claim / *Steps* F0–F7 | `dispatch-log.md` F-rows (F5, F11, F12, …) | — |
| **(σ5)** | §(K-σ) claim (σ5) | §(K-σ) *Step σ5* (the four obligations) | — |
| **(S1)–(S5)** | §(K-slide) claims | `S29` test shape (distinct form; noted for completeness) | — |

The two most dangerous in live prose are **(W4)** — because "W4" reads as
`hcontract` everywhere in `Phase39.md` and as the limit-system condition
everywhere in §(K-slide)/§(K-pure) — and **(C6)/(C7)**, which have already
caused one landed fixup.
