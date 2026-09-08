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

**This file is the canonical detail for the general rule.** `RESEARCH-ARC.md`
§1 promotes the reservation-plus-minting-rule pattern for any research-shaped
phase and carries the *why*; this file stays authoritative for the mechanics
and every label's meaning.

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

Seven clauses. They are cheap; clause 1 is the one that actually prevents the
next collision, (L6) is the landing-time backstop for the one case L1
structurally cannot see, and (L7) is how the *check itself* is run.

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
  **Scope, sharpened 2026-08-20 — L4 covers the GRANDFATHERED corpus, not a
  fresh mint.** A bare token caught within a few commits of the landing that
  minted it is **renamed**, not qualified: direction A's `(R1)`/`(R2)` →
  `(ANH-R1)`/`(ANH-R2)` at landing, and GFLOW's `(R1)`/`(C1)`/`(C2)` →
  `(GR-R1)`/`(GR-C1)`/`(GR-C2)` by user adjudication three commits after
  (the collision record below). The two clauses do not conflict — L4 prices
  churn against ~40 existing references, and (L6) exists to catch a token
  before it has three.
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
- **(L6) Landing-time bare-token grep** *(coordinator process fix, 2026-08-20,
  after the GFLOW collision below)*. The reservation check in (L1) verifies
  only the *prefix* and the *step range* — it structurally cannot see a bare
  `(X<digit>)` token minted **inside** a reservation for a sub-clause, which
  is exactly how direction A's bare `(R1)`/`(R2)` and direction GFLOW's bare
  `(R1)`/`(C1)`/`(C2)` both got through (clause L1's "a reserved prefix
  protects a dispatch from its siblings, not from the existing corpus"
  firing twice in the phase). The cheap fix is a **landing-time** grep for
  bare `(X<digit>)` tokens in the returned draft — run it in addition to,
  not instead of, the prep-time prefix/range check.
  **SHARPENED 2026-09-08 (direction BFOUR), and the sharpening is free: the
  grep runs over the WHOLE REPOSITORY, not the returned draft alone, and a
  hit in a `*.lean` doc-comment COUNTS.** BARCH's `(E4)` is the measured
  case. It is a bare `(X<digit>)` token minted inside a reservation, and it
  collides **two** ways: with §(K-grid)'s **live** termination-ledger family
  `(E1)`/`(E2)`/`(E3)` — whose next slot it takes, and which *this file
  already names three times* — and with the molecular program's brick codes
  in **live Lean doc-comments** (`Molecular/Induction/Operations.lean` uses
  `(E4)` for the ENTRY binder reshape; `Arms.lean` `(E5)`,
  `ForestSurgery/Reduction.lean` `(E2)`). A grep confined to the draft, or
  to `notes/`, sees neither. **And the reference count is the real lesson**:
  four commits after the mint, `(E4)` already carried ~74 references across
  10 files, **two of them landed drivers** — so a bare token minted inside a
  reservation can blow past (L4)'s own *"~40 existing references"*
  grandfathering threshold **in a single landing**, which makes the
  landing-time grep the only place it can be caught cheaply.
  **DISPOSITION, SETTLED (coordinator, 2026-09-08): NO RENAME.** `(E4)` now
  names a **refuted** clause ((BE-160)), so renaming buys nothing
  mathematically while costing edits to two landed drivers and the
  figure-invariance gate's one-line discharge; and the **live** successor
  token **`(BE-E4′)`** is already `BE-`-prefixed and was 0-hit at mint, so
  the compliant name is in place going forward and the collision is
  confined to history. The standing obligations are therefore (i) the
  collision-table row above, (ii) **(L3)-qualified citations throughout** —
  write `§(K-bare-ext) (E4)` — and (iii) a recorded **debt item**: were a
  rename ever wanted, the name is **`(BE-E4)`** (0-hit at 2026-09-08),
  priced at ~74 references across 10 files including `w4/barch.py` and
  `w4/bfour.py`, which makes it a deliberate coordinator round and **not**
  something a dispatch may do.
- **(L7) A reservation check enumerates the range; it does not sample it**
  *(landing fix, 2026-09-03, direction BARCH — the incident and its
  two-defect comparison are in the BARCH reservation block below)*. Check
  **every** token in the reserved range — both label forms and every raw step
  token — and report **HITS** (matching lines) and **FILES** separately.
  Sampling the range's endpoints is not a check, and sampling its *closing*
  endpoints is the worst case: the *opening* tokens are exactly the ones the
  predecessor's own tail-declaration had to write down, so a hit there is
  **guaranteed** and is precisely what a sampled check will miss.

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
(`notes/Pencil-fanout-archive.md` §"Second fan-out"; letters chosen precisely to avoid
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
(`notes/Pencil-fanout-archive.md` §"Third fan-out"; letters dated — A/B/C and T/R/M
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
(`notes/Pencil-fanout-archive.md` §"Fourth fan-out"; letters dated — A/B/C (×2),
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
(`notes/Pencil-fanout-archive.md` §"Fifth fan-out"). **The first fan-out under (L5)**:
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

**The SIXTH direction — CFLANK — LANDED 2026-08-07**
(`notes/Pencil-fanout-archive.md` §"Sixth direction"), reservation row moved into
the registry above: (GR-21)–(GR-26), Steps G24–G28, `w4/cflank.py` (§(K-grid)'s
row — the argument stayed inside §(K-grid)'s own family, so the reserved
section name **§(K-prof)** and its tag **`PF-`** were never opened and
return to the pool unopened; the optional M2 leaf `m2/cflank.m2` was also
never needed). A **single direction**, not a fan-out — its selection was
**delegated to the coordinator**, not user-adjudicated from a candidate
list (`notes/Pencil-adjudications.md`, the "keep going on my own
judgment" adjudication). No flank found; (GR-15) stays OPEN, unchanged in
status.

**The SEVENTH direction — GCAP — LANDED 2026-08-13**
(`notes/Pencil-fanout-archive.md` §"Seventh direction"), reservation row moved
into the registry above: (GR-27)–(GR-28), Steps G29–G33, `w4/gcap.py`
(§(K-grid)'s row — the argument stayed inside §(K-grid)'s own family, so
the reserved section name **§(K-gcap)** and its tag **`GC-`** were never
opened and return to the pool **unopened**, reserved-but-unopened — the
same disposition §(K-prof)/`PF-` got from CFLANK; the optional M2 leaf
`m2/gcap.m2` was also never needed). A **single direction**, not a
fan-out — its selection was **delegated to a top-rung fable recon** under
the 2026-08-12 refinement of the standing delegation (`notes/Phase39.md`
*Current state*). No flank found; (GR-15) stays OPEN, unchanged in
status.

**The EIGHTH direction — GUNIF — LANDED 2026-08-13**
(`notes/Pencil-fanout-archive.md` §"Eighth direction"), reservation row moved
into the registry above: (GR-29)–(GR-31), Steps G34–G37, `w4/gunif.py`
(§(K-grid)'s row — the argument stayed inside §(K-grid)'s own family
**again**, so the reserved section name **§(K-gcap)** and its tag
**`GC-`** were **still** never opened and return to the pool
**unopened, reserved-but-unopened**, exactly as they did from GCAP; no
M2 leaf was expected or opened). A **single direction**, not a
fan-out — selected under the standing 2026-08-07 delegation as refined
2026-08-12 (the TERMINATION test checked on GCAP's return did not
fire). **GUNIF refuted both of its targets**: (GR-28)(iv) at `k ≥ 3` is
REFUTED with an exact boundary (four constructed habitat witnesses at
`n_hub = 8, 10, 12, 16`; a theorem exactly at `n_hub ≤ 6`, false from
`n_hub = 8` on), and the (GR-24)-analogue repair theorem is unprovable
as posed (premise refuted, measured conclusion also false at `n_hub =
16`). Per-shape (GR-15) HOLDS at all four new witnesses; (GR-15) itself
stays OPEN, unchanged in status. **§(K-unif)/`GU-` was considered and
is, again, deliberately NOT reserved** — verified 0-hit and recorded
here so a successor does not mint them.

**The NINTH direction — GEXIST — LANDED 2026-08-13**
(`notes/Pencil-fanout-archive.md` §"Ninth direction"), reservation row moved
into the registry above: (GR-32)–(GR-35), Steps G38–G42, driver modes
`--exh`/`--charge`/`--repair`/`--adv`/`--validate` (`w4/gexist.py`;
§(K-grid)'s row — the argument stayed inside §(K-grid)'s own family
**again**, so the reserved section name **§(K-gcap)** and its tag
**`GC-`** were **still** never opened and return to the pool
**unopened, reserved-but-unopened**, available a third time; no M2 leaf
was expected or opened). A **single direction**, not a fan-out — its
selection was **delegated to a top-rung fable recon** by the user's
2026-08-13 check-in pick of the option "Delegate to a fable recon
(2026-08-12 style)" (an option selection, not free-text; the same
shape that selected GCAP). **GEXIST is an honest MISS**: three new
theorems — **(GR-32)** the capacity theorem, **(GR-33)** the weakness
lemma, **(GR-35)** the uncrossing lemma — reduce the uniform target to
a **minority-dart orientation problem** with one unit of slack at every
proper chunk; **(GR-34)** refutes the uncorrelated (first-moment /
union-bound) mechanism by a constructed witness (`CL10`) while a
correlated **rung-minority rule** closes the whole ladder family by
explicit rank-certified colourings. No g-flank found; the target stays
**OPEN**, and so does **(GR-15)**, unchanged in status. **§(K-unif)/`GU-`
stays, again, deliberately NOT reserved.**

**The TENTH direction — GORIENT — LANDED 2026-08-13**
(`notes/Pencil-fanout-archive.md` §"Tenth direction"), reservation row moved
into the registry above: (GR-36)–(GR-39), Steps G43–G47, driver modes
`--hall`/`--kill`/`--hot`/`--adv`/`--validate` (`w4/gorient.py`;
§(K-grid)'s row — the argument stayed inside §(K-grid)'s own family
**again**, so the reserved section name **§(K-gcap)** and its tag
**`GC-`** were **still** never opened and return to the pool
**unopened, reserved-but-unopened**, available a fourth time; no M2
leaf was expected or opened). A **single direction**, not a fan-out —
its selection was **re-delegated to a top-rung fable recon** at the
user's 2026-08-13 check-in (the third use of the 2026-08-12 shape that
selected GCAP and GEXIST). **GORIENT is an honest MISS**: four new
theorems — **(GR-36)** the structural charge, **(GR-37)** the selection
reduction, **(GR-38)** the intersection kill (settled vacuously strong
at `n_hub ≤ 6`), **(GR-39)** the hot-hub adjudication (census upgraded
to exhaustive) — re-anchor the target on a **bounded-deviation
selection principle**, sticking at **W3** (needs `d = 3` against the
measured `d ≤ 2` elsewhere). No g-flank found; the target stays
**OPEN**, and so does **(GR-15)**, unchanged in status. **§(K-unif)/`GU-`
stays, again, deliberately NOT reserved.**

**The ELEVENTH direction — GDEV — LANDED 2026-08-15**
(`notes/Pencil-fanout-archive.md` §"Eleventh direction"), reservation converted
in place: **(GR-40)–(GR-42) and Steps G48–G52 are CLAIMED**, leaving
**(GR-43)+ and Steps G53+** as §(K-grid)'s live unclaimed tails; driver
modes `--charge`/`--bound`/`--adv`/`--hunt`/`--validate`
(`w4/gdev.py`; §(K-grid)'s row — the argument stayed inside
§(K-grid)'s own family **again**, so the reserved section name
**§(K-gcap)** and its tag **`GC-`** were **still** never opened and
return to the pool **unopened, reserved-but-unopened**, available a
**sixth** time; no M2 leaf was expected or opened). A **single
direction**, not a fan-out — selection delegated to a top-rung fable
recon at the user's 2026-08-14 check-in (the fourth use of the
2026-08-12 shape); verdict verified and ACCEPTED. **GDEV is a
REFUTATION-with-successors, not a MISS**: **(GR-40)** the corner
charge (sub-deliverable (b) as a standalone theorem, tight at W3M
where (GR-36) prices 0), **(GR-41)** the parity floor (deviations
bounded below by the coset invariant `φ*`), **(GR-42)** the
pentagon-necklace family — the bounded-deviation selection form is
**refuted as posed** (`d ≥ m/2`, unbounded; every member
rank-certified fully-good, so a form-refutation, never a flank); the
W3 stick located in the **balance layer** (`φ*(W3) = 2`, not parity);
`d_fg = d_adm` measured 133/133. (GR-15) stays OPEN, unchanged in
status. **§(K-unif)/`GU-` stays, again, deliberately NOT reserved.**
The code **GDEV** (the
bounded-**DEV**iation selection theorem) was verified **0-hit as a raw
substring**, case-insensitively, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` at reservation time — as was the driver basename `gdev` (control
tokens `gorient`/`gexist` hit 7/9 files, so the grep was live). Checked
0-hit and **rejected**, recorded so they stay checkable without a re-run:
`GSEL` (names the generic mechanism, not the theorem's content — the *bound*
on the deviation count), `GPM`, `GMATCH`, `GBOUND`, `GBDD`, `GANCHOR`,
`GDEVI`. GORIENT-prep's checked-not-chosen list (`GHALL`/`GCSP`/`GHOT`/
`GSAT`) was **not** re-used: the deliverable changed, and those checks are a
landing old. The direction *extended* §(K-grid): the reserved tails
**(GR-40)+** / **Steps G48+** (both verified 0-hit at reservation time)
were consumed exactly as **(GR-40)–(GR-42)** / **Steps G48–G52**, per
the claim recorded at the top of this entry; the owning section stays
authoritative. **Do not mint §(K-unif)/`GU-`** (considered twice,
deliberately not minted — recorded below).

**The TWELFTH direction — GADM — LANDED 2026-08-17**
(`notes/Pencil-fanout-archive.md` §"Twelfth direction"), reservation converted
in place: **(GR-43) and Steps G53–G57 are CLAIMED**, leaving
**(GR-44)+ and Steps G58+** as §(K-grid)'s live unclaimed tails; driver
modes `--nk`/`--free`/`--balance`/`--adv`/`--validate` (`w4/gadm.py`;
§(K-grid)'s row — the argument stayed inside §(K-grid)'s own family
**again**, so the reserved section name **§(K-gcap)** and its tag
**`GC-`** were **still** never opened and return to the pool
**unopened, reserved-but-unopened**, available a **seventh** time; no
M2 leaf was expected or opened; this landing also **BACKFILLED the
GDEV clause into the §(K-grid) registry row**, which the eleventh's
landing had recorded only in its narrative entry). **GADM is an honest
MISS on (a′)-as-a-theorem carrying one new theorem and a refutation**:
**(GR-43)** the odd-cycle-packing shift floor — `d_par = d_adm = d_fg
= m` **exactly** at NK(2)/6/8/10, rank-certified at the optimum — so
experiment 1 lands outcome 3: the **shift-metric layer is unbounded**
and the growth law's bounded-correction reading is **refuted**, while
the **(a′) `d_fg = d_adm` law survives its first large-`d` test**;
ledger **entry 5 settled as a separate OPEN statement** ((GR-37)(iii)'s
"balance rider alike" clause is statement-beyond-proof, flagged at the
statement site); **(b′) supported** (balance gaps `{0, 1, 2}`
everywhere probed; the W3 stick corrected to a 1-shift + 1-balance
split). No g-flank found; **(GR-15) stays OPEN, unchanged in status.**
A **single direction**, not a
fan-out. **Selection shape differs from the four picks before it:** the
user's 2026-08-17 check-in elected **coordinator-authored prep from the
eleventh landing's routing clause** over the 2026-08-12 fable-recon
shape, so the spec and its ranking record are the coordinator's, with
the cost ("no independent ranking of the losers") disclosed in the
spec's own *Status*. Target: the growth-law question at the pentagon
necklaces — attack **(a′)** the `d_fg = d_adm` law (primary) and
**(b′)** the balance-layer bound (secondary). The code **GADM** (the
`d_fg = d_`**ADM** law) was verified **0-hit as a raw substring**,
case-insensitively, across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at
reservation time — as was the driver basename `gadm` (controls `gdev`
8 files, `gorient` 8, `gexist` 10, so the grep was live). **`GFREE` was
checked and REJECTED for a LIVE hit** (`Gfree`,
`notes/scripts/m2/lambda1.m2:129`) — the first candidate code in this
arc to lose to an actual substring collision rather than to a naming
judgement, recorded because it is clause L5's check earning its keep.
Checked 0-hit and **not chosen**, recorded so they stay checkable
without a re-run: `GLAW`, `GGROW` (both name the growth *law*
generically rather than the layer this direction proves — the `GSEL`
rejection reason one landing back), `GLAYER`, `GBAL`, `GSPLIT`,
`GLIFT`, `GFG`. GDEV-prep's checked-not-chosen list was **not** re-used
(the deliverable changed, and those checks are a landing old). The
direction *extends* §(K-grid), so its reservation is that section's
unclaimed tails and the owning section stays authoritative. **On
outgrowth reuse the already-reserved §(K-gcap) / `GC-`** — returned
unopened by GCAP, GUNIF, GEXIST, GORIENT, GDEV and now GADM, available
a **seventh** time. **Do not mint §(K-unif)/`GU-`** — considered
twice, deliberately not minted, and this landing does not revive it.
No M2 leaf was expected or opened.

**The THIRTEENTH direction — GPSA — LANDED 2026-08-18**
(`notes/Pencil-fanout-archive.md` §"Thirteenth direction"), reservation
converted in place: **(GR-44)–(GR-45) and Steps G58–G62 are CLAIMED**,
leaving **(GR-46)+ and Steps G63+** as §(K-grid)'s live unclaimed
tails; driver modes `--sdr`/`--balance`/`--odd`/`--adv`/`--validate`
(`w4/gpsa.py`; §(K-grid)'s row — the argument stayed inside
§(K-grid)'s own family **again**, so the reserved section name
**§(K-gcap)** and its tag **`GC-`** were **still** never opened and
return to the pool **unopened, reserved-but-unopened**, available an
**eighth** time; no M2 leaf was expected or opened). **GPSA lands
entry 5's parity half as a THEOREM ((GR-44): the Hall/SDR step
automatic, `d_par(M) = w_M` exact) and its balance half
true-modulo-named-gap ((GR-45) + the descent lemma's stuck case) —
entry 5 NOT a HIT, E3 not armed; the fourteenth routes to the stuck
case.** A **single direction**, not a fan-out.
**Selection returned to the fable-recon shape** — the user's
2026-08-18 check-in elected "Delegate the pick to a fable recon" (the
**fifth** use of the 2026-08-12 shape, chosen specifically because the
coordinator-authored twelfth prep had no independent ranking of the
losers); the recon's verdict was verified and **ACCEPTED, including
its OVERRIDE of GADM's shift-metric routing clause** (grounds and the
process finding in the spec). Target: **route-ledger entry 5 —
per-shape admissibility, BOTH halves** (the Hall/SDR parity step and
the ≤ 6-odd-branch balance rider), with **(b′)** the secondary. The
code **GPSA** (**P**er-**S**hape **A**dmissibility — the statement
itself) was verified **0-hit as a raw substring**, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation time —
as was the driver basename `gpsa` (controls `gadm` and `gdev` 9 files
each, so the grep was live). **`GBAL` — the recon's own first
suggestion — was reconsidered and NOT taken**: it is **no longer
0-hit** (it now sits in the GADM prep's checked-not-chosen lists, in
this file's GADM entry above and the fanout spec's — a bookkeeping hit
rather than a semantic one; the recon's own "must re-grep at prep"
caution is the check that fired, clause L5 earning its keep a second
time), and, decisive independently of the collision, "balance" names
only **one of the target's two halves** where `GPSA` names the
statement. Checked 0-hit and **not chosen**, recorded so they stay
checkable without a re-run: `GODD`, `GADMIS`, `GBALANCE`. GADM-prep's
checked-not-chosen list was **not** re-used (a landing old — and its
`GBAL` row is exactly what made this prep's grep live). The direction
*extends* §(K-grid), so its reservation was that section's unclaimed
tails and the owning section stays authoritative. **No outgrowth
occurred: §(K-gcap) / `GC-`** — returned unopened by GCAP, GUNIF,
GEXIST, GORIENT, GDEV, GADM and now GPSA — is available an **eighth**
time.
**Do not mint §(K-unif)/`GU-`** — considered twice, deliberately not
minted, and this prep does not revive it. No M2 leaf expected — the
target is a finite combinatorial statement.

**The FOURTEENTH direction — GDESC — LANDED 2026-08-18**
(`notes/Pencil-fanout-archive.md` §"Fourteenth direction"), reservation
converted in place: **(GR-46)–(GR-48) and Steps G63–G67 are CLAIMED**,
leaving **(GR-49)+ and Steps G68+** as §(K-grid)'s live unclaimed
tails; driver modes `--stuck`/`--cases`/`--opt`/`--adv`/`--validate`
(`w4/gdesc.py`; §(K-grid)'s row — the argument stayed inside
§(K-grid)'s own family **again**, so the reserved section name
**§(K-gcap)** and its tag **`GC-`** were **still** never opened and
return to the pool **unopened, reserved-but-unopened**, available a
**ninth** time; no M2 leaf was expected or opened). **GDESC RESHAPES
the target rather than closing it, and dissolves a route**:
**(GR-46)** the (GR-45) legal-move family is **one-move transitive**,
so (Cor. 1) the descent lemma over the FULL family is **equivalent to
entry 5's balance half** — the stuck case is no smaller residual — and
(Cor. 2) a full-family demotion witness exists iff `d_adm = ∞`, i.e.
it would have been E1 clause (v); **(GR-47)** the (coset
representative, SDR end-selection, perfect matching) **normal form**,
restating balance as a matching-flexibility statement; **(GR-48)** the
escape catalogue — the exact reduction criterion, the K1/K2 star
rescues, a **PROVEN {T1, T2} kill** at all-doubly-blocked
configurations and the **K3 pair-star** repair — with the kill
**REALIZED at n = 30** (two of 110 capped-hunt stuck configs at NKp(6)
defeat every {T1, T2} move), so the bounded **{T1, T2} descent route
is DEMOTED BY WITNESS** while {T1, T2, K3} stays unbeaten. **Entry 5
stays OPEN, NOT a HIT, E3 NOT armed**, its residual named **input
(X)**: balance existence in the (GR-47) normal form. **(b′)**'s named
unmeasured half is **measured** (`|δ|` at parity-optimal maps
`{0: 92, 2: 2}`); **(a′) was not attempted** and stays dispatchable
with no bar. No g-flank; **(GR-15) stays OPEN, unchanged in status.**
**§(K-unif)/`GU-` stays, again, deliberately NOT reserved.**
A **single direction**, not a fan-out. **No selection was made:
the routing is FIXED by GPSA's landed otherwise-clause** (*"entry 5
stuck with a named blocking configuration → that configuration"*),
whose stuck branch was instantiated by GPSA's own landing — so unlike
GADM's overridden clause this one routes on landed mathematics, not on
a pre-landing guess. **The prep was authored at the `opus` rung by
explicit user adjudication** (a recorded down-substitution against a
top-rung-mapped task; weekly_scoped at 83%, fable conserved for the
direction's own dispatch — `notes/dispatch-log.md`, 2026-08-18).
Target: **the entry-5 descent lemma's STUCK CASE** — every
majority-side odd branch dart-blocked, a finite local case analysis
over the ≤ 6 odd branches with the T1/T2-family escape catalogue —
with **(b′)** the secondary. The code **GDESC** (the **DESC**ent
lemma — the statement the direction closes, not the case it is stuck
at) was verified **0-hit as a raw substring**, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation time —
as was the driver basename `gdesc` (controls `gpsa` 7 files and `gadm`
9, so the grep was live). **`GDART` was checked and REJECTED for a
hit** — it sits in `notes/Pencil-fanout-archive.md` §"Eighth direction"'s
code-minting paragraph (the GUNIF prep's own checked-but-not-used
list): a **bookkeeping** hit like `GBAL`'s one prep ago, not a semantic
one, and the second consecutive time clause L5's
"re-grep at prep" has fired on this arc's own records. Checked 0-hit
and **not chosen**, recorded so they stay checkable without a re-run:
`GSTUCK` (names the residual *case*, not the theorem), `GESC` /
`GESCAPE` (name the *method* — the `GSEL` rejection reason), `GBLOCK`,
`GDROP`, `GTRAP`, `GDESCENT`. GPSA-prep's checked-not-chosen list
(`GODD`/`GADMIS`/`GBALANCE`) was **not** re-used (a landing old, and
the deliverable changed). The direction *extended* §(K-grid), so its
reservation was that section's unclaimed tails — **(GR-46)+ / Steps
G63+**, consumed exactly as **(GR-46)–(GR-48) / Steps G63–G67** per
the claim recorded at the top of this entry — and the owning section
stays authoritative. **On outgrowth reuse the already-reserved
§(K-gcap) / `GC-`** — returned unopened by GCAP, GUNIF, GEXIST,
GORIENT, GDEV, GADM, GPSA and now GDESC, available a **ninth** time.
**Do not mint §(K-unif)/`GU-`** — considered twice, deliberately not
minted, and this landing does not revive it. No M2 leaf was expected
or opened — the target was a finite combinatorial statement.

**The FIFTEENTH direction — GBAL — LANDED 2026-08-19**
(`notes/Pencil-fanout-archive.md` §"Fifteenth direction"), reservation
converted in place: **(GR-49)–(GR-54) and Steps G68–G73 are CLAIMED**,
leaving **(GR-55)+ and Steps G74+** as §(K-grid)'s live unclaimed
tails; driver modes
`--zform`/`--oracle`/`--two`/`--split`/`--thm`/`--adv`/`--validate`
(`w4/gbal.py`; §(K-grid)'s row — the argument stayed inside
§(K-grid)'s own family **again**, so the reserved section name
**§(K-gcap)** and its tag **`GC-`** were **still** never opened and
return to the pool **unopened, reserved-but-unopened**, available a
**tenth** time; no M2 leaf was expected or opened). **GBAL is a
HIT — the arc's FIRST**: input (X) is **DISCHARGED**. A change of
coordinates — **(GR-49)**, the z-form: a parity-consistent minority
map with a chosen potential is exactly an admissible dart 2-colouring,
one bit per branch, absorbing the whole (c, m)/coset/SDR/matching
apparatus — turns balance into **(GR-50)**, a degree-constrained
orientation of the even branches decided EXACTLY in polynomial time;
**(GR-51)** collapses its two-sided Hall condition to a local weight
inequality negative only at a monochromatic-pair hub; **(GR-52)**
shows one such hub per side is harmless (a parity contradiction);
**(GR-53)** shows one always suffices (a finite exhaustion over the
maximal constraint structures); **(GR-54)** chains the five into the
**balance theorem**. **Entry 5 is PROVEN in both halves** — the parity
half re-derived **without Petersen**, (GR-44)'s `d_par(M) = w_M`
untouched — and **E3 is ARMED but does NOT fire** (entry 1's **(a′)**
stays open, no bar, GLAW's target this wave). The (GR-45)–(GR-48)
apparatus is **subsumed, not contradicted**, no landed figure moves;
one in-place correction to route note (b) (*Step G65*): the `2k = 2`
dichotomy's exceptional side is the **parallel pair** (a cycle-space
condition), not a 2-edge cut, and both readings are **vacuous at
habitat shapes**. No g-flank; **(GR-15) stays OPEN, unchanged in
status.** **§(K-unif)/`GU-` stays, again, deliberately NOT reserved.**
One of **five** concurrent directions in the **sixth fan-out**
(GBAL/GLAW/OCON/LTWO/FRES, dispatched 2026-08-19 by explicit user
adjudication, `notes/Pencil-fanout-archive.md` §"Sixth fan-out"), not a serial
single direction — GBAL and GLAW ran in the **compute-licensed** tier,
OCON/LTWO/FRES in the **derivation-first** tier (coordinator-set).
Dispatched **opus**. Target: **input (X)** — balance existence in the
(GR-47) normal form, GDESC's named residual — with one
(a′)-relevant z-form by-product reported (not developed) as a finding
for GLAW / the successor. The code **GBAL** (**BAL**ance — the
statement's content) sat as a **bookkeeping** hit (not a semantic
collision) in GADM's checked-not-chosen list and was reconsidered but
**not** taken at both GPSA's and GDESC's own preps, each for the same
reason: "balance" named only part of *their* target ("per-shape
admissibility" at GPSA, "the descent lemma's stuck case" at GDESC).
It is **taken here** because the mismatch that sank it twice does not
apply: this direction's deliverable *is* exactly balance existence,
and no live section or tag currently uses the name. The direction
*extended* §(K-grid), so its reservation was that section's unclaimed
tails — **(GR-49)+ / Steps G68+**, consumed exactly as **(GR-49)–(GR-54)
/ Steps G68–G73** per the claim recorded at the top of this entry —
and the owning section stays authoritative. **On outgrowth reuse the
already-reserved §(K-gcap) / `GC-`** — returned unopened by GCAP,
GUNIF, GEXIST, GORIENT, GDEV, GADM, GPSA, GDESC and now GBAL, available
a **tenth** time. **Do not mint §(K-unif)/`GU-`** — considered twice,
deliberately not minted, and this landing does not revive it. No M2
leaf was expected or opened — the target was a finite combinatorial
statement.

**The SIXTEENTH direction — GLAW — LANDED 2026-08-19**
(`notes/Pencil-fanout-archive.md` §"Sixteenth direction"), reservation
converted in place: **(GR-55)–(GR-60) and Steps G74–G79 are CLAIMED**,
leaving **(GR-61)+ and Steps G80+** as §(K-grid)'s live unclaimed
tails; driver modes
`--law`/`--nf`/`--exh`/`--sdr`/`--big`/`--adv`/`--validate`
(`w4/glaw.py`; §(K-grid)'s row — the argument stayed inside
§(K-grid)'s own family **yet again**, so the reserved section name
**§(K-gcap)** and its tag **`GC-`** were **still** never opened and
return to the pool **unopened, reserved-but-unopened**, available an
**eleventh** time; no M2 leaf was expected or opened). **GLAW is an
honest MISS carrying four theorems and one refutation.** **(GR-55)**
puts every minority map at deviation distance `d` from a perfect
matching in a `(y, Z, φ)` normal form, parity-consistency a condition
on `y` alone, the `M`-avoiding coset space affine of dimension
`n/2 − 1`; **(GR-56)** supplies the missing SPLIT identity, collapsing
full-goodness to ONE inequality per chunk of which the balance rider
is exactly the whole-graph instance; **(GR-57)** is the SDR exchange
calculus — the elementary shift is a distance-preserving 2-hub move
that CROSSES μ-classes, GADM's named missing second exchange axis;
**(GR-58)** verifies `d_fg = d_adm` EXHAUSTIVELY at all 4920
`n_hub ≤ 6` habitat shapes at no deviation cap, and at the first
odd-carrying `n = 30` tests. **(GR-59)** REFUTES the per-matching
variant of (a′) — 1278 of 24 638 (shape, matching) pairs, smallest
witness `n_hub = 4` — so `min_M` is load-bearing and no (a′) proof may
fix its anchor matching; (a′) itself is untouched. **(GR-60)** names
the residual **input (Y)**, a joint matching-and-representative
selection statement. **A cross-entry finding:** by (GR-56)(iv),
GDESC's input (X) (now PROVEN by GBAL) and this input (Y) are the
whole-graph and proper-chunk instances of one inequality, but the
proof does **not** transfer. **(a′) did NOT HIT; entry 1 stays OPEN,
no bar; E3 stays ARMED (by GBAL) but does NOT fire**; no g-flank,
(GR-15) stays OPEN. One of **five** concurrent directions in the
**sixth fan-out** (GBAL/GLAW/OCON/LTWO/FRES, `notes/Pencil-fanout-archive.md`
§"Sixth fan-out"), in the **compute-licensed** tier alongside GBAL.
Dispatched **opus**. Target: **(a′)**, the `d_fg = d_adm` law, entry
1's primary. **The direction code GLAW is the arc's first re-use of a
previously-rejected candidate**: `GLAW` was checked 0-hit and rejected
at GADM's prep (*"names the growth law generically rather than which
layer this direction proves"*) — that ground no longer applies here,
since this direction's deliverable *is* that law itself, so the code
was taken; its only pre-existing occurrences are the two bookkeeping
lines recording the earlier rejection (`notes/Pencil-fanout-archive.md`
§"Twelfth direction", this file above), a **bookkeeping** hit in the
`GBAL`/`GDART` sense, not a semantic one. The direction *extended*
§(K-grid), so its reservation was that section's unclaimed tails —
**(GR-55)+ / Steps G74+**, consumed exactly as **(GR-55)–(GR-60) /
Steps G74–G79** per the claim recorded at the top of this entry — and
the owning section stays authoritative. **Do not mint §(K-unif)/`GU-`**
— considered twice, deliberately not minted, and this landing does not
revive it. No M2 leaf was expected or opened.

**The NINETEENTH direction — FRES — LANDED 2026-08-19**
(`notes/Pencil-fanout-archive.md` §"Nineteenth direction"), reservation converted in
place in §(K-frame)'s row above: **(FR-15)–(FR-17) and Steps FR12–FR15 are
CLAIMED**; **(FR-18) is reserved and returned UNUSED**, available for a
later direction. One of **five** concurrent directions in the **sixth
fan-out** (GBAL/GLAW/OCON/LTWO/FRES, `notes/Pencil-fanout-archive.md` §"Sixth
fan-out"), in the **derivation-first** tier. Dispatched **opus**. Target:
§(K-frame) (FR-4)'s single named gap (the (GR-5)-at-`G′` restatement).
**Verdict: (FR-4) CLOSED — but not by the restatement alone.** (FR-15)
transports (GR-5) to `G′` verbatim, minus its target-rank clause; but (GR-5)
is a chart-**MAP** statement (hub normals free, points derived) while
(ANH-9)(iii) needs membership in the chart-**VARIETY** of (ANH-9)(ii) (hub
points free, normals derived) — a different sentence, **the direction's one
genuine finding**. **(FR-16)** discharges it: at a σ-fixed configuration the
normals *are* the points, so the two parametrizations' genericity loci
coincide on the single clause `framedom.legality_free` already tests, and it
also retro-certifies (FR-6)'s θ(3,4,5) points. **(FR-17)** then proves the
(ANH-R1) β-clause at every bare-cycle site of every `k = 4` class triple
(76 sites, 22 iso classes) with **no named gap**, at the arc's ordinary
proven-informally standing. **No driver was run**: the reserved
`notes/scripts/w4/fres.py` returned **unused and not created**, every
hypothesis consumed being already asserted by the landed `framedom.py`. No
`GR-` label minted and §(K-grid) not touched; (OC-8) and §(K-Λ) item (vii)
cited, not worked; the (FR-6) follow-ons untouched and un-commissioned. The
code **FRES** was verified 0-hit as a raw substring across the pencil doc
set at reservation time; **(L5) note, recorded not demanded**: repo-wide the
bare token is a substring of 19 unrelated hits, every one inside the word
`FRESH` (`Molecular/Induction/Operations.lean`, `notes/dispatch-log.md`,
`notes/model-experiment-archive.md`, `notes/Phase23-design.md`,
`notes/coordinate-phase-rescue.md`) — harmless, and **no rename is
proposed**; (L5)'s substring check is stated repo-wide, so the reservation
technically missed it, recorded so the next one greps the whole tree.

**The SEVENTEENTH direction — OCON — LANDED 2026-08-19** (fourth of the
sixth fan-out's five to land, after GBAL/GLAW/FRES; `notes/Pencil-fanout-archive.md`
§"Seventeenth direction"), reservation converted in place in §(K-out)'s row
above: **(OC-17)–(OC-22) and Steps O13–O18 are CLAIMED**; the tails move to
**(OC-23)+ / O19+**, §(K-out)'s live unclaimed range. One of **five**
concurrent directions in the **sixth fan-out** (GBAL/GLAW/OCON/LTWO/FRES,
`notes/Pencil-fanout-archive.md` §"Sixth fan-out"), in the **derivation-first** tier.
Dispatched **opus**. Target: §(K-out) (OC-8)'s hard-stratum target-rank
qualifier. **Verdict: an honest MISS carrying three theorems and a
reduction — (OC-8) stays OPEN, reshaped.** **(OC-17)** proves
`dim R_a = corank(G′) − s₀` at every legal chart point with no genericity,
so the hard-stratum target-rank locus `Z` is an intersection of two
maximal-rank conditions — Zariski **open**, not a stratum — which **strikes**
§(K-frame) (FR-7)'s (OC-16)-side un-owned-irreducibility sentence (`Z`'s
irreducibility is the chart's, owned by (ANH-9)(ii)) and makes §(K-frame)
*What would change this* item (iii) **unnecessary rather than open**; `Z ≠ ∅`
is a separate input, and a prerequisite of the *whole* (K-tight) criterion,
not (OUT)'s to pay. **(OC-18)** gives a degree-free sufficient condition —
`H/X` infinitesimally rigid at a chart point ⟹ `L_b ⊄ R₁` — open, at **both**
ends of **every** class pair (5226/5226 labelled POOL-CW pairs, vs (OC-12)'s
3081/3702 and (OC-13)'s 1715). **(OC-19)** reduces (OC-8) at a (shape, split)
to `Z ≠ ∅` + chart irreducibility + one chart point, anywhere, with `H/X`
rigid — one-point decidable, **two named inputs ADDED, not removed**. The
adversarial control is the sharp finding: `--control` lands **3 constructed**
points **in `Z`**, guard-accepted, coincidence-free, `L_b ⊆ R₁`, `H/X`
flexible — `Z` genuinely meets the bad divisor, so the reduction needs
openness **plus** irreducibility **plus** a witness, and no two of the three
suffice. **(OC-20)/(OC-21)** restate the shape-level bad case in perp form
(`T_u^{⊥_B} ∩ β_b ≠ 0`) and strip `x₁` from the availability condition
(`L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁`). **(OC-22)** places the residue in §(K-ann)
(ANH-R1)'s object class, the first arrival at the *same kind of object*
rather than the same missing technology. **No gap-map status moves; class
uniformity untouched; (GR-15) untouched; no g-flank.** E1/E2/E3 all NO; E3
stays ARMED (by GBAL), not fired; entry 1 untouched. The code **OCON**
(the direction's target being the **O**uter-line chart's **CON**tainment
residue) was verified 0-hit as a raw substring, case-insensitively, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation time and re-checked
at landing (repo-wide, `*.py`/`*.m2`: 0 hits outside the driver's own
filename). The direction *extended* §(K-out), so its reservation was that
section's unclaimed tails — **(OC-17)+ / Steps O13+**, consumed exactly as
**(OC-17)–(OC-22) / Steps O13–O18** per the claim recorded at the top of
this entry — and the owning section stays authoritative. No M2 leaf was
expected or opened — the target was an exact-ℚ derivation, not a symbolic
one.

**The EIGHTEENTH direction — LTWO — LANDED 2026-08-19** (fifth and last of
the sixth fan-out's five to land, after GBAL/GLAW/FRES/OCON;
`notes/Pencil-fanout-archive.md` §"Eighteenth direction"), reservation converted in
place in §(K-Λ)'s row above: **(Λ4)–(Λ8) and Steps Λ8–Λ12 are CLAIMED**; the
tails move to **(Λ9)+ / Steps Λ13+**, §(K-Λ)'s live unclaimed range. One of
**five** concurrent directions in the **sixth fan-out**
(GBAL/GLAW/OCON/LTWO/FRES, `notes/Pencil-fanout-archive.md` §"Sixth fan-out"), in the
**derivation-first** tier. Dispatched **opus**. Target: §(K-Λ) item (vii) —
class shapes with two or more hubs on a length-4 companion's interior.
**Verdict: an honest MISS on the commissioned "prove the class forbids it"
branch — item (vii) is REALIZED.** **(Λ4)** the branch calculus reduces class
membership to a finite statement about the hub multigraph `G°` alone,
re-deriving girth `≥ 7`, (SD-6)'s `ℓ ≤ 5` and §(K-dom) (D3)'s `k ≥ 4` in one
line each — a reformulation, not new mathematics, but what makes the census
below exhaustive rather than capped. **(Λ5)** the companion-cycle lemma: no
branch outside the split-plus-companion `C₇` joins two of its hubs, the sole
exception being θ(3,4,5) (agreeing with §(K-out) (OC-10)'s independent
uniqueness proof — a cross-check, not re-derived). **(Λ6)** the size floor:
`j` interior hubs force `n° ≥ j + 3`, so `|V| ≥ 21` at `j = 2` and
`|V| ≥ 26` at `j = 3`, with the hub multigraph **forced** to the wheel at one
non-frame hub. **(Λ7)** the witnesses `LT21a`/`LT21b`/`LT26` attain those
floors exactly, each class-certified by the tracked oracles (at `|V| = 21`
also by the `2^{21}` partition oracle, `hnoRigid` over every vertex subset)
and each at a guarded hard-stratum target-rank chart point (`dim R_a = 1`)
with (Λ0d)/(Λ0g) holding and `g₁₄ ≠ 0`/`d g₁₄ ≠ 0`. **(Λ8)** classifies
(Λ0i)'s exact coverage: exactly the three patterns `(0,0,0)`/`(1,0,0)`/
`(0,0,1)`, never a two-hub-interior companion. **The correction**:
`outer.py --patterns`' recorded "4 of 8 patterns realized in scope" is a
**cap artifact** — its `V5e8` leg caps at 400 shapes of 19 041 length tuples
and terminates inside split index 0 of 8; uncapped at the exhaustive bound
`ℓ ≤ 5` the same family list realizes **7 of 8** patterns, `(1,1,0)`/
`(0,1,1)`/`(1,0,1)` at 80 each on the very hub multigraph `--patterns`
enumerated; only `(1,1,1)` is genuinely out of `|V°| ≤ 5` scope, now by
(Λ6), a theorem. The 7002 and "4 of 8" figures stay true **as measured**;
`outer.py` is untouched. **Λ-completeness stands as written; the (K-wit) row's
residual sentence is recomputed, not re-graded (status word unchanged); no
gap-map status moves; class uniformity untouched; (GR-15) untouched; no
g-flank.** E1/E2/E3 all NO; E3 stays ARMED (by GBAL's entry-5 HIT), not
fired; entry 1 untouched. The direction *extended* §(K-Λ), so its reservation
was that section's unclaimed tails — **(Λ4)+ / Steps Λ8+**, consumed exactly
as **(Λ4)–(Λ8) / Steps Λ8–Λ12** per the claim recorded at the top of this
entry — and the owning section stays authoritative. One driver added
(`w4/ltwo.py`, four modes: `--witness`/`--floor`/`--census`/`--validate`); no
M2 leaf was expected or opened — the target was an exact-ℚ derivation, not a
symbolic one. The **`Λ`-prefixed step scheme** (*Step Λ8* … *Step Λ12*,
distinct from the existing bare *Step 8*) is this direction's own convention,
per `notes/Pencil-labels.md`'s clause-4 diagnosis that bare step numbers
collide with claim labels — recorded in §(K-Λ)'s registry row above, not a
new minting rule.

**Reserved 2026-08-19 for the SEVENTH fan-out — directions YLOC / BALB / AGLU /
ZNEQ / CIRR** (`notes/Pencil-fanout.md` §"Seventh fan-out"; five concurrent
opus directions, the second multidispatch). Codes are **multi-letter and
topic-tagged** per clause (L5) — `YLOC` = input **(Y)** **LOC**alized, `BALB` =
the **BAL**ance-layer **B**ound, `AGLU` = the **A**A-**GLU**e configuration,
`ZNEQ` = **Z** **≠** ∅, `CIRR` = **C**hart **IRR**educibility. Every code, the
new section name **§(K-chart)** and the new prefix **`CH-`** were verified
**0-hit** across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation time.
Four of the five *extend* live sections, so their reservations are the
unclaimed tails of those sections' existing families and **the owning section
stays authoritative**; only CIRR opened a section. **All five have LANDED —
the seventh fan-out is COMPLETE — and every row is released below.**

**The TWENTY-FOURTH direction — CIRR — LANDED 2026-08-19** (first of the
seventh fan-out's five to land, `notes/Pencil-fanout.md` §"Twenty-fourth
direction"), reservation released: **the new section §(K-chart) is OPENED**,
tag `CH-`, with **(CH-1)–(CH-8) and Steps CH1–CH8 CLAIMED exactly** — the full
reservation consumed, nothing returned to the pool; see its new row in the
Registry below. One of **five** concurrent directions in the **seventh
fan-out** (YLOC/BALB/AGLU/ZNEQ/CIRR, dispatched 2026-08-19,
`notes/Pencil-fanout.md` §"Seventh fan-out"), in the **derivation-first**
tier. Dispatched **opus**. Target: write chart irreducibility down once, as a
standalone statement with a proof. **Verdict: a HIT.** **(CH-1)** proves the
pencil chart of `G′` (loopless, `hcard`, min degree 2, girth ≥ 4) is a
nonempty, irreducible, ℚ-rational variety — a tower of affine-linear fibres
whose constant-fibre-dimension restriction **is** `IsNondegPencilRealization`
conjunct 3 ((CH-6)), already carried by `hK`'s own hypothesis at `G′`; the
restriction costs no closure ((CH-4)); nonemptiness needs girth ≥ 4, not the
stated ≥ 3 ((CH-5), a correction to §(K-frame) *Step FR13*'s hypothesis list,
free at `G′` three ways); all **four** named consumers — §(K-out) (OC-19),
§(K-slide) (S1)(e), §(K-dom) (D4), §(K-ann) (ANH-9)(ii) — audit clean
((CH-7)). **One self-correction, recorded not dropped:** (CH-8) was drafted as
a new incidental and is **already landed, compiler-checked and strictly
stronger** as `not_pencilNondegFeasible_of_triangle_two_hubs`
(`Motive.lean:563`); it lands as a **pointer**, this section's own addition
being only the chart-side contrast (`𝒜(Γ) ≠ ∅` while the graph is infeasible).
No gap-map status moves; class uniformity, (OC-8), (ANH-R1), (GR-15), the
balance layer and route-ledger entry 5 all untouched. Driver
`notes/scripts/w4/cirr.py` (three modes `--empty`/`--guard`/`--fibre`, run
together by `--all`) — **written, contrary to the dispatch's "expected
unused"**, because (CH-5)'s and part of (CH-6)'s content is a sampler-behaviour
claim no amount of prose settles (F11). The code **CIRR** was verified 0-hit
as a raw substring across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at
reservation time. No M2 leaf was expected or opened — the target was
algebraic-geometry prose, not a symbolic computation.

**The TWENTIETH direction — YLOC — LANDED 2026-08-19** (second of the
seventh fan-out's five to land, after CIRR; `notes/Pencil-fanout.md`
§"Twentieth direction"), reservation released into §(K-grid)'s existing
registry row: **(GR-61)–(GR-66) and Steps G80–G85 CLAIMED exactly** — the
full reservation consumed, nothing returned to the pool; see the extension of
§(K-grid)'s row in the Registry below. Target: push GBAL's
(GR-49)–(GR-54) instrument down to the **chunk** level to discharge input
(Y). **Verdict: an honest MISS, with substantial positive content — the
localization FAILS and (Y) is NOT discharged.** **(GR-61)** carries the
(GR-56) chunk invariants into the `z`-form exactly (notation only); **(GR-62)
REFUTES step 2 by witness** — full goodness is **not** a function of the
(GR-50) degree data (7982/217 468 fibres split at 1499/4924 shapes, the
smallest witness rank-certified at `n_hub = 4`), so no (GR-51)-shaped
criterion applies to the chunk system, with the localization's premise's
exact boundary a 10-shape exceptional family; **(GR-63) REFUTES the
coordinator's predicted obstruction as stated** — (GR-52)'s parity step is a
**per-hub-subset** identity, available at every `R` (305 704 pairs, 0
failures), so it localizes for free, and the chain breaks two links earlier,
at (GR-50)→(GR-51); the positive content is **(GR-64)**, the collision
bound (a colouring-free lower bound on `d_fg` with a proven `≤ 2` per-chunk
ceiling, a packing form and a sound 1250-of-24 671 anchor-matching prune) and
**(GR-65)**, the fit identity (`dist(m, M)` and `z_mono(S)` are one
statistic); **(GR-66)** measures GBAL's own certificate against (Y), missing
both constraints at 3514/4924 and 651/4924 shapes respectively. Input (Y)
stays OPEN, (a′) is NOT hit, **E3 (ARMED by GBAL) does NOT fire**; (GR-15)
OPEN, no gap-map status moves. **Two coordinator adjudications on landing:**
the predicted-obstruction refutation is genuine, not a partial hit — the
prediction was wrong and (GR-63) is right; and GLAW's *Step G79* routing
override is **SPLIT, not simply upheld** — GBAL's `z`-form is reinstated for
the **chunk/balance** rung, and GLAW's matching-flexibility clause is
**reinstated for the distance rung specifically**, the two rungs bridged by
(GR-65)'s `fit`. **(GR-64)(R1)/(R2)** are sub-items of (GR-64), not separate
mints; **(GR-64)(R2)** (*"every habitat shape carries an anchor `M` with
`B(M) = 0`"*) is the sharpest cheap successor named, measured but not
proven. Driver `notes/scripts/w4/yloc.py` (seven modes
`--loc`/`--fibre`/`--par`/`--coll`/`--fit`/`--cert`/`--adv`, `--validate` runs
all seven but exceeds the 600 s foreground budget at ~890 s). The code
**YLOC** was verified 0-hit as a raw substring across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` at reservation time. No M2 leaf was expected or
opened.

**The TWENTY-FIRST direction — BALB — LANDED 2026-08-19** (third of the
seventh fan-out's five to land, after CIRR and YLOC; `notes/Pencil-fanout.md`
§"Twenty-first direction"), reservation released into §(K-grid)'s existing
registry row: **(GR-67)–(GR-72) and Steps G86–G91 CLAIMED exactly** — the
full reservation consumed, nothing returned to the pool; see the extension of
§(K-grid)'s row in the Registry below. Target: (b′), the balance-layer bound
`d_adm − d_par ≤ 2`, ridden as a secondary three times and made a **primary**
for the first time. **Verdict: (b′) stays OPEN, NOT a HIT — its PRICE half
becomes a THEOREM and its AVAILABILITY half is re-shaped at an exact
boundary.** **(GR-67)** anchors the z-form at a perfect matching — the
perfect-matching instance of GLAW's landed (GR-65)(i) fit identity,
independently re-derived and now corroborating it — giving the **parity
law** (every per-matching layer gap EVEN, so a violation must jump to 4,
never 3); **(GR-68)** prices every legal move in closed form (matching
branches and whole 2-factor cycles FREE, a single-path repair costing
exactly ≤ 2 at any length), **proving (b′)'s price half outright**;
**(GR-69)** derives the imbalance ceiling `|δ| ≤ 2·min(k, ⌊n_hub/4⌋)` from
(GR-51)(i)(a)'s necessity alone — a **THEOREM at `n_hub ≤ 6`** and **FALSE
from `n_hub = 8`** at an explicit Wagner-graph witness (`|δ| = 4`), tight at
every rung; **(GR-70)** reduces per-matching (b′) to one availability clause
(Clause A′), verified **EXHAUSTIVELY** on the whole stratum in its landed
T1-only instance, which is then **REFUTED from `n_hub = 8`** by stuck
witnesses, each repaired at price 0 by a named mixed-pair successor;
**(GR-71)** extends (b′) to 536 exact shapes at `n_hub = 8/10/12` and
cap-free per-matching certificates at `n = 30`. Residual: Clause A′'s
**doubly-blocked** case. **By-product, corroborated not developed:**
(GR-67) Cor. 1 extends to `d_fg(M)`, and GLAW's landed (GR-59) measurement
(`{2: 1251, 4: 27}`, all even) already confirms the prediction. Input (Y),
(a′), E3, (GR-15), class uniformity and route-ledger entry 5 all untouched.
Driver `notes/scripts/w4/balb.py` (six modes
`--anchor`/`--flip`/`--ceil`/`--exh`/`--big`/`--adv`, `--validate` runs all
six in ~135 s, inside the 600 s foreground budget). The code **BALB** was
verified 0-hit as a raw substring across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` at reservation time. No M2 leaf was expected or opened.

**The TWENTY-THIRD direction — ZNEQ — LANDED 2026-08-19** (fourth of the
seventh fan-out's five to land, after CIRR, YLOC and BALB;
`notes/Pencil-fanout.md` §"Twenty-third direction"), reservation released
into §(K-out)'s existing registry row: **(OC-23)–(OC-28) and Steps O19–O24
CLAIMED exactly** — the full reservation consumed, nothing returned to the
pool; see the extension of §(K-out)'s row in the Registry below. (**Its
successor tail (OC-29)–(OC-40) / Steps O25–O36 is now RESERVED, not free** —
OSCHU and SIGZ, the eighth fan-out's block below.) Target:
(OC-19) input (a), `Z ≠ ∅`, as a statement in its own right. **Verdict: input
(a) is OPEN as a class-uniform statement and is NOT an independent gap.**
**(OC-23)** peels the pendant edge `ac`: `s₀ = corank R(H)` at every legal
chart point, `H = G − v − a`, so the `s₀` half of input (a) is independence
of the far framework alone. **(OC-24)** proves the dichotomy — `Z ≠ ∅ ⟺`
both halves nonempty, each one-point witnessable — and the sharper finding:
`{σ = 0} = ∅` at a class shape would make `hK` **FALSE there**, a **PENCIL
event**, strictly stronger than the (K-tight) event the dispatch named; the
`s₀` half is therefore a **necessary condition** for `hK` and can never be
the binding obstruction. **(OC-25)** shows the target-rank half **is**
§(K-tight) *Step 2* item 1's own attainment criterion, one split down.
**(OC-26)** derives the closed form of failure along the meet line — a
**disjunction**, both branches forcing a codimension-2 Schubert jump — after
**refuting its own first closed form by construction** (POOL-ZQ Case C: a
nonsingular hyperplane with no pencil inside it, yet identical badness).
**(OC-27)** measures **138/138** (shape, split) witnesses of `Z ≠ ∅`, no
miss (POOL-ZN, caps disclosed). **(OC-28)** proves the `s₀` half is
**dominated** by §(K-grid) (GR-10) — one grid point per shape covers every
split at once, free at 907/907 of that pool, though the two pools are not
re-keyed — and exhibits `{σ = 0}` as a **proper** open at the (K-res) shape
`P21` (5 of 35 valid seeds off it). **Chart irreducibility (input (b)) is
cited from §(K-chart) (CH-1), not re-derived** — CIRR landed mid-run, and its
(CH-1)/(CH-2) turned this pass's one flagged structural input (the shared
`G`/`G′` sub-tower, (OC-28)(i)) into a proof. No gap-map status moves;
(OC-8) stays OPEN, reshaped; class uniformity untouched. **Cross-direction
convergence, the wave's third** (after OCON/FRES in the sixth fan-out and
YLOC/BALB in this one): ZNEQ wrote (OC-28)(i) blind to CIRR, flagging it as
an open structural input; CIRR's same-day (CH-2) stage table discharged it
outright. Driver `notes/scripts/w4/zneq.py` (four modes
`--factor`/`--sweep`/`--reject`/`--transfer`, no `--validate`; ~521 s total,
run individually rather than as one foreground call). The code **ZNEQ** was
verified 0-hit as a raw substring across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` at reservation time. No M2 leaf was expected or opened — the target
was an exact-ℚ derivation. **Harness debt recorded, not paid**: `ocon.meet`
now has two consumers, `notes/scripts/README.md` §2 rule 2's own move-down
trigger — the pass may not modify a landed file, so the move is recorded for
a successor, not made (see the README's *Harness debt* list).

**The TWENTY-SECOND direction — AGLU — LANDED 2026-08-19** (fifth and last of
the seventh fan-out's five to land, after CIRR, YLOC, BALB and ZNEQ;
`notes/Pencil-fanout.md` §"Twenty-second direction"), reservation released
into §(K-grid)'s existing registry row: **(GR-73)–(GR-78) and Steps G92–G97
CLAIMED exactly** — the full reservation consumed, nothing returned to the
pool; see the extension of §(K-grid)'s row in the Registry below. Target:
ledger attack (c), AA-glue realizability at `n_hub ≥ 8`. **Verdict: a HIT on
the "not realizable" branch, with one correction to the dispatch's predicted
consequence.** **(GR-73)** pins the slack-0 crossing interface to a rigid
`{2,3}`-degree subgraph and extends the J-charge to arbitrary branch sets.
**(GR-74)** proves the AA-glue configuration at `n_hub = 8` has exactly **one**
combinatorial template, EXHAUSTIVE at all 44 premise-satisfying pairs of all
20 classes, and explains the `n_hub ≤ 6` vacuity combinatorially. **(GR-75)**
proves the configuration and its whole kill residual are **NOT realizable** at
`n_hub = 8`, independently certified by an EXHAUSTIVE scan of the complete
stratum (39 689 shapes, 9 617 854 colourings, 0 instances) that reproduces
(GR-38)'s own `n_hub ≤ 6` headline exactly — so the (GR-38) intersection kill
is a **THEOREM** at `n_hub = 8`, non-vacuously. **(GR-76)** derives a
general-`n` charge forcing `n_hub ≥ 10`, an `n`-free strengthening, and narrows
`n_hub = 10` to exactly **three** counting-satisfiable templates. **(GR-77)
REFUTES the dispatch's predicted consequence**: outright binding laminarity is
**FALSE** at `n_hub = 8` (3 774 crossing same-block binding pairs, EXHAUSTIVE,
against 0 at `n_hub ≤ 6`) — what (GR-75) buys is only the **uncrossing** of the
**maximal** binding family, not laminarity of the family itself. **(GR-78)**
delivers the (GR-15) counting-side target EXHAUSTIVELY over the whole
`n_hub = 8` stratum, no cap (86.9 % of 9 833 022 colourings fully good, every
shape ≥ 10; no g-flank). No gap-map status moves; (GR-15) stays OPEN, modulo
(GR-4′); class uniformity untouched. Driver `notes/scripts/w4/aglu.py` (six
modes `--pool`/`--pin`/`--kill8`/`--lam8`/`--adv`/`--val`, `--lam8` sliced
`--slice i/3` for the F15 budget). The code **AGLU** was verified 0-hit as a
raw substring across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation
time. No M2 leaf was expected or opened — the target was exact-integer
combinatorics.

**Three directions share §(K-grid) this wave**, which the sixth fan-out already
proved safe (GBAL took (GR-49)–(GR-54) / G68–G73 and GLAW (GR-55)–(GR-60) /
G74–G79 concurrently, no rename): the protection is the **disjoint reserved
range**, not the section. **The `GR-`/`G`-step tails have now moved to
(GR-79)+ / Steps G98+** — all three of YLOC, BALB and AGLU have landed, each
consuming its reservation exactly, none returning a remainder (**and
(GR-79)–(GR-96) / Steps G98–G115 are now RESERVED, not free — see the eighth
fan-out's block below**); a direction
that consumes fewer labels than it reserved **returns the remainder to the
tail** in its landing commit, as GBAL's exact-consumption row records. **`CH-`
uses the `Λ`-precedent step scheme**
(*Step CH1* … *Step CH8*, prefixed so it cannot collide with a bare *Step 1*) —
clause 4's diagnosis, not a new minting rule.

No M2 leaf is expected or reserved for any of the five: four targets are exact-ℚ
or combinatorial searches and the fifth is a derivation. A direction that finds
it needs one asks the coordinator rather than minting a path.

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

**Reserved 2026-08-19 for the EIGHTH FAN-OUT — directions GTMPL / GFLOW /
GCOLL / OSCHU / SIGZ** (`notes/Pencil-fanout.md` §"Eighth fan-out"; five
concurrent directions, the third consecutive multidispatch wave). All five
*extend* live sections, so each reservation is a **disjoint sub-range of the
owning section's unclaimed tail** and the owning section stays authoritative:

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GTMPL** | §(K-grid) | **(GR-79)–(GR-84)** — **CLAIMED EXACTLY** (LANDED 2026-08-19) | **G98–G103** — CLAIMED | `w4/gtmpl.py` — committed |
| **GFLOW** | §(K-grid) | **(GR-85)–(GR-90)** — **CLAIMED EXACTLY** (LANDED 2026-08-19) | **G104–G109** — CLAIMED | `w4/gflow.py` — committed |
| **GCOLL** | §(K-grid) | **(GR-91)–(GR-96)** — **CLAIMED EXACTLY** (LANDED 2026-08-19) | **G110–G115** — CLAIMED | `w4/gcoll.py` — committed |
| **OSCHU** | §(K-out) | **(OC-29)–(OC-34)** — **CLAIMED EXACTLY** (LANDED 2026-08-19) | **O25–O30** — CLAIMED | `w4/oschu.py` — committed |
| **SIGZ** | §(K-out) | **(OC-35)–(OC-39)** CLAIMED, **(OC-40) returned UNUSED** (LANDED 2026-08-19) | **O31–O36** — CLAIMED | `w4/sigz.py` — committed |

**Three directions share §(K-grid) and two share §(K-out)** — the sixth and
seventh fan-outs both proved the shared-section shape safe, and the protection
is the **disjoint reserved range**, not the section. On consumption the tails
move to **(GR-97)+ / Steps G116+** and **(OC-41)+ / Steps O37+**; a direction
that consumes fewer labels than it reserved **returns the remainder to the
tail** in its landing commit.

**GCOLL LANDED fifth and last, 2026-08-19, consuming its reservation EXACTLY**
— (GR-91)–(GR-96) / Steps G110–G115, no remainder. **The eighth fan-out is now
COMPLETE**, and all five reservations are released: three consumed exactly
(GTMPL, GFLOW, GCOLL in §(K-grid)), one consumed exactly (OSCHU in §(K-out)),
one returning a single label (SIGZ's (OC-40)). The live tails are **(GR-97)+ /
Steps G116+** and **(OC-40)** then **(OC-41)+ / Steps O37+**. §(K-gcap)/`GC-`
returns unopened a **fourteenth** time; §(K-unif)/`GU-` stays un-minted. One
citation entered the registry's orbit with this landing and was
coordinator-verified against a primary source: **Ján Plesník, *Connectivity of
Regular Graphs and the Existence of 1-Factors*, Matematický časopis 22 (1972),
no. 4, 310–318** (EUDML) — author, title, journal, volume, issue, pages and the
quoted statement all check out; its **graphs-vs-multigraphs** reading is the
named gap, recorded at (GR-94)(iv) and not load-bearing on any figure.

**OSCHU LANDED fourth, 2026-08-19, consuming its reservation EXACTLY** —
(OC-29)–(OC-34) / Steps O25–O30, no remainder. With SIGZ's landing this
**closes §(K-out)'s share of the eighth fan-out**; the section's live tails are
now **(OC-40)** (SIGZ's returned label) then **(OC-41)+ / Steps O37+**. Three
harness items are recorded, not paid, in `notes/scripts/README.md` *Harness
debt*: `ocon.meet` gains a **third** consumer (re-dated), six `zneq` primitives
and `gridwit.tree_triple` each gain a **second**, and **`closure.Gauss`** is
flagged as a *design* item rather than a mechanical move-down — the residual
route needs exact `ℚ(i)`, and `closure` is deliberately the only driver whose
scalars are not `ℚ`. **All three PAID 2026-08-20** (the harness move-down
round; `Gauss` adjudicated down to `exactcore`), each with a re-export from its
old home, so no figure of any eighth-fan-out direction moved.

**SIGZ LANDED third, 2026-08-19, returning one label to the tail** —
(OC-35)–(OC-39) and Steps O31–O36 CLAIMED, **(OC-40) reserved and returned
UNUSED**, so it is available to a later §(K-out) direction (the first
remainder-return of the eighth fan-out; GBAL's exact-consumption row is the
precedent for recording it either way). **(OC-29)–(OC-34) / Steps O25–O30 stay
RESERVED for OSCHU**, still in flight. No new section name was minted: SIGZ
extended §(K-out) exactly as the reservation intended, and the deliberately
un-minted **§(K-sig)/`SG-`** stays un-minted. One **Divergences** candidate is
flagged for the harness: `sigz.topo_reduce` reduces a *subgraph* at
`F`-degree-≥3 vertices, **not** `nogood_subdiv.branch_decomposition`'s `G`-hub
reduction — a genuinely different function, correctly given a different name,
and the absorption is where `P21`'s length-6 path lives.

**GFLOW LANDED second, 2026-08-19, also consuming its reservation EXACTLY** —
(GR-85)–(GR-90) / Steps G104–G109, no remainder. The code and driver basename
were 0-hit verified at reservation; no outgrowth, so §(K-gcap)/`GC-` returns
unopened a **thirteenth** time. **(GR-91)–(GR-96) / Steps G110–G115 stay
RESERVED for GCOLL**, still in flight, and were re-confirmed unused in the
tracked tree at this landing.

**GTMPL LANDED first, 2026-08-19, consuming its reservation EXACTLY** —
(GR-79)–(GR-84) / Steps G98–G103, nothing returned to the tail; §(K-grid)'s
row in the registry below is extended accordingly, and (GR-85)–(GR-96) /
Steps G104–G115 stay **RESERVED** for GFLOW and GCOLL, still in flight. The
code **GTMPL** and the driver basename `gtmpl` were verified 0-hit as raw
substrings at reservation time and the driver is now committed; **no
outgrowth** occurred, so the already-reserved **§(K-gcap) / `GC-`** returns
unopened a **twelfth** time, and **§(K-unif)/`GU-`** stays deliberately
un-minted. One judgement recorded because it is the kind a landing should not
make silently: `gtmpl.py` imports **seven** read-only devices from the sibling
leaf `aglu.py`, none of them catalogued in `notes/scripts/README.md` §1. That
is the documented sibling-import pattern every recent `w4/` leaf uses, so it
is in policy — **but it trips §2 rule 2's move-down trigger**, and the move is
recorded there as a new dated **UNPAID** debt item, exactly as ZNEQ's
`ocon.meet` was one landing earlier.

**Codes: all five verified 0-hit as raw substrings**, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` at reservation time — as were
the five driver basenames (control token `aglu` hit 10 files, so the grep was
live). Each label token was separately verified 0-hit: `(GR-96)`, `(OC-29)`,
`(OC-40)`, *Step O31*, *Step G115* all 0 hits; **`(GR-79)` returned exactly
one hit, this file's own live-tails bookkeeping line** — a bookkeeping hit in
the `GBAL`/`GLAW` sense, not a semantic one.

**Checked 0-hit and NOT chosen**, recorded so they stay checkable without a
re-run: `SIGVOID`, `DEPEV`, `GTEN`, `TEMP10`. **Checked and REJECTED for live
hits**, recorded because clause L5's substring check earned its keep four more
times: **`THETA`** (46 files — the arc's own subject matter, the worst
candidate collision recorded so far), **`SCHUB`** (7 files — "Schubert",
inside the very statement OSCHU attacks), **`SZERO`** (10 files), **`GANCH`**
(2 files — a substring of `GANCHOR`, itself a GDEV-prep checked-not-chosen
entry, so the rejection is *caused by* an earlier prep's bookkeeping, the
same mechanism that took `GBAL` out of the running at GPSA's prep).

**No new section name was minted, and one was deliberately NOT minted.**
**§(K-sig)** was considered as SIGZ's home and **rejected on two independent
grounds**: it is **not 0-hit** (5 hits), and it would sit one character from
the live **§(K-σ)** (route σ) — a reader-side collision the substring check
does not even measure. SIGZ therefore *extends* §(K-out), which is also its
honest home: the hunt is *Step O24*'s own named successor and (OC-24) owns the
`{σ = 0}` dichotomy it tests. **On outgrowth reuse the already-reserved
§(K-gcap) / `GC-`** — returned unopened by GCAP, GUNIF, GEXIST, GORIENT, GDEV,
GADM, GPSA, GDESC, GBAL and GLAW, available a **twelfth** time. **Do not mint
§(K-unif)/`GU-`** — considered twice, deliberately not minted, and this prep
does not revive it.

No M2 leaf is expected or reserved for any of the five: three targets are
combinatorial or exact-ℚ searches and two are derivations. A direction that
finds it needs one asks the coordinator rather than minting a path.

**One clause-L1 reminder, aimed at SIGZ specifically.** A reserved prefix
protects a dispatch from its **siblings**, not from the **existing corpus**.
SIGZ's subject matter is dense in bare tokens the corpus already owns — `σ`,
`s₀`, `θ(3,4,5)`, `P21`, the theta support `{12, 13, 23a, 23b}` — none of
which are its to re-mint. Every label it mints is `OC-`-prefixed inside its
reserved range; everything else is **cited in the qualified form (L3)**.

**Collision recorded 2026-08-20, ADJUDICATED 2026-08-20: RENAMED — direction
GFLOW minted three BARE tokens inside its reservation, and the coordinator
missed it at landing.** GFLOW's (GR-89) named its residual clauses
**`(R1)`**, **`(C1)`** and **`(C2)`**. All three were bare single letters,
which clause L1 forbids and which this file's own diagnosis predicted would
collide — and they did:

- **`(R1)`** had **five** owners: the *Shared dictionary*'s rigid-graph facts
  (R1)–(R5), the opening recon questions R1–R3, `Pencil-strategy.md` §4.6's
  refutations (R1)–(R6), **(GR-64)(R1)** (a sub-item, so qualified already),
  and GFLOW's own (R1).
- **`(C1)`/`(C2)`** collided with `Pencil-strategy.md` §4's candidate
  invariants C1/C2/C3, §`hnoGood'` vacuity's (C1)–(C6), and §(K-slide-cl)'s
  step/claim pair — the same overload clause 4 names.

**Disposition: RENAMED**, per the 2026-08-20 user adjudication
(`notes/Pencil-adjudications.md`): the rename option this record left open for the user was
offered as one of a small option selection, and the user selected **"Rename
to (GR-R1)/(GR-C1)/(GR-C2)"** verbatim, citing the direction-A precedent
(bare `(R1)`/`(R2)` → renamed to `(ANH-R1)`/`(ANH-R2)` at landing, before
they propagated) — GFLOW's were only three commits old, so the same move
was cheap. GFLOW's three tokens are now
**`(GR-R1)`**, **`(GR-C1)`**, **`(GR-C2)`** everywhere in the corpus (verified
0-hit as raw substrings before minting, per (L1)); the qualified-citation form
`§(K-grid) (R1)` / `(C1)` / `(C2)` is retired along with the bare tokens it
existed only to disambiguate.

**Why it got through, for the next prep.** Promoted to the minting rule as
**(L6)** above — a landing-time grep for bare `(X<digit>)` tokens, since the
prefix/step-range reservation check cannot see one minted inside a
reservation for a sub-clause.

## Reserved namespace — probe KBARE-FALSIFY (2026-08-20, **USED — the probe landed**)

**Reserved 2026-08-20 for probe KBARE-FALSIFY**, the first of the two
architecture-testing probes specced and authorized 2026-08-20
(`notes/Pencil-fanout.md` §"Two probes SPECCED and AUTHORIZED 2026-08-20").
Coordinator-set, single dispatch — **not** a fan-out, so this reservation
protects against the *existing corpus* only; there are no siblings in flight.

| what | reserved | note |
|---|---|---|
| section | **§(K-bare-ext)** (`notes/Pencil-informal.md`) | **already registered, currently a stub** — the probe OPENS it; no new section name is minted |
| tag / labels | **`BE-`**, tokens **(BE-1)–(BE-10)** | the registered tag for §(K-bare-ext); no `BE-` token has ever been minted in the pencil doc set |
| steps | ***Steps BE1–BE8*** | first steps the section has had |
| driver | **`notes/scripts/kbare/breakhunt.py`** | new leaf on the `kbare/` model layer |
| M2 leaf | **none** — not expected, not reserved | a probe that finds it needs one asks the coordinator rather than minting a path |

**0-hit verification, at reservation time.** `(BE-1)`, `(BE-2)`, `(BE-10)`,
*Step BE*, `BE1` and `breakhunt` were each verified **0-hit** across this
file's *Files in scope* plus `notes/Pencil-informal-grid.md`. `breakhunt` is
additionally 0-hit as a **raw substring**, case-insensitively, across `*.md`,
`*.tex`, `*.lean`, `*.py`, `*.m2`.

**What was actually minted (2026-08-20, at landing).** §(K-bare-ext) opened
with ***Steps BE1–BE8*** and tokens **(BE-1)–(BE-9)** — `(BE-10)` unused and
therefore **still free** inside this tag. Driver `breakhunt.py` landed at the
reserved path with six modes (`tiers|calc|arith|rzero|locus|c1b`); the two
checked-0-hit alternates `stressgad` and `bexist` were **not** needed and stay
available. No new section name was minted, and no label outside `BE-` was
touched. The namespace is therefore closed as **used, within scope**.

**Two disclosures, recorded rather than smoothed over.**

- **`BE-` is not globally 0-hit** — `notes/Phase23-design.md` carries `BE-1`,
  `BE-2`, `BE-3` and `notes/model-experiment-archive.md` carries `BE-2`/`BE-5`.
  Those files are **outside** this registry's *Files in scope* (a different
  phase's design doc and the frozen experiment log), and `BE-` is the tag the
  §(K-bare-ext) row has carried since 2026-08-05. Not re-minted, not renamed.
- **The code `KBARE-FALSIFY` fails clause L5's raw-substring test on its first
  five characters** — `kbare` hits 68 files, being both the arc's subject
  matter and the script layer's own directory name. This is the shape that got
  `SCHUB` rejected in favour of `OSCHU` at the eighth fan-out's prep, and it is
  recorded here as a **deliberate exception**, not an oversight: the code was
  minted in the authorizing spec (`877fcee7`), the **full token** is 0-hit
  outside its own three bookkeeping files, and the collision is *self-naming*
  rather than accidental — no reader will confuse `KBARE-FALSIFY` with
  `kbare_common`. Renaming it would churn a user-facing, already-authorized
  probe name for no disambiguation gain. **Precedent set narrowly:** an
  exception is available when the substring hit is the dispatch's own declared
  subject and the full code is unique — not merely when a candidate is
  convenient.

**Two checked-and-rejected driver basenames**, recorded so they stay checkable
without a re-run: **`falsify`** (4 live files — HEAD's own spec prose, so the
obvious basename is taken) and **`snap`** (8 files). **Checked 0-hit and NOT
chosen:** `stressgad`, `bexist` — available if the probe needs a second leaf.

**Layering, per `notes/scripts/README.md` §2.** `kbare/` drivers sit
**directly** on the model layer `kbare/kbare_common.py` (plus base
`exactcore.py`); unlike `w4/` they are not a chain. If `breakhunt.py` imports
from a sibling leaf (`danger.py`, `optc.py`, `stress_extra.py`, `gate1.py`,
`gate2.py`) that is the documented sibling-import pattern and **in policy**,
but it **trips §2 rule 2's move-down trigger** — record a new dated **UNPAID**
debt item naming every consumer, and do **not** modify the landed sibling in
the same commit (the `ocon.meet` / `aglu.py` precedents). The one debt item
open on purpose, **`zneq.ledger`**, is not this probe's to disturb.

## Reserved namespace — probe C3-AVOID (2026-08-20, **USED — the probe landed 2026-08-24; §(K-avoid) RELEASED unopened**)

**Reserved 2026-08-20 for probe C3-AVOID**, the second of the two
architecture-testing probes authorized 2026-08-20 (`notes/Pencil-fanout.md`
§"Two probes SPECCED and AUTHORIZED 2026-08-20"). Coordinator-set, single
dispatch. **KBARE-FALSIFY ran first and did NOT moot it** (its T1 hit is a
route finding on the *other* kernel), so this reservation goes live as written.

| what | reserved | note |
|---|---|---|
| section | **§(K-avoid)** | **new**, 0-hit; open it only if the mathematics warrants a workbook section — the spec's default deliverable is a design-pass on `notes/Pencil-strategy.md` §4's C3 entry |
| tag / labels | **`AV-`**, tokens **(AV-1)–(AV-8)** | 0-hit |
| steps | ***Steps AV1–AV6*** | 0-hit |
| driver | **`notes/scripts/w4/avoidgen.py`** — *only if a search is needed* | the spec makes the driver conditional; the question is combinatorial on the **landed** generation theorem (Thm 4.9, Phase 20), so a leaf that consumes `nogood_subdiv`'s combinatorial oracles sits on the `w4/` stack |
| M2 leaf | **none** — not expected, not reserved | purely combinatorial; ask the coordinator rather than minting a path |

**0-hit verification, at reservation time.** `K-avoid`, `AV-`, `(AV-1)`,
`(AV-8)`, `AV1`, `AV6`, *Step AV* and `avoidgen` were each verified **0-hit** as
raw substrings, case-insensitively, across the tracked tree (`.git` and `.lake`
excluded — an unfiltered first pass reported phantom hits for `AV-` and *Step
AV* from build artifacts, which is worth knowing for the next prep: **exclude
`.git`/`.lake` or the check lies to you in the conservative direction**).

**One disclosure, the same shape as KBARE-FALSIFY's.** The code **`C3-AVOID`**
embeds the strategy doc's own **§4 candidate-invariant label `C3`**, so it is
not 0-hit as a raw substring; the **full token** hits exactly 3 files, all of
them its own authorizing bookkeeping (`Pencil-fanout.md`, `Pencil-strategy.md`,
`Phase39.md`). Deliberate and self-naming, exactly like `KBARE-FALSIFY`'s
`kbare`, and it falls inside the narrow exception that reservation recorded —
the substring hit **is** the dispatch's declared subject. Not renamed.

**Checked 0-hit and NOT chosen**, recorded so they stay checkable without a
re-run: `csavoid`, `reduceout`, `sdodge`, `AVD-`. **Checked and rejected for
live hits:** the bare word **`avoid`** (139 files — ordinary English throughout
the corpus, so it can never be a code or basename here) and **`dodge`** (22).

**What was actually minted (2026-08-24, at landing).** Tokens **(AV-1)–(AV-8)
CLAIMED exactly** — the full reservation consumed, nothing returned to the pool
— together with ***Steps AV1–AV6***, all of them **inside
`notes/Pencil-strategy.md` §4.7**, which is their owning section. The driver
landed at the reserved path `notes/scripts/w4/avoidgen.py` with seven modes
(`--supply|--census|--betti|--forced|--avoid|--count|--validate`, plus `--all`).

**The reserved section name §(K-avoid) was NOT opened and RETURNS TO THE POOL
unopened** — the deliberate branch the reservation itself provided for. The
mathematics is about the **generation theorem** (Thm 4.9, Phase 20), not about
kernel (K): it has no *State of (K)* gap-map row, moves no gap-map status, and
putting it in the (K) workbook would have mis-filed it. `notes/Pencil-strategy.md`
§4 is the canonical home for the C3 option, so §4.7 is where its gate's pricing
belongs. **`§(K-avoid)` and a *fresh* `AV-` tag stay available** for any future
kernel-side avoidance question — but the `AV-` **tokens (AV-1)–(AV-8) are spent**
and a successor mints (AV-9) onward under clause (L4)'s no-renaming rule.

**One consequence for the registry, executed here:** because the labels live in
`notes/Pencil-strategy.md` rather than a workbook, the **strategy registry table
below carries the `AV-` row** — not the (K) workbook table. That is the first
time this registry has had to route a reservation's labels to the strategy
document, and it is the general rule: **a namespace is registered where its
labels actually land, not where they were reserved.**

## Reserved namespace — direction GFLIP (2026-08-25, **USED — the direction landed the same day, returning two labels and a step to the tail**)

**Reserved 2026-08-25 for the single direction GFLIP** (ordinal 30, the arc's
thirty-eighth direction; `notes/Pencil-fanout.md` §"GFLIP"), the standing
research pick made at the 2026-08-25 check-in (single direction, cheapest
first → **(GR-R1)**, §8.1's cheapest board entry). One direction, no siblings
— the reservation still binds because it protects the *next* dispatch's prep
from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GFLIP** | §(K-grid) — **extends**, no new section | **(GR-97)–(GR-101)** | **G116–G120** | `w4/gflip.py` (conditional — see the spec) |

The reservation was the head of §(K-grid)'s unclaimed tail (declared
**(GR-97)+ / Steps G116+** at the eighth fan-out's release above).
**Consumed 2026-08-25 at landing: (GR-97)–(GR-99) and Steps G116–G119
CLAIMED; (GR-100), (GR-101) and Step G120 RETURNED UNUSED** — the live tail
is therefore **(GR-100)+ / Step G120+** (SIGZ's (OC-40) precedent for a
remainder return). The registry's §(K-grid) row above is extended
accordingly; the (L6) landing-time bare-token grep ran clean on the merged
draft (every mint `GR-`-prefixed inside the reservation; sub-items are
roman/paren numerals of their own labels, never bare tokens). The target token **(GR-R1)** is
GFLOW's landed clause — already minted, renamed by the 2026-08-20
adjudication, and **not** in this reservation; GFLIP *cites* it and mints its
own results at (GR-97)+.

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded
(the unfiltered-grep lesson of C3-AVOID's prep), control token `aglu` live at
14 files. Label tokens `(GR-101)`, *Step G116*, *Step G120* each 0-hit;
`(GR-97)` hits only this file's own live-tails bookkeeping line (the
`(GR-79)` precedent). **Checked 0-hit and NOT chosen:** `GRONE`, `GMAJ`,
`MAJFL`. **Checked and REJECTED for live hits:** **`GFEAS`** (26 files — a
case-insensitive substring of `PencilNondegFeasible`, the worst rejected
candidate since `THETA`; recorded because "feasible" is exactly the concept a
(GR-R1) direction reaches for, so the next prep will be tempted by it too).
**On outgrowth reuse the already-reserved §(K-gcap) / `GC-`** (returned
unopened fourteen times); **do not mint §(K-unif)/`GU-`**.

## Reserved namespace — direction GCHEAP (2026-08-25, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-25 for the single direction GCHEAP** (ordinal 31, the
arc's thirty-ninth direction; `notes/Pencil-fanout.md` §"GCHEAP"), the
standing research pick made at the second 2026-08-25 check-in (single
direction, cheapest first → **(GR-C2)**, §8.1's cheapest board entry with
(GR-R1) struck by GFLIP). One direction, no siblings — the reservation still
binds because it protects the *next* dispatch's prep from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GCHEAP** | §(K-grid) — **extends**, no new section | **(GR-100)–(GR-104)** | **G120–G124** | `w4/gcheap.py` (conditional — see the spec) |

The reservation is the head of §(K-grid)'s unclaimed tail (declared
**(GR-100)+ / Step G120+** at GFLIP's landing above).
**Consumed 2026-08-25 at landing: (GR-100)–(GR-104) and Steps G120–G124 ALL
CLAIMED, none returned** — the live tail is therefore **(GR-105)+ /
Step G125+**. The registry's §(K-grid) row above is extended accordingly;
the (L6) landing-time bare-token grep ran clean on the merged draft (every
mint `GR-`-prefixed inside the reservation; sub-items are roman/paren
numerals of their own labels, never bare tokens).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `aglu` live at 14 files. Label tokens `(GR-104)`,
`(GR-105)`, *Step G124*, *Step G125* each 0-hit; `(GR-100)` and *Step G120*
hit only the GFLIP reservation's live-tails bookkeeping above and its landing
record (the `(GR-97)` precedent). **Checked 0-hit and NOT chosen:** `GCTWO`,
`GRESID`, `CHEAPB`, `GBRANCH`. `GSEL` was already REJECTED at an earlier prep
for naming the generic mechanism; **`GCHEAP` names the theorem's content** —
the *cheap branch* is *Step G108*(iv)'s own defined term, the object (GR-C2)
selects. The target token **(GR-C2)** is GFLOW's landed clause (renamed at
the 2026-08-20 adjudication) — already minted, **not** in this reservation;
GCHEAP *cites* it and mints its own results at (GR-100)+.

## Reserved namespace — direction OQRANK (2026-08-25, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-25 for the single direction OQRANK** (ordinal 32, the
arc's fortieth direction; `notes/Pencil-fanout.md` §"OQRANK"), the standing
research pick made at the third 2026-08-25 check-in via two option
selections (recon-first → the eighth strategy-only pass's board re-rank
`f72cbb35`; then its rank-1 front-runner, the ℚ(i) eigen-block leg of
§(K-out) *Step O29*). One direction, no siblings — the reservation still
binds because it protects the *next* dispatch's prep from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **OQRANK** | §(K-out) — **extends**, no new section | **(OC-40)–(OC-44)** | **O37–O41** | `w4/oqrank.py` (conditional — see the spec) |

The reservation is the head of §(K-out)'s unclaimed tail (declared
**(OC-40)** — SIGZ's returned label — **then (OC-41)+ / Steps O37+** at the
eighth fan-out's close above).
**Consumed 2026-08-25 at landing: (OC-40)–(OC-44) and Steps O37–O41 ALL
CLAIMED, none returned** — the live tail is therefore **(OC-45)+ /
Step O42+**. The registry's §(K-out) row below is extended accordingly; the
(L6) landing-time bare-token grep ran clean on the merged draft (every mint
`OC-`-prefixed inside the reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `aglu` live at 14 files. Label tokens `(OC-44)`,
`(OC-45)`, *Step O41*, *Step O42* each 0-hit; `(OC-40)`/`(OC-41)`/*Step
O37* hit only the live-tails bookkeeping lines (the `(GR-97)` precedent).
**Checked 0-hit and NOT chosen:** `QDBLK`, `EIGB`, `STARB`. **Checked and
REJECTED for live hits:** `QRANK` (7 files). `EIGB`/`STARB` name the
*mechanism* (the eigen-block split — the `GSEL` rejection reason);
**`OQRANK` names the theorem's content** — the rank of the pitch form
`Q|_D`, §(K-out)'s own object. The target tokens **(OC-33)**/(a₁) are
OSCHU's landed labels — already minted, **not** in this reservation; OQRANK
*cites* them and mints its own results at (OC-40)+.

## Reserved namespace — direction GPRICE (2026-08-25, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-25 for the single direction GPRICE** (ordinal 33, the
arc's forty-first direction; `notes/Pencil-fanout.md` §"GPRICE"), the
standing research pick made at the fourth 2026-08-25 check-in (single
direction, front-runner-first → **(GR-104)(i)**, the 2026-08-25 re-rank's
rank 2 and its highest unlanded entry, rank 1 having landed as OQRANK the
same day). One direction, no siblings — the reservation still binds because
it protects the *next* dispatch's prep from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GPRICE** | §(K-grid) — **extends**, no new section | **(GR-105)–(GR-109)** | **G125–G129** | `w4/gprice.py` (conditional — see the spec) |

The reservation is the head of §(K-grid)'s unclaimed tail (declared
**(GR-105)+ / Step G125+** at GCHEAP's landing above).
**Consumed 2026-08-25 at landing: (GR-105)–(GR-109) and Steps G125–G129 ALL
CLAIMED, none returned** — the live tail is therefore **(GR-110)+ /
Step G130+**. The registry's §(K-grid) row above is extended accordingly;
the (L6) landing-time bare-token grep ran clean on the merged draft (every
mint `GR-`-prefixed inside the reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `aglu` live at 14 files. Label tokens `(GR-110)`
and *Step G130* each 0-hit; `(GR-105)` and *Step G125* hit only GCHEAP's
live-tails bookkeeping above (the `(GR-97)` precedent). **Checked 0-hit and
NOT chosen:** `GSTALL`, `GTAX`, `GPFORM` — the stall and the tax name
(GR-102)/(GR-103)'s landed *instruments*, not the target (the `GSEL`
rejection reason). **`GPRICE` names the theorem's content** — the *price*
`f(p + χ_γ) − f(p)` of a majority-side flip, the quantity (GR-104)(i)
bounds. The target token **(GR-104)** is GCHEAP's landed label — already
minted, **not** in this reservation; GPRICE *cites* it and mints its own
results at (GR-105)+.

## Reserved namespace — direction GBLAW (2026-08-25, **USED — the direction landed 2026-08-26; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-25 for the single direction GBLAW** (ordinal 34, the
arc's forty-second direction; `notes/Pencil-fanout.md` §"GBLAW"), the
standing research pick made at the fifth 2026-08-25 check-in (single
direction, front-runner-first → **(GR-108)**, the balance law — GPRICE's
residual #1 and the head of *Step G129*'s successor order, the re-rank's
ranks 1 and 2 both having landed the same day as OQRANK / GPRICE). One
direction, no siblings — the reservation still binds because it protects
the *next* dispatch's prep from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GBLAW** | §(K-grid) — **extends**, no new section | **(GR-110)–(GR-114)** | **G130–G134** | `w4/gblaw.py` (conditional — see the spec) |

The reservation is the head of §(K-grid)'s unclaimed tail (declared
**(GR-110)+ / Step G130+** at GPRICE's landing above).
**Consumed 2026-08-26 at landing: (GR-110)–(GR-114) and Steps G130–G134 ALL
CLAIMED, none returned** — the live tail is therefore **(GR-115)+ /
Step G135+**. The registry's §(K-grid) row above is extended accordingly;
the (L6) landing-time bare-token grep ran clean on the merged draft (every
mint `GR-`-prefixed inside the reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `aglu` live at 14 files. Label tokens
`(GR-111)`–`(GR-115)` and *Steps G131–G135* each 0-hit; `(GR-110)` and
*Step G130* hit only GPRICE's live-tails bookkeeping above (the `(GR-97)`
precedent). **Checked 0-hit and NOT chosen:** `GXCH`, `GEXCH` — they name
the pinned proof *mechanism* (the exchange between maximum reversal sets),
not the target (the `GSEL`/`GSTALL` rejection reason); `GRLAW` — reads as a
`(GR-…)` label token, inviting exactly the bare-token ambiguity this
registry exists to prevent. **`GBLAW` names the theorem's content** — the
*balance law* (GR-108), the statement the direction proves or refutes. The
target token **(GR-108)** is GPRICE's landed label — already minted, **not**
in this reservation; GBLAW *cites* it and mints its own results at (GR-110)+.

## Reserved namespace — direction GXESC (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction GXESC** (ordinal 35, the
arc's forty-third direction; `notes/Pencil-fanout.md` §"GXESC"), the
standing research pick made at the sixth check-in of the 2026-08-25/26
session (single direction, front-runner-first → **existential escape**,
(GR-112)(v)'s hypothesis — GBLAW's sharpened residual #1 and the head of
*Step G134*'s successor order). One direction, no siblings — the
reservation still binds because it protects the *next* dispatch's prep
from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GXESC** | §(K-grid) — **extends**, no new section | **(GR-115)–(GR-119)** | **G135–G139** | `w4/gxesc.py` (conditional — see the spec) |

The reservation is the head of §(K-grid)'s unclaimed tail (declared
**(GR-115)+ / Step G135+** at GBLAW's landing above).
**Consumed 2026-08-26 at landing: (GR-115)–(GR-119) and Steps G135–G139 ALL
CLAIMED, none returned** — the live tail is therefore **(GR-120)+ /
Step G140+**. The registry's §(K-grid) row above is extended accordingly;
the (L6) landing-time bare-token grep ran clean on the merged draft (every
mint `GR-`-prefixed inside the reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `aglu` live at 14 files. Label tokens
`(GR-116)`–`(GR-120)` and *Steps G136–G140* each 0-hit; `(GR-115)` and
*Step G135* hit only GBLAW's live-tails bookkeeping above (the `(GR-97)`
precedent). **Checked and NOT chosen:** `GESC` — **collides** (2 files,
raw-substring); `GWALK`, `GFINE` — 0-hit but they name the *instrument*
(the walk, the fine-move class), not the target (the `GSEL`/`GXCH`
rejection reason). **`GXESC` names the theorem's content** — the
e**X**istential **ESC**ape statement itself, (GR-112)(v)'s hypothesis. The
source tokens **(GR-108)/(GR-112)** are landed labels — already minted,
**not** in this reservation; GXESC *cites* them and mints its own results
at (GR-115)+.

## Reserved namespace — direction GHWIT (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction GHWIT** (ordinal 36, the
arc's forty-fourth direction; `notes/Pencil-fanout.md` §"GHWIT"), the
standing research pick made at the seventh check-in of the 2026-08-26
session (single direction, front-runner-first → the **half-witness
clause**, (GR-117)(iii) — GXESC's reshaped residual and the head of
*Step G139*'s successor order). One direction, no siblings — the
reservation still binds because it protects the *next* dispatch's prep
from this one's labels.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GHWIT** | §(K-grid) — **extends**, no new section | **(GR-120)–(GR-124)** | **G140–G144** | `w4/ghwit.py` (conditional — see the spec) |

The reservation is the head of §(K-grid)'s unclaimed tail (declared
**(GR-120)+ / Step G140+** at GXESC's landing above).
**Consumed 2026-08-26 at landing: (GR-120)–(GR-124) and Steps G140–G144 ALL
CLAIMED, none returned** — the live tail is therefore **(GR-125)+ /
Step G145+**. The registry's §(K-grid) row above is extended accordingly;
the (L6) landing-time bare-token grep ran clean on the merged draft (every
mint `GR-`-prefixed inside the reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `aglu` live at 14 files (`gxesc` live at 8, the
freshest control). Label tokens `(GR-121)`–`(GR-125)` and *Steps
G141–G145* each 0-hit; `(GR-120)` and *Step G140* hit only GXESC's
live-tails bookkeeping above (the `(GR-97)`/`(GR-115)` precedent).
**Checked and NOT chosen:** `GHALF` — **collides** (1 file: `ghalf`, a
local variable in `notes/scripts/w4/gxesc.py`, a raw-substring hit and so
barred); `GHRES` — 0-hit but it names one *disjunct of the conclusion*
(half-residency), not the clause (the `GWALK`/`GFINE` rejection reason).
**`GHWIT` names the theorem's content** — the **H**alf-**WIT**ness clause
itself, the corpus's own name for (GR-117)(iii). The source tokens
**(GR-104)/(GR-115)/(GR-117)** are landed labels — already minted, **not**
in this reservation; GHWIT *cites* them and mints its own results at
(GR-120)+.

## Reserved namespace — direction GMINM (2026-08-26, **USED — the direction landed the same day; (GR-125)–(GR-128) and Steps G145–G148 consumed, (GR-129) and Step G149 RETURNED to the tail**)

**Reserved 2026-08-26 for the single direction GMINM** (ordinal 37, the
arc's forty-fifth direction; `notes/Pencil-fanout.md` §"GMINM"), the first
direction picked under the **2026-08-26 widened delegation** (the
coordinator chooses; `notes/Pencil-adjudications.md`). Target: the
**`min_M` reading** of (GR-104)(i), GHWIT's residual #2.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GMINM** | §(K-grid) — **extends**, no new section | **(GR-125)–(GR-129)** | **G145–G149** | `w4/gminm.py` (conditional — see the spec) |

The reservation is the head of §(K-grid)'s unclaimed tail (declared
**(GR-125)+ / Step G145+** at GHWIT's landing above).
**Consumed 2026-08-26 at landing: (GR-125)–(GR-128) and Steps G145–G148;
(GR-129) and Step G149 were NOT needed and are RETURNED** — the live tail is
therefore **(GR-129)+ / Step G149+**. The (L6) landing-time bare-token grep
ran clean on the merged draft (every mint `GR-`-prefixed inside the
reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `ghwit` live at 7 files. `(GR-126)`–`(GR-130)` and
*Steps G146–G150* each 0-hit; `(GR-125)` and *Step G145* hit only GHWIT's
live-tails bookkeeping above (the `(GR-97)`/`(GR-115)`/`(GR-120)`
precedent). **Checked and NOT chosen:** `GANCH` — **collides** (2 files,
raw-substring, on "anchor"); `GMREAD` — 0-hit but it names the *act of
reading* rather than the object. **`GMINM` names the statement's content**
— the **min-over-M** form of the price gap.

## Reserved namespace — direction OGEOM (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction OGEOM** (ordinal 38, the
arc's forty-sixth direction; `notes/Pencil-fanout.md` §"OGEOM"), the second
pick under the 2026-08-26 widened delegation and the first to leave
§(K-grid). Target: **the geometric route to a disproof** —
`notes/Pencil-strategy.md` §8.5's one open row.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **OGEOM** | §(K-out) — **extends**, no new section | **(OC-45)–(OC-49)** | **O42–O46** | `w4/ogeom.py` (conditional — see the spec) |

The reservation is the head of §(K-out)'s unclaimed tail (declared
**(OC-45)+ / Step O42+** at OQRANK's landing above).
**Consumed 2026-08-26 at landing: (OC-45)–(OC-49) and Steps O42–O46 ALL
CLAIMED, none returned** — the live tail is therefore **(OC-50)+ /
Step O47+**. The (L6) landing-time bare-token grep ran clean on the merged
draft (every mint `OC-`-prefixed inside the reservation).

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `gminm` live at 7 files. `(OC-46)`–`(OC-50)` and
*Steps O43–O47* each 0-hit; `(OC-45)` and *Step O42* hit only OQRANK's
live-tails bookkeeping above (the `(GR-97)`/`(GR-115)`/`(GR-120)`
precedent). **Checked and NOT chosen:** `OKIRCH`, `OFORCE` — both 0-hit, but
each names one candidate *mechanism* (the Kirchhoff drop, the forcing)
rather than the route, and the route is the target (the `GWALK`/`GFINE`
rejection reason). **`OGEOM` names the route's content** — the **geometric**
half of the disproof question, the half (OC-37) left standing when it killed
the counting half.

## Reserved namespace — direction OWALL (2026-09-02, **USED — the direction landed the same day; all six labels and all five steps consumed, none returned**)

**Reserved 2026-09-02 for the single direction OWALL** (ordinal 70;
`notes/Pencil-fanout.md` §"OWALL"), a **draft-only** dispatch run concurrently
with one committing dispatch in `notes/Pencil-informal-grid.md` §(K-grid) and a
second draft-only one in §(K-bare-ext) — `RESEARCH-ARC.md` §2's serial-landing
pattern at a **three-way** concurrency, the widest exercised outside a prepared
fan-out, and it landed with zero label collisions.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **OWALL** | §(K-out) — **extends**, no new section | **(OC-50)–(OC-55)** | **O47–O51** | `w4/owall.py` |

The reservation is the head of §(K-out)'s unclaimed tail (declared
**(OC-50)+ / Step O47+** at OGEOM's landing above).
**Consumed 2026-09-02 at landing: (OC-50)–(OC-55) and Steps O47–O51 ALL
CLAIMED, none returned** — the live tail is therefore **(OC-56)+ /
Step O52+**. The (L6) landing-time bare-token grep ran clean on the returned
draft: every mint is `OC-`-prefixed inside the reservation, and the only bare
token the draft introduces, **(OW)** (the reduced target's *statement name*, not
an `(X<digit>)` label), was verified 0-hit before use. The bare tokens the draft
*cites* — `(C6)`, `(I4)`, `(L5)`, `(L6)`, `(F20)` — are all grandfathered and all
written L3-qualified (`§(K-slide-comb) (C6)`, `§(K-ind) (I4)`).

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2`: `OWALL` 0-hit, `owall` 0-hit, `POOL-OW` 0-hit, `(OW)`
0-hit. `(OC-51)`–`(OC-57)` and *Steps O48–O52* each 0-hit; `(OC-50)` and
*Step O47* hit **only** this file's own OGEOM live-tails bookkeeping above (the
`(GR-97)`/`(OC-45)` precedent). **`OWALL` names the target's own object** — the
**wall**-avoiding certificate-colouring existence question of (OC-44)(iii). The
target tokens **(OC-42)** and **(OC-44)(iii)** are OQRANK's landed labels,
already minted and **not** in this reservation; OWALL *cites* them and mints its
own results at (OC-50)+. **No new section name and no new tag were considered or
reserved** — the argument stays inside §(K-out)'s own family, so nothing returns
to the pool.

## Reserved namespace — direction BATTAIN (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction BATTAIN** (ordinal 39, the
arc's forty-seventh direction; `notes/Pencil-fanout.md` §"BATTAIN"), the
third pick under the 2026-08-26 widened delegation and **the arc's FIRST
direction ever aimed at `hbareSplit`** — 46 directions on `hK`, zero on
(K-bare), the imbalance the gap map has called *"open, nothing being
developed"* since 2026-07-30.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BATTAIN** | §(K-bare-ext) — **extends**, no new section | **(BE-10)–(BE-14)** | **BE9–BE13** | `w4/battain.py` (conditional — see the spec) |

The reservation is the head of §(K-bare-ext)'s unclaimed tail: KBARE-FALSIFY
consumed *Steps BE1–BE8* and **(BE-1)–(BE-9)**, leaving **(BE-10) unused and
returned**, so the tail is **(BE-10)+ / Step BE9+**. At landing, record what
was consumed, return any remainder, and flip this header to **USED**.

**Code and basename verified 0-hit** as raw substrings, case-insensitively,
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`
excluded, control token `ogeom` live at 7 files. `(BE-11)`–`(BE-15)` and
*Steps BE9–BE14* each 0-hit; `(BE-10)` hits only KBARE-FALSIFY's own
reservation record above, which is exactly the bookkeeping that declared it
unused (the `(GR-97)`/`(OC-45)` precedent). **Checked and NOT chosen:**
`BDIRECT` — **collides** hard (26 files, raw-substring, on "direct");
`BSEED` — 0-hit but it names what the shape **avoids** (the seed) rather
than what it delivers. **`BATTAIN` names the target's content** — direct
**attain**ment of `HasPencilRealization K 3 G` on the habitat.

## Reserved namespace — direction BZAVOID (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction BZAVOID** (ordinal 40, the
arc's forty-eighth direction; `notes/Pencil-fanout.md` §"BZAVOID"), the
**first pick this arc has ever made by USER OPTION SELECTION between slice
shapes of a landed direction's own offer** — BATTAIN's `def₂ = def₃`
proof-of-concept was declined in favour of **(BE-14) at the full statement**.
It is the direct successor of BATTAIN inside the same section.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BZAVOID** | §(K-bare-ext) — **extends**, no new section | **(BE-15)–(BE-19)** | **BE14–BE18** | `w4/bzavoid.py` (conditional — see the spec) |

The reservation is the head of §(K-bare-ext)'s unclaimed tail: KBARE-FALSIFY
consumed *Steps BE1–BE8* and **(BE-1)–(BE-9)**, BATTAIN consumed
*Steps BE9–BE13* and **(BE-10)–(BE-14)** with **nothing returned**, so the tail
was **(BE-15)+ / Step BE14+**.

**Consumed at landing (2026-08-26), NOTHING RETURNED:** *Steps BE14–BE18* and
**(BE-15)–(BE-19)** — (BE-15) the generalized forced-class cap and the
falsification arm's cap-free closure, (BE-16) the planar-atom molecular
identification plus the dimension count's structural impossibility, (BE-17) the
landed `G²` apparatus closed with a measured witness, (BE-18) the 1-cut
composition, (BE-19) the verdict label. Driver `w4/bzavoid.py` **shipped**
(eight modes). The tail is now **(BE-20)+ / Step BE19+**.

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded. `BZAVOID`, `(BE-16)`–
`(BE-20)`, *Step BE14*/*Steps BE14* each 0-hit; **`(BE-15)` hits exactly one
line — BATTAIN's own reservation record above**, which is the bookkeeping that
declared it unclaimed (the `(GR-97)`/`(OC-45)` precedent, and the same shape as
BATTAIN's own `(BE-10)` note). **Checked and NOT chosen:** `BZLOC` — 0-hit but
collides *semantically* with the landed direction `YLOC`, whose "loc" means
localization, not locus; `BGENZ` — 0-hit but names the *method* (genericity)
rather than the statement, and the method is exactly what is undecided.
**`BZAVOID` names the target's content** — `Y°` **avoid**ing the rank-drop
locus **Z**(G), on the **b**are half.

## Reserved namespace — direction ZSHEAR (2026-08-26, **USED — the direction landed the same day; all six labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction ZSHEAR** (ordinal 41, the arc's
forty-ninth direction; `notes/Pencil-fanout.md` §"ZSHEAR"), dispatched
**concurrently with BZAVOID as the session's side line**, on unprompted user
initiative. It is the **first direction ever produced by
`notes/Pencil-strategy.md` §9's external-technique shelf**, and the first to
mint a section from an outside idea source rather than from an internal
residual.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **ZSHEAR** | **§(K-shear)** — **NEW section**, `notes/Pencil-informal.md` | **(SH-1)–(SH-6)** | **SH1–SH5** | `w4/zshear.py` (expected — the adversarial pre-test is measured) |

**Consumed at landing (2026-08-26), NOTHING RETURNED:** *Steps SH1–SH5* and
**(SH-1)–(SH-6)** — (SH-1) the shear-is-a-translation identity, (SH-2) `Q` as
the shear group's own invariant, (SH-3) the guarded bed, (SH-4) the equivariance
theorem, (SH-5) the per-body repair decided, (SH-6) the general dichotomy.
**§(K-shear) was MINTED** (as the reservation anticipated for a death as much as
a hit) and driver `w4/zshear.py` **shipped** (four modes). The tail is
**(SH-7)+ / Step SH6+**.

**Non-collision with the concurrent BZAVOID is structural, not negotiated:**
the two sit in **different workbook sections** with **disjoint tags** (`BE-`
vs `SH-`), which is exactly the independence RESEARCH-ARC.md's *Candidates*
item asks a concurrent pair to have. Neither may edit a shared file; the
coordinator lands them **serially, one commit each** (RESEARCH-ARC §2).

**Code, section name, tag and basename verified 0-hit** as raw substrings
across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded:
`ZSHEAR`, `K-shear`, **`SH-` itself** (globally 0-hit — a cleaner tag than
`BE-`, which the KBARE-FALSIFY reservation had to scope-qualify against
`notes/Phase23-design.md` and the frozen experiment log), `(SH-1)`–`(SH-7)`,
*Step SH1*/*Steps SH1*. **`SH-` is the tag and `ZSHEAR` names the content** —
the **Z**heng-sourced Witt **shear**. If (ZH-1) dies, §(K-shear) is minted
anyway: a recorded death with its exact reason is the deliverable, and an
unminted section would leave the shelf row unresolvable.

## Reserved namespace — direction BINDUC (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the direction BINDUC** (ordinal 42, the arc's fiftieth
direction; `notes/Pencil-fanout.md` §"BINDUC"), the max-impact half of the
session's second concurrent pair, picked under a **user-supplied criterion**
(max impact on proving or disproving `PencilPair K 3 G`). It is the direct
successor of BZAVOID inside the same section, carrying the induction (BE-18)
opened.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BINDUC** | §(K-bare-ext) — **extends**, no new section | **(BE-20)–(BE-24)** | **BE19–BE23** | `w4/binduc.py` (expected — the 2-cut `def₃` law is enumerable) |

The reservation is the head of §(K-bare-ext)'s unclaimed tail: KBARE-FALSIFY
consumed *Steps BE1–BE8* / **(BE-1)–(BE-9)**, BATTAIN *Steps BE9–BE13* /
**(BE-10)–(BE-14)**, BZAVOID *Steps BE14–BE18* / **(BE-15)–(BE-19)** — all three
returning nothing — so the tail was **(BE-20)+ / Step BE19+**.

**Consumed at landing (2026-08-26), NOTHING RETURNED:** *Steps BE19–BE23* and
**(BE-20)–(BE-24)** — (BE-20) the free base (3-connected ⇒ `def₂ = 0`) and its
contrapositive, (BE-21) the exact 2-cut `def₃` law refuting BZAVOID's `− 6`,
(BE-22) the rank-half composition criterion with its free cases and located
obstruction, (BE-23) the assembled induction plus the hub-plane construction and
the generalized forcing mechanism, (BE-24) the classification. Driver
`w4/binduc.py` **shipped** (eight modes). The tail is **(BE-25)+ / Step BE24+**.
**Four consecutive directions have now consumed this namespace with nothing
returned** — KBARE-FALSIFY, BATTAIN, BZAVOID, BINDUC — which is worth noting for
the next reservation: `BE-` is the arc's most heavily-worked tag.

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded. `BINDUC`, `(BE-21)`–
`(BE-25)` and *Step BE19*'s neighbours each 0-hit; **`(BE-20)` and `Step BE19`
hit only this file's own tail-bookkeeping** from the BZAVOID landing, which is
exactly the record that declared them unclaimed (the `(GR-97)`/`(OC-45)` and
`(BE-10)`/`(BE-15)` precedents — third occurrence of that benign shape in this
namespace). **Checked and NOT chosen:** `BTWOCUT` — 0-hit but it names only the
*first slice*, and the direction's target is the whole induction plus its base;
`BSTARS` — 0-hit but ambiguous against the `closedNbhd`/`closed star` vocabulary
already dense in §(K-bare-ext). **`BINDUC` names the target's content** — the
**b**are-half direct-attainment **induc**tion.

## Reserved namespace — direction ZJACOB (2026-08-26, **USED — the direction landed the same day; all six labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the direction ZJACOB** (ordinal 43, the arc's
fifty-first direction; `notes/Pencil-fanout.md` §"ZJACOB"), the **Zheng line's
second direction** and the second section this arc mints from an external idea
source. Dispatched concurrently with BINDUC.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **ZJACOB** | **§(K-jac)** — **NEW section**, `notes/Pencil-informal.md` | **(JC-1)–(JC-6)** | **JC1–JC5** | `w4/zjacob.py` (conditional) + `m2/zjacob.m2` (only if a symbolic leaf is genuinely needed) |

**Consumed at landing (2026-08-26), NOTHING RETURNED:** *Steps JC1–JC5* and
**(JC-1)–(JC-6)** — (JC-1) the polynomial presentation and its zero-section
Jacobian, (JC-2) the stratification equivalence that kills the route, (JC-3) the
classical bounds' direction and input-dependence, (JC-4) the criterion's
identical blindness to the pure-condition half, (JC-5) the faithful-hence-useless
re-encoding, (JC-6) the conservation law. **§(K-jac) was MINTED** and driver
`w4/zjacob.py` **shipped** (four modes); **no `m2/zjacob.m2`**, and the reason is
recorded as mathematical rather than budgetary. The tail is
**(JC-7)+ / Step JC6+**.

**Non-collision with the concurrent BINDUC is structural, not negotiated:**
different workbook sections, disjoint tags (`BE-` vs `JC-`), and — unlike the
BZAVOID/ZSHEAR pair — also disjoint *subject matter*, since BINDUC owns
(BE-14)/`hbareSplit` and ZJACOB is barred from it. Neither may edit a shared
file; the coordinator lands them **serially, one commit each** (RESEARCH-ARC §2).

**Code, section name, tag and basename verified 0-hit** as raw substrings across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded:
`ZJACOB`, `K-jac`, **`JC-` itself**, `(JC-1)`–`(JC-7)`, *Step JC1*/*Steps JC1*.
**`JC-` is the tag and `ZJACOB` names the content** — the **Z**heng-sourced
**Jacob**ian/singular-locus route. The `Z` prefix is now this arc's convention
for a §9-shelf direction (`ZSHEAR` the first), which keeps the externally-sourced
sections visibly grouped; note it is **not** a claim about the source's
correctness, only about where the idea came from.

## Reserved namespace — direction BTWOCUT (2026-08-26, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-26 for the single direction BTWOCUT** (ordinal 44, the arc's
fifty-second direction; `notes/Pencil-fanout.md` §"BTWOCUT"), the **fifth
consecutive direction to work this namespace** and the first whose selection was
**forced rather than ranked**: BINDUC proved (BE-14)'s decomposition exhaustive
and closed every layer but one, so the strengthened 2-cut composition lemma is
the only candidate, and proving it proves (BE-14).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BTWOCUT** | §(K-bare-ext) — **extends**, no new section | **(BE-25)–(BE-29)** | **BE24–BE28** | `w4/btwocut.py` (expected — extend `binduc.py`'s `twocut`/`rank2`/`ear` by read-only import) |

The reservation is the head of §(K-bare-ext)'s unclaimed tail, which four
consecutive directions have consumed with **nothing returned**: KBARE-FALSIFY
*Steps BE1–BE8* / **(BE-1)–(BE-9)**, BATTAIN *Steps BE9–BE13* /
**(BE-10)–(BE-14)**, BZAVOID *Steps BE14–BE18* / **(BE-15)–(BE-19)**, BINDUC
*Steps BE19–BE23* / **(BE-20)–(BE-24)** — so the tail is
**(BE-25)+ / Step BE24+**.

**Consumed at landing (2026-08-26), NOTHING RETURNED:** *Steps BE24–BE28* and
**(BE-25)–(BE-29)** — (BE-25) the pinned strengthened statement with the
simultaneity worry proved vacuous and the S-all/S-mark decision, (BE-26) the ear
misses cleared as a constructor artifact, (BE-27) the general-position half
counted, (BE-28) the cross-pair closure gap, (BE-29) the obstruction hunt and the
concurrent-plane rung. Driver `w4/btwocut.py` **shipped** (eight modes). The tail
is **(BE-30)+ / Step BE29+**. **Five consecutive directions have now consumed this
namespace with nothing returned.**

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded. `(BE-26)`–`(BE-30)` each
0-hit; **`(BE-25)`, `Step BE24` and `BTWOCUT` hit only this file's own
bookkeeping** — the first two the BINDUC landing's tail record, the third
BINDUC's *"Checked and NOT chosen"* line. Fourth occurrence of that benign shape
in this namespace, and worth recording for a reason beyond bookkeeping:
**`BTWOCUT` was rejected for BINDUC on the stated ground that it "names only the
first slice, and the direction's target is the whole induction plus its base"** —
BINDUC then *closed* the base and the rest, so that slice **is** now the whole
target and the rejection reason has expired. The code is taken here on its
original merit. **Checked and NOT chosen:** `BGLUE` — 0-hit, but "glue" is
already the name of `bzavoid.py`'s 1-cut mode and would read as that mode's
successor rather than as the 2-cut lemma.


## Reserved namespace — direction BIMAGE (2026-08-27, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-27 for the single direction BIMAGE** (ordinal 45, the arc's
fifty-third direction; `notes/Pencil-fanout.md` §"BIMAGE"), the **sixth
consecutive direction to work this namespace** and the second in a row whose
selection was **forced rather than ranked**: BTWOCUT reduced the strengthened
2-cut lemma to a single geometric sentence and ranked its own successors, and
this direction takes successor (1) in BTWOCUT's own recommended restriction (the
ear case first).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BIMAGE** | §(K-bare-ext) — **extends**, no new section | **(BE-30)–(BE-34)** | **BE29–BE33** | `w4/bimage.py` (expected — extend `btwocut.py`, and through it `binduc.py`, by read-only import) |

The reservation is the head of §(K-bare-ext)'s unclaimed tail, which **five**
consecutive directions have consumed with **nothing returned**: KBARE-FALSIFY
*Steps BE1–BE8* / **(BE-1)–(BE-9)**, BATTAIN *Steps BE9–BE13* /
**(BE-10)–(BE-14)**, BZAVOID *Steps BE14–BE18* / **(BE-15)–(BE-19)**, BINDUC
*Steps BE19–BE23* / **(BE-20)–(BE-24)**, BTWOCUT *Steps BE24–BE28* /
**(BE-25)–(BE-29)** — so the tail is **(BE-30)+ / Step BE29+**, exactly as
BTWOCUT's landing record states.

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded: `BIMAGE`, `bimage`,
`(BE-31)`–`(BE-34)` and `Step BE30`–`Step BE33` each **0-hit**; `(BE-30)` and
`Step BE29` hit **only this file's own bookkeeping** (BTWOCUT's landing record
naming the free tail) — the fifth occurrence of that benign shape in this
namespace. **Checked and NOT chosen:** `BGENPOS` — 0-hit, but it names only the
*general-position* half, which (BE-27)(ii) has already refuted as a *reading*;
`BSPAN` — 0-hit, but it presumes the coordinator's untested hinge-line-span
hypothesis is the answer, which is exactly the framing RESEARCH-ARC §7 forbids a
spec from inheriting. `BIMAGE` is BTWOCUT's own word for the residue (*"the
image statement"*).

**Consumed at landing (2026-08-27), NOTHING RETURNED:** *Steps BE29–BE33* and
**(BE-30)–(BE-34)** — (BE-30) the ear's image as a chain on the Klein quadric
plus the three confinement laws, (BE-31) the series/parallel recursion and the
refutation of the path-intersection bound, (BE-32) the three merge-inequality
theorems and the `δ ≤ dist` sweep, (BE-33) the α-plane escape lemma and the
three-mechanism classification, (BE-34) the image at real graphs, the hunt and
the F27 escalation. Driver `w4/bimage.py` **shipped** (nine modes). The tail is
**(BE-35)+ / Step BE34+**. **Six consecutive directions have now consumed this
namespace with nothing returned** — and the gap-map row it feeds was
**recomputed rather than appended to** at this landing (1 370 → 1 402 words
against a 1 600 combined cap, after folding the KBARE-FALSIFY and BATTAIN
clauses), so a **seventh** landing here needs a fuller recompute first, not
another clause.


## Reserved namespace — direction BEARCASE (2026-08-27, **USED — the direction landed the same day; four of five labels and four of five steps consumed, (BE-39) and *Step BE38* RETURNED**)

**Reserved 2026-08-27 for the single direction BEARCASE** (ordinal 46, the arc's
fifty-fourth direction; `notes/Pencil-fanout.md` §"BEARCASE"), the **seventh
consecutive direction to work this namespace** and the **third in a row whose
selection was forced rather than ranked**: BIMAGE reduced the ear case to exactly
two open items and stated that together they prove it.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BEARCASE** | §(K-bare-ext) — **extends**, no new section | **(BE-35)–(BE-39)** | **BE34–BE38** | `w4/bearcase.py` (expected — extend `bimage.py`, and through it `btwocut`/`binduc`, by read-only import) |

The reservation is the head of §(K-bare-ext)'s unclaimed tail, which **six**
consecutive directions have consumed with **nothing returned**: KBARE-FALSIFY
*BE1–BE8*, BATTAIN *BE9–BE13*, BZAVOID *BE14–BE18*, BINDUC *BE19–BE23*, BTWOCUT
*BE24–BE28*, BIMAGE *BE29–BE33* — so the tail is **(BE-35)+ / Step BE34+**,
exactly as BIMAGE's landing record states.

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded: `BEARCASE`, `bearcase`,
`(BE-36)`–`(BE-39)` and `Step BE35`–`Step BE38` each **0-hit**; `(BE-35)` and
`Step BE34` hit **only this file's own bookkeeping** (BIMAGE's landing record
naming the free tail) — the sixth occurrence of that benign shape here.
**Checked and NOT chosen:** `BESCAPE` — it would collide *semantically* with
"the escape" (`hK`'s `≢ 0` uniformity kernel), which is a different object in a
different section, and clause L3 would need qualifying on every use; `BNONCON`
and `BGREEDY` — both 0-hit, but each names only **one** of the direction's two
jobs, and the point of pairing (α) with (β) is that together they close the ear
case.

**Gap-map note carried forward from the BIMAGE landing:** the `(K-bare)` row
stands at **1 402 / 1 600** words after a recompute. A seventh landing here needs
a **fuller recompute first** — folding the remaining dated clauses into a
current-state paragraph — not another appended clause.

**Consumed at landing (2026-08-27):** *Steps BE34–BE37* and **(BE-35)–(BE-38)** —
(BE-35) the 2-step lemma, the ear's last step, the end-pair lemma, the
reordering-and-slide and the `m ≤ 2` corners; (BE-36) the refutation of (β) as
stated; (BE-37) the quantifier collapse, the reduction and the named residue;
(BE-38) (β) for real pieces, the transfer, the independent-sampler falsification
arm and the classification. **(BE-39) and *Step BE38* are RETURNED UNCONSUMED** —
**the first return in this namespace after six directions of nothing returned**,
so the tail is **(BE-39)+ / Step BE38+**. Driver `w4/bearcase.py` **shipped**
(eight modes).

**The fuller recompute the note above called for was DONE at this landing**, not
deferred again: the `(K-bare)` status cell was rewritten as a **current-state
paragraph** rather than a stack of dated *"Since Steps…"* clauses, going
**1 409 → 1 130 words** *while absorbing a full direction* — 470 words of
headroom against the 1 600 cap, and a reader cost of ~2 550 tokens against
~3 076. Label preservation was checked by **scripted set-diff**: 28 tokens
dropped, **every one verified present in the workbook body first**, and the four
that are *current-state* rather than historical figures (**`Y° ⊄ Z(G)`**,
`Z(G)`, `HasPencilRealization`, `dim Y° ≤ dim Z`) were **restored** into the new
cell. The steps column now reads **BE1–BE37**, and the cell states explicitly
that per-direction history for *Steps BE14–BE33* is the workbook's, not the
cell's.


## Reserved namespace — direction BEARFULL (2026-08-27, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-27 for the single direction BEARFULL** (ordinal 47, the arc's
fifty-fifth direction; `notes/Pencil-fanout.md` §"BEARFULL"), the **eighth
consecutive direction to work this namespace**. Jobs 1–2 are forced (BEARCASE's
successors (1) and (2), the ear case's last two items); **job 3 is not** — it is
a coordinator-raised routing question, and the spec lifts BEARCASE's own
*"do not re-open S-all vs S-mark"* bar **for that job only**, with the reason
stated.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BEARFULL** | §(K-bare-ext) — **extends**, no new section | **(BE-39)–(BE-43)** | **BE38–BE42** | `w4/bearfull.py` (expected — extend `bearcase.py`, and through it `bimage`/`btwocut`/`binduc`, by read-only import) |

The reservation opens at **(BE-39) / Step BE38**, which BEARCASE **returned
unconsumed** — the first return in this namespace after six directions of nothing
returned, so for once the tail was not simply the head of the previous
reservation's remainder.

**Code and basename verified 0-hit** as raw substrings across `*.md`, `*.tex`,
`*.lean`, `*.py`, `*.m2` with `.git`/`.lake` excluded: `BEARFULL`, `bearfull`,
`(BE-40)`–`(BE-43)` and `Step BE39`–`Step BE42` each **0-hit** — and, unusually,
so are `(BE-39)` and `Step BE38`, because BEARCASE's landing record returned them
rather than consuming them. **Checked and NOT chosen:** `BFORCED` (0-hit, but it
names only job 1) and `BEARDONE` (0-hit, but it **presumes the outcome** — the
ear case is not done until jobs 1 and 2 both close, and a code that asserts the
verdict is the framing RESEARCH-ARC §7 forbids).

**Gap-map note:** the `(K-bare)` row was **fully recomputed** at the BEARCASE
landing (current-state paragraph, **1 130 / 1 600** words, 470 of headroom), so
this landing may fold its clause in normally. The next *full* recompute is not
due until that headroom is spent.

**Consumed at landing (2026-08-27), NOTHING RETURNED:** *Steps BE38–BE42* and
**(BE-39)–(BE-43)** — (BE-39) the quotient sparsity law and the join lemma,
(BE-40) the short-cycle law, (BE-41) (BE-32)(+) proved at 96.2 % with its exact
boundary, (BE-42) (b2) as a corollary of (b1), (BE-43) the ear-decomposition
routing verdict. Driver `w4/bearfull.py` **shipped** (eight modes). The tail is
**(BE-44)+ / Step BE43+**.

**The headroom the note above allotted is SPENT, and the lesson is recorded
rather than just the number.** The coordinator's first draft of this landing's
gap-map edit was a **374-word dated clause** — *"Since Steps BE38–BE42 (BEARFULL,
…)"* — i.e. **exactly the changelog shape the BEARCASE recompute had just removed
from this row**, and it took the cell to 1 504 / 1 600. It was discarded and the
content **INTEGRATED** into the existing current-state sentences instead (the
merge-theorem sentence became the short-cycle law; the residue sentence absorbed
the 96.2 % result; the routing verdict joined the closed-routes list), landing at
**1 402 / 1 600**. **A recompute does not hold if the next landing appends** —
integrate, and treat "may fold its clause in normally" as licence to *edit
sentences*, not to add one.

## Reserved namespace — direction RESGRID (2026-08-28, **USED — the direction landed the same day; §(K-res) opened with (RS-1)–(RS-6) and *Steps RS1–RS10* consumed, (RS-7)–(RS-12) RETURNED, the M2 leaf never needed**)

**Reserved 2026-08-28 for the single direction RESGRID** (ordinal 48, the arc's
fifty-sixth direction; `notes/Pencil-fanout.md` §"RESGRID") — the **(K-res)
scoping slice**, a user-selected item (2026-08-26) deferred four rounds and
committed to this slot at the BEARFULL prep. It is the **first direction ever
aimed at the (K-res) habitat**, which has been a *bar* in eight consecutive
specs, and it **breaks the eight-direction run in §(K-bare-ext)**. Coordinator-set,
single dispatch — **not** a fan-out, so this reservation protects against the
*existing corpus* only; there are no siblings in flight.

| what | reserved | note |
|---|---|---|
| section | **§(K-res)**, new, in `notes/Pencil-informal-grid.md` | that workbook owns §(K-grid), so the audit sits beside what it audits |
| tag / labels | **`RS-`**, tokens **(RS-1)–(RS-12)** | no `RS-` token has ever been minted in the pencil doc set |
| steps | ***Steps RS1–RS10*** | first steps the section has had |
| driver | **`notes/scripts/w4/resgrid.py`** — **optional** | job 1 is an audit and may need no code; job 3 reuses `gridcol`/`gridwit`/`gexist` + `widened`/`saferes` by read-only import |
| M2 leaf | **none** — not expected, not reserved | a direction that finds it needs one asks the coordinator rather than minting a path |

**0-hit verification, at reservation time.** `RESGRID`, `resgrid`, `§(K-res)`,
`(RS-1)`, `(RS-2)`, `(RS-9)`, `RS1` and *`Step RS`* were each verified **0-hit**
as raw substrings, case-insensitively, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2`.

**The deliberate near-miss, recorded because clause L1 still binds inside a
reservation.** `(K-res)` **alone** is a live **habitat name** with **139**
existing hits across the corpus; only `§(K-res)` is free. So every citation of
the new section must carry its `§` — the same shape as §(K-bare-ext) sitting
beside the `(K-bare)` gap-map row, which has held without incident. A bare
`(K-res)` in the new section's prose still means *the habitat*, as it does
everywhere else.

**Checked and NOT chosen.** Extending the **`GR-` tail** ((GR-129)+, *Step
G149*+): it is the mechanically obvious choice and it is wrong here, because it
would mix **two habitats** inside one label family — the registry's rule is to
qualify a cross-section citation, not to merge the families. And **`RESPORT`**
(0-hit): it names the hoped-for answer, which is exactly the framing
`RESEARCH-ARC.md` §7 forbids in a spec whose whole job is to test a coordinator
hypothesis.

**Gap-map note — the two rows this verdict can land in have very different
headroom, and the difference is measured, not guessed.** The natural home is
**(K-tight)**'s row, which carries the umbrella claim under test (*"one uniform
gap serves both"*): **297 / 800** status words, ~500 of headroom, so a clause
folds in normally. But **(K-grid)**'s *close-it* cell — where (GR-15) is stated,
and therefore where any qualification of its quantifier belongs — sits at
**959 / 985**: **twenty-six words of headroom**. If the verdict touches it,
**integrate into the existing sentences, do not append a dated clause** (the
BEARFULL lesson recorded above), and if that cannot be done, recompute with an
**explicit target** that leaves room for the landings already queued behind it
(`RESEARCH-ARC.md` §6) and verify label preservation **by a scripted set-diff,
never by eye**. Bump a cap only with a dated one-line reason.

## Reserved namespace — direction RPOOL (2026-09-03, **USED — the direction landed the same day; (RS-11)–(RS-15) and *Steps RS11–RS16* consumed, (RS-16)–(RS-18) RETURNED, no M2 leaf needed**)

**Reserved 2026-09-03 for the single direction RPOOL** (arc ordinal 75;
`notes/Pencil-fanout.md` §"RPOOL") — the `§(K-res)/(RS-5)` row's own **two
cheap items**, the 255-residual pool sweep and the flank hunt. It is the
**second** direction ever aimed at the (K-res) habitat (RESGRID, 2026-08-28,
was the first) and the first dispatched under the **2026-09-03 declines-are-
not-locks** directive: the declined **wave** is not re-litigated here.
Coordinator-set, one half of a concurrent pair (sibling on
(BE-14)/(K-bare-ext) — **no shared section, label family or driver**).

| what | reserved | note |
|---|---|---|
| section | **§(K-res)**, existing, in `notes/Pencil-informal-grid.md` | the row's own section; the direction extends it rather than opening one |
| tag / labels | **`RS-`**, tokens **(RS-11)–(RS-18)** | (RS-7)–(RS-12) were RETURNED by RESGRID, so (RS-11)/(RS-12) were free to re-reserve; **a returned token is back in the pool, and re-reserving one is not a rename (clause L4 untouched)** |
| steps | ***Steps RS11–RS18*** | RS1–RS10 consumed by RESGRID |
| driver | **`notes/scripts/w4/rpool.py`** | imports `resgrid.py` read-only for the floor's ingredients; third consumer of `saferes.prime()`'s pool list (harness debt) |
| M2 leaf | **none** — not expected, not reserved | the whole question is exact-ℚ linear algebra over an enumerated colouring space |

**0-hit verification, at reservation time and re-verified as the dispatch's
first action.** `RPOOL`, `rpool`, `w4/rpool.py`, `(RS-11)`–`(RS-18)` and
*`Step RS11`*/*`RS18`* were each verified **0-hit** as raw substrings across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2`. The two live `RS-` hits found at
re-verification were the RESGRID reservation's own *"(RS-7)–(RS-12)
returned"* records in this file and `notes/Pencil-fanout.md` — records of a
**return**, not of a use, so they are not collisions; the re-reservation is
noted in the table row above so a later reader does not read the two
sentences as contradicting each other.

**What the direction consumed, at landing.** (RS-11) the per-block floor law,
(RS-12) the pool census, (RS-13) the refutation of (RS-5) with the witness
`R20`, (RS-14) the mechanism, (RS-15) the covering law — *Steps RS11–RS16*
(six steps for five labels: RS16 is the verdict step, which the section's own
convention gives no label, per clause L2 *never label a step*).
**(RS-16)–(RS-18) and *Steps RS17–RS18* return to the pool unused.**


## Reserved namespace — direction BSHARP (2026-08-28, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-28 for the single direction BSHARP** (ordinal 49, the arc's
fifty-seventh direction; `notes/Pencil-fanout.md` §"BSHARP") — BEARFULL's
successor (1), the ear case's **last (β) clause**: prove `ρ̄₁ ∩ Π_u = 0`, which
by the proved (BE-42)(ii) carries **both** (b1) and (b2). Coordinator-set,
single dispatch — **not** a fan-out, so this reservation protects against the
*existing corpus* only; there are no siblings in flight. It is §(K-bare-ext)'s
**first** direction since RESGRID broke the namespace's eight-direction run.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSHARP** | §(K-bare-ext) — **extends**, no new section | **(BE-44)–(BE-48)** | **BE43–BE47** | `w4/bsharp.py` (expected — extend `bearfull.py`, and through it `bearcase`/`bimage`/`btwocut`/`binduc`, by read-only import) |

The reservation opens at **(BE-44) / Step BE43**, **exactly the tail BEARFULL
declared** at its landing — the ordinary case, unlike BEARFULL's own opening on
a returned token.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2`: `BSHARP`, `bsharp`, `(BE-45)`, `(BE-48)` and *`Step BE47`* each
**0-hit**. **`(BE-44)` and *`Step BE43`* each have TWO hits, and both were
opened and confirmed to be the tail POINTERS** — `notes/Pencil-fanout.md`'s
BEARFULL reservation line and this file's line 1993 (*"The tail is (BE-44)+ /
Step BE43+"*) — **not consumed labels**. Recorded because a bare hit count
would otherwise read as a collision; clause L1 binds inside a reservation, and
the check is the whole corpus, not just the siblings.

**Checked and NOT chosen.** **`BZERO`** (0-hit): it names the answer as if
settled, and worse, the answer it names is **false at path pieces** —
(BE-38)(i) proves `dim(ρ̄₁ ∩ Π_u) = 1` there, sharp — so the honest target is a
**case split**, and a code asserting `0` would prime exactly the framing
`RESEARCH-ARC.md` §7 forbids. **`BFLAG`** (0-hit): it names the apparatus (the
point-plane flag `Π_u = p_u ∧ π_u`) rather than the question.

**Gap-map note.** The `(K-bare)` row was fully recomputed at the BEARCASE
landing and stood at **1 402 / 1 600** words after BEARFULL integrated its
clause rather than appending one — **198 words of headroom** for this landing,
enough to integrate and not enough to append a dated clause.

**What the BSHARP landing actually spent (2026-08-28).** The (BE-42) sentence
was **rewritten in place** to carry the whole (BE-44)–(BE-48) result — `+196`
words gross — and the landing **paid part of its own way** by compressing the
(BE-43) ear-route clause (`−30` words: the *why* of the chord-free argument
moves to the workbook, which owns it), leaving the row at **1 568 / 1 600**.
**Nothing was appended**, and no label was dropped: the row's label set grew by
exactly (BE-44)–(BE-48) and its step range moved BE1–BE42 → BE1–BE47.
**32 words of headroom remain, which is not enough for the next landing** —
the successor named by (BE-47) (the window identity) should **recompute the
row against an explicit target** rather than bump the cap, and the natural
target is *Steps BE1–BE13*'s option-C / BATTAIN history, every claim of which
is settled and cited by label. Verify label preservation by a **scripted
set-diff, never by eye**.

**RECOMPUTE DONE 2026-08-28** (docs-only, no direction). The row was rewritten as a
**current-state paragraph** against the explicit target above rather than extended:
**1 568 → 1 200 / 1 600 words** (10 368 → 8 157 characters; reader cost ~3 456 → ~2 719
tokens), leaving **400 words of headroom** for the three landings already queued on this
namespace — the window identity ((BE-47)'s successor 1), the spread step, and (b3). The cap
was **not** bumped. *Steps BE1–BE13*'s option-C / BATTAIN history collapsed to one
label-cited sentence, and the two surviving dated *"Since Steps …"* clauses (BEARCASE,
BSHARP) became current-state headers. **Scripted set-diff, run before the write:** **zero**
`(XX-n)` labels dropped and zero added (59 distinct, counting roman sub-items); **18 code
spans** dropped, each verified body-present in §(K-bare-ext) or still present as text
elsewhere in the row — and `HasPencilRealization`, one of the four the BEARCASE recompute
had deliberately restored, was **restored again** because the diff caught it. The next
landing has room to integrate a clause; the one after that asks this question again.

## Reserved namespace — direction BRULE (2026-08-28, **USED — the direction landed the same day; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-28 for the single direction BRULE** (ordinal 50, the arc's
fifty-eighth direction; `notes/Pencil-fanout.md` §"BRULE") — **(b3)**, the one
clause of the ear case's (β) side that has **never been attacked**.
Coordinator-set, single dispatch — **not** a fan-out, so this reservation
protects against the *existing corpus* only; there are no siblings in flight.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BRULE** | §(K-bare-ext) — **extends**, no new section | **(BE-49)–(BE-53)** | **BE48–BE52** | `w4/brule.py` (expected — extend `bsharp.py`, and through it the `bear*`/`bimage`/`btwocut`/`binduc` chain, by read-only import) |

The reservation opens at **(BE-49) / Step BE48**, exactly the tail BSHARP
declared; BSHARP consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2`: `BRULE`, `brule`, `(BE-49)`, `(BE-53)`, *`Step BE48`* and
*`Step BE52`* each **0-hit** — unlike BSHARP's opening, no token here needed the
tail-pointer carve-out. **Checked and NOT chosen:** `BOPP` (0-hit, but it
abbreviates "opposite" to something that reads as a typo beside `(b3)`) and
`BRULING` (0-hit, but it names the ruling rather than the clause under test).

**Gap-map note — the row was RECOMPUTED at `5ae57257` and this landing has
room.** `(K-bare)` sits at **1 200 / 1 600** words, **400 of headroom** (was
32), with **zero labels dropped** by scripted set-diff and one span
(`HasPencilRealization`) restored that a by-eye pass would have lost. So this
landing folds in **normally** — but *integrate into the current-state
sentences*, never append a dated *"Since Steps …"* clause: that is the shape
three consecutive landings have had to undo, and the 400 words are meant to
carry the window identity and the spread step behind this direction, not one
landing.

**Landed 2026-08-28.** The reservation is **fully consumed**: labels
**(BE-49)–(BE-53)** and *Steps BE48–BE52*, **nothing returned**. §(K-bare-ext)
gained one continuation section (`## §(K-bare-ext) — continuation (direction
BRULE)`), and the `(K-bare)/(K-bare-ext)` gap-map row was **integrated, not
appended to** — its (β)-side sentences rewritten as current state, the row
moving 1 200 → 1 442 of 1 600 words (the requested shape; no dated *"Since
Steps …"* clause was added) and its step range BE1–BE47 → **BE1–BE52**. One
**F12** hunk landed at the originating prose, (BE-37)(ii) itself, where the
corrected inference is stated. The tail a successor opens at is **(BE-54) /
*Step BE53***.

## Reserved namespace — direction BWIN (2026-08-28, **USED — landed 2026-08-29; all five labels and all five steps consumed, none returned**)

**Reserved 2026-08-28 for the single direction BWIN** (ordinal 51, the arc's
fifty-ninth direction; `notes/Pencil-fanout.md` §"BWIN") — BSHARP's **window
identity as a CLASS statement**, the **last open item of the ear case's (β)
side** after BRULE proved (b3) and (BE-50)(iii) proved it disjoint from the
window. Coordinator-set, single dispatch — **not** a fan-out, so this
reservation protects against the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BWIN** | §(K-bare-ext) — **extends**, no new section | **(BE-54)–(BE-58)** | **BE53–BE57** | `w4/bwin.py` (expected — extend `brule.py`, and through it `bsharp` and the rest of the chain, by read-only import) |

The reservation opens at **(BE-54) / Step BE53**, exactly the tail BRULE
declared; BRULE consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2`: `BWIN`, `bwin`, `(BE-58)` and *`Step BE57`* each **0-hit**.
**`(BE-54)` and *`Step BE53`* have ONE hit each, and both were opened and
confirmed to be the tail POINTER** BRULE wrote at its landing — not consumed
labels. Recorded because a bare hit count would read as a collision; the same
carve-out BSHARP's reservation needed, for the same structural reason.

**Checked and NOT chosen:** `BMID` (0-hit, but it names *the middle*, and job
2's whole point is that the identity may **not** be a condition on the middle
alone — `Z` is defined from `u` and `v`. A code asserting otherwise would prime
the answer, which is the framing `RESEARCH-ARC.md` §7 forbids).

**Gap-map note.** `(K-bare)` sits at **1 442 / 1 600** words. The `5ae57257`
recompute bought 400 and BRULE spent 242 of them, so this landing **integrates
into the current-state sentences** — and if it is large, the recompute target is
*Steps BE14–BE33*'s per-direction history (BZAVOID/BINDUC/BTWOCUT/BIMAGE), which
the row **already declares** to be the workbook's rather than the cell's.

**Landed 2026-08-29.** The reservation is **fully consumed**: labels
**(BE-54)–(BE-58)** and *Steps BE53–BE57*, **nothing returned**. §(K-bare-ext)
gained one continuation section (`## §(K-bare-ext) — continuation (direction
BWIN)`), and the `(K-bare)/(K-bare-ext)` gap-map row was **integrated, not
appended to** — the window sentence (u23) and the ear-case header (u16)
rewritten as current state, the row moving 1 442 → **1 550 / 1 600** words
(no dated *"Since Steps …"* clause; the *Steps BE14–BE33* recompute target was
**not needed** at +108 words) and its step range BE1–BE52 → **BE1–BE57**.
Three **F12** hunks landed at originating prose: (BE-47)(iii) (marked PROVED
as a class statement), BSHARP's *What would change this* successor bullet
(the *"misses `Z`"* form refined at source, no measurement changed), and
BRULE's successor bullet (marked LANDED). The tail a successor opens at is
**(BE-59) / *Step BE58***. ~~the row's next landing must recompute (50 words of
headroom)~~ — **STALE, corrected 2026-09-01 at the BRNODE prep:** the
`442c9363` recompute (the BWIN-required one, landed the same day as this block
was written) took the row 1 550 → **1 162** words, so the recompute is **already
paid** and the next landing has **431 words of headroom**, not 50.

## Reserved namespace — direction BRNODE (2026-09-01, **USED — landed 2026-09-01; all five labels and all five steps consumed, none returned**)

**Reserved 2026-09-01 for the single direction BRNODE** (ordinal 52, the arc's
sixtieth direction; `notes/Pencil-fanout.md` §"BRNODE") — the **internal
R-node**, (BE-31)(ii)'s named residue and the step from *ear* to *general
piece*, **user-selected at the 2026-08-29 twelfth check-in**. Coordinator-set,
single dispatch — **not** a fan-out, so this reservation protects against the
*existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BRNODE** | §(K-bare-ext) — **extends**, no new section | **(BE-59)–(BE-63)** | **BE58–BE62** | `w4/brnode.py` (expected — extend `bwin.py`, and through it `brule`/`bsharp` and the rest of the chain, by read-only import) |

The reservation opens at **(BE-59) / Step BE58**, exactly the tail BWIN
declared; BWIN consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` with `.git`/`.lake` excluded: `BRNODE`, `brnode`, `(BE-60)`,
`(BE-61)`, `(BE-62)`, `(BE-63)` and *`Step BE62`* each **0-hit**. **`(BE-59)`
and *`Step BE58`* have ONE hit each — both on this file's line 2216, and both
opened and confirmed to be the tail POINTER** BWIN wrote at its landing, not
consumed labels. Recorded because a bare hit count would read as a collision;
the same carve-out BSHARP's and BWIN's reservations needed, for the same
structural reason.

**Checked and NOT chosen:** `BFLOW` and `BSPQR` — both 0-hit, but each names a
**candidate answer** rather than the object. `BFLOW` would prime the
coordinator's own annihilator-flow duality (job 2's spec labels it *to be
tested, not inherited*), and `BSPQR` would prime an SPQR-tree recursion, which
is exactly the shape job 1's sharp sub-question is written to be able to kill.
Priming the answer is the framing `RESEARCH-ARC.md` §7 forbids. `BGEN` was
rejected on the (L5) substring rule (2 hits).

**(L6) reminder for the landing.** The reservation check above verifies the
*prefix* and the *step range* only; it structurally cannot see a bare
`(X<digit>)` token minted **inside** the reservation for a sub-clause. Run the
landing-time bare-token grep on the returned draft.

**Landed 2026-09-01.** The direction consumed exactly its reservation:
**(BE-59)–(BE-63)** and *Steps BE58–BE62*, **nothing returned**. §(K-bare-ext)
gained one continuation section (`## §(K-bare-ext) — continuation (direction
BRNODE)`), and the `(K-bare)/(K-bare-ext)` gap-map row was **integrated, not
appended to** — the (BE-31) recursion sentence rewritten as current state, the
row moving 1 162 → **1 298 / 1 600** words (no dated *"Since Steps …"*
clause; 302 words of headroom remain) and its step range BE1–BE57 →
**BE1–BE62**. One **F12** hunk landed at originating prose: (BE-31)(ii)'s
*"What has no such description is the R-node"* (marked LANDED — the
decorated-skeleton law closes it). The landing-time (L6) bare-token grep found
**no** new bare token — every minted token is (BE-59)–(BE-63) with roman
sub-clauses. The tail a successor opens at is **(BE-64) / *Step BE63***.


## Reserved namespace — direction BDECOR (2026-09-01, **LANDED**)

**Reserved 2026-09-01 for the single direction BDECOR** (ordinal 53, the arc's
sixty-first direction; `notes/Pencil-fanout.md` §"BDECOR") — the
**achievable-decorations class statement** ((BE-62)(iii)), BRNODE's successor (1),
taken only after the coordinator re-ran the F26 consumer trace. Coordinator-set,
single dispatch — **not** a fan-out, so this reservation protects against the
*existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BDECOR** | §(K-bare-ext) — **extends**, no new section | **(BE-64)–(BE-68)** | **BE63–BE67** | `w4/bdecor.py` (expected — extend `brnode.py`, and through it `bwin`/`brule`/`bsharp` and the rest of the chain, by read-only import) |

The reservation opens at **(BE-64) / Step BE63**, exactly the tail BRNODE
declared; BRNODE consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` with `.git`/`.lake` excluded: `BDECOR`, `bdecor`, `(BE-68)` and
*`Step BE67`* each **0-hit**. **`(BE-64)` and *`Step BE63`* have TWO hits each —
`notes/Pencil-fanout.md:7789` and this file's line 2271 — and both were opened
and confirmed to be the tail POINTER** BRNODE wrote, not consumed labels. Two
rather than one because BRNODE records its tail in both places; recorded because
a bare hit count would read as a collision, the same carve-out BSHARP's, BWIN's
and BRNODE's reservations needed.

**Checked and NOT chosen:** `BTHETA` — 0-hit, but it names the **theta child**,
which is only the spec's *first* sub-case of job 1. A code that pins the scoping
would prime it, and job 1 explicitly may find theta children the wrong cut
(the coordinator's own job-2 hypothesis is that they are *free*, in which case
the direction's content is elsewhere entirely). `RESEARCH-ARC.md` §7.

**(L6) reminder for the landing.** The reservation check above verifies the
*prefix* and the *step range* only; it structurally cannot see a bare
`(X<digit>)` token minted **inside** the reservation for a sub-clause. Run the
landing-time bare-token grep on the returned draft.

**Landed 2026-09-01.** The direction consumed exactly its reservation:
**(BE-64)–(BE-68)** and *Steps BE63–BE67*, **nothing returned**. §(K-bare-ext)
gained one continuation section (`## §(K-bare-ext) — continuation (direction
BDECOR)`), and the `(K-bare)/(K-bare-ext)` gap-map row was **integrated, not
appended to** — (BE-62)'s residue sentence rewritten as current state, the row
moving 1 298 → **1 501 / 1 600** words (no dated *"Since Steps …"* clause; 99
words of headroom remain) and its step range BE1–BE62 → **BE1–BE67**. **Two**
**F12** hunks landed at originating prose, both inside (BE-62)(iii) (BRNODE
section): *"open in general"* marked CLOSED, and the *"achievable by pencil
configurations"* quantifier sharpened to the **attaining** locus. The
landing-time (L6) bare-token grep over the new section found **no** new bare
token — every minted token is (BE-64)–(BE-68) with roman sub-clauses; the only
`(X<digit>)`-shaped strings are the dispatch-log friction ids `(F12)`/`(F27)`,
already in arc-wide use. The tail a successor opens at is **(BE-69) / *Step
BE68***.


## Reserved namespace — direction BPEEL (2026-09-01, **USED — the direction landed**)

**Reserved 2026-09-01 for the single direction BPEEL** (ordinal 54, the arc's
sixty-second direction; `notes/Pencil-fanout.md` §"BPEEL") — **half (B)'s class
statement** ((BE-67)(iii)), BDECOR's residue (1), taken after the coordinator
re-ran the F26 consumer trace. Coordinator-set, single dispatch — **not** a
fan-out, so this reservation protects against the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BPEEL** | §(K-bare-ext) — **extends**, no new section | **(BE-69)–(BE-73)** | **BE68–BE72** | `w4/bpeel.py` (expected — extend `bdecor.py`, and through it `brnode`/`bwin`/`brule`/`bsharp` and the rest of the chain, by read-only import) |

The reservation opens at **(BE-69) / Step BE68**, exactly the tail BDECOR
declared; BDECOR consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` with `.git`/`.lake` excluded: `BPEEL`, `bpeel`, `(BE-73)` and
*`Step BE72`* each **0-hit**. **`(BE-69)` has TWO hits and *`Step BE68`* ONE** —
`notes/Pencil-fanout.md:8090` and this file's line 2323 — **all opened and
confirmed to be the tail POINTER** BDECOR wrote, not consumed labels; the same
carve-out the four preceding reservations needed.

**Checked and NOT chosen:** `BCLASS` — rejected on the **(L5) substring rule**
(3 hits as `BCLASS`, 19 as `bclass`, the latter inside driver identifiers), which
is exactly the failure (L5)'s substring half exists to catch. `BCHART` and
`BFIBRE` are both 0-hit but name the *method's frame* rather than the question's
site, and job 3 explicitly may find that the chart is **not** where the argument
lives — `RESEARCH-ARC.md` §7.

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the
returned draft; the reservation check sees prefixes and step ranges only.

**Landed 2026-09-01.** The direction consumed exactly its reservation:
**(BE-69)–(BE-73)** and *Steps BE68–BE72*, **nothing returned**. §(K-bare-ext)
gained one continuation section (`## §(K-bare-ext) — continuation (direction
BPEEL)`), and the `(K-bare)/(K-bare-ext)` gap-map row was **RECOMPUTED to a
target, not merely kept under the cap** (F21) — *Steps BE14–BE33*'s
per-direction history rewritten as current state, the row moving 1 511 →
**1 228 / 1 600** words (headroom 89 → **372**) and its step range BE1–BE67 →
**BE1–BE73**. **Label preservation was verified by scripted set-diff, never by
eye**: **0 of 56** labels dropped and **5** added; eight *clause* qualifiers
(`(BE-22)(iii)`, `(BE-31)(i)`, `(BE-34)(ii)`, `(BE-37)(i)`, `(BE-38)(i)`,
`(BE-38)(ii)`, `(BE-42)(ii)`, `(BE-42)(iii)`) were folded into their parent
label, each verified **body-present** by the same script (6–26 occurrences
each). **One F12 hunk** landed at originating prose: (BE-66)(iv)'s *"the only
landed mechanism ... needs `x ∼ y`"* clause, marked **FALSE as stated** with its
conclusion re-derived.

**The (L6) landing-time bare-token grep CAUGHT ONE, which is what it is for.**
The draft minted `(G1)`/`(G2)` for the proviso `G`'s two coincidence types —
**0-hit inside the pencil doc set but in prior use in `notes/FRICTION.md`,
`notes/Phase22a.md`, `notes/Phase22-realization-design.md`,
`notes/MolecularConjecture.md` and `notes/Prospect.md`** — and `(P₂)`/`(Z₂)` for
the two-sided forms of (BE-33)(ii)'s (P)/(Z). All four were **renamed before
commit** to bold prose names (**G-point**, **G-line**, *two-sided (P)*,
*two-sided (Z)*) rather than parenthesized tokens, so nothing new is minted at
all; the driver's own text was renamed in the same commit. The only surviving
`(X<digit>)`-shaped strings in the new section are the dispatch-log friction ids
`(F11)`/`(F12)`/`(F27)`, already in arc-wide use, and the backticked maths
`(H₁)`/`(H₂)` inside `ρ̄(H₁)`-style expressions, which are not tokens. **This is
the first time (L6) has caught a live collision rather than confirming a clean
draft** — recorded here because the (L5) substring rule's own precedent bullet
is the model.

The tail a successor opens at is **(BE-79) / *Step BE78*** (BSPREAD reserved
(BE-74)–(BE-78) / *Steps BE73–BE77* below, and consumed them in full).


## Reserved namespace — direction BSPREAD (2026-09-01, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved 2026-09-01 for the single direction BSPREAD** (ordinal 55, the arc's
sixty-third direction; `notes/Pencil-fanout.md` §"BSPREAD") — the **SPREAD step**,
(BE-32)(+)'s last 3.8 %, re-ranked to the top by BPEEL and picked by the
coordinator under the standing research delegation. Coordinator-set, single
dispatch — **not** a fan-out, so this reservation protects against the *existing
corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSPREAD** | §(K-bare-ext) — **extends**, no new section | **(BE-74)–(BE-78)** | **BE73–BE77** | `w4/bspread.py` (expected — extend `bearfull.py` and `bpeel.py`, and through them `binduc`/`btwocut`/`bimage` and the rest of the chain, by read-only import) |

The reservation opens at **(BE-74) / Step BE73**, exactly the tail BPEEL declared;
BPEEL consumed its reservation in full and returned nothing.

**CONSUMED IN FULL at the 2026-09-01 landing.** (BE-74) the block-absorption
lemma, (BE-75) what it retires and the coordinator's hypothesis disposed of,
(BE-76) job 0's correction, (BE-77) job 2's confinement, (BE-78) the board;
*Steps BE73–BE77*. **Nothing returned.** The next reservation on this section's
tail opens at **(BE-84) / Step BE83** — BONEONE reserved (BE-79)–(BE-83) /
*Steps BE78–BE82* on 2026-09-01, in the section below. The landing-time (L6) bare-token grep was
run on the drafted section: the new prose names — *block-absorption lemma*,
*route* / *edge route* / *path route*, *`[v]`-end*, *peel factorization*,
*witness split* — are **prose, not tokens**, minted deliberately in that form
because BPEEL's own (L6) grep caught four parenthesized tokens (`(G1)`/`(G2)`,
`(P₂)`/`(Z₂)`) that were 0-hit inside the pencil doc set but in prior use
elsewhere; this landing mints **no** new parenthesized token beyond
(BE-74)–(BE-78).

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` with `.git`/`.lake`/`__pycache__` excluded: `BSPREAD`, `bspread`,
`(BE-75)`, `(BE-76)`, `(BE-77)`, `(BE-78)` and *`Steps BE74–BE77`* each **0-hit**.
**`(BE-74)` and *`Step BE73`* have ONE hit each** — this file's own tail-pointer
line, opened and confirmed to be the pointer BPEEL wrote, not a consumed label:
the same carve-out the five preceding reservations needed.

**Checked and NOT chosen:** `BFORCE` and `BSTAR` — both rejected on the **(L5)
substring rule** (`BFORCE` hits inside driver text, `BSTAR` inside
`assert_generic_star`-adjacent prose), which is exactly the failure (L5)'s
substring half exists to catch. `BINDEP` is rejected because `bindep` hits as a
substring, and because it names the coordinator's *hypothesised* mechanism (the
independence proviso) rather than the question's site — `RESEARCH-ARC.md` §7 warns
against baking a coordinator prediction into the name, and job 1 may well find the
argument lives somewhere other than independence. `BSPREAD` names the site.

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the
returned draft; the reservation check sees prefixes and step ranges only. **BPEEL's
landing is the live precedent** — its (L6) grep caught four tokens (`(G1)`/`(G2)`,
`(P₂)`/`(Z₂)`) that were 0-hit inside the pencil doc set but in prior use
elsewhere in `notes/`, and all four were renamed to bold prose names before commit.


## Registry — `notes/Pencil-informal.md` (the (K) workbook)

Status keywords are pointers to the owning section's verdict block and the
*State of (K)* map, which remain authoritative.

| owning section | tag | labels in use | what the family is | status (see owner) |
|---|---|---|---|---|
| *Shared dictionary* | `SD-` | (R1)–(R5) *(grandfathered)*; **(SD-6)** | elementary rigid-graph facts used by **both** workbooks: min degree, size bound, short cycles, `hcard` restated, feasible triangles pendant, **branch length `≤ 5`** (= §(K-ann)'s (ANH-8), promoted here 2026-08-06; `SD-` because `(R6)` is taken by `Pencil-strategy.md` §4.6) | settled |
| §(K-tight) | `KT-` | (K-move) *(named here)*; Steps 0–5 | the carrier escape criterion, KT pp. 684–691 re-pin | criterion proven-informally; (K-tight) open |
| §(K-ins) | `INS-` ✓ | **(INS-1)–(INS-8)**; Steps INS1–INS7 | **new, 2026-09-08, direction BINSERT** — option B for `hbareSplit`, the insertion calculus: the chain audit, KT route B on the `ρ`-pullback, the chain-end **panel collapse** mechanism, and the one surviving endpoint (the joint sweep) | **option B SPENT save its joint sweep**; both KT-inherited routes REFUTED at `corank(G′) = 3`; `hbareSplit` UNTOUCHED (tier T1) |
| §(K-pitch) | `PT-` | (T1)–(T5); (K-wit), (K-pitch-∞) *(named here)*; Steps 0–6 | motion-side transfer, sign law, placement quartic, Λ-compression | (T1)–(T5) proven-informally; uniform form open |
| §(K-slide) | `SL-` | (S1)–(S5); **(W1)–(W4)**; (K-slide-cl) *(named here)*; Steps 1–5 | the slide-in transfer theorem; **(W1)–(W4) are the four conditions of the `ε = 0` limit line system** | (S1) proven-informally |
| §(K-slide-cl) | `SC-` | Steps C0–C5, and a claim **(C1)** stated in Step C1 | the tetrahedral collapse; (C1) = *rows independent ⟺ every class is a forest* | reduction proven; statement refuted as stated; `∃Σ` form open |
| §(K-slide-comb) | `SB-` | **(C6)**, **(C7)**, (C8); Steps D0–D5 | the combinatorial residue; (C6) = the packing half, (C7) = the repaired length-4 entry | (C6)/(C7) proven-informally; section refuted as a class statement |
| §(K-flank) | `FL-` | **(F1)**; Steps F0–F7 | adversarial rank test at the uncovered flanks | half 2 proven-informally per shape |
| §(K-pure) | `PC-` ✓ | (PC1), (PC2), (PC3), (PC5), (PC6), (PC-Z), (PC-OBS); (K-chord) *(named here)*; Steps P0–P9 | the pure condition of the limit carrier | (PC-Z)/(PC-OBS) proven-informally; direction C refuted |
| §(K-Λ) | `Λ` ✓ | (Λ0), (Λ0a)–(Λ0i), (Λ0′), (Λ0f′), (Λ1), (Λ2), (Λ3), **(OUT)**; **driver blocks (M1)–(M4)** (`lambda1.m2`) and **(P1)–(P7)** (`lambda0.m2`); **since 2026-08-19 (direction LTWO)** (Λ4)–(Λ8), Steps Λ8–Λ12 (**`Λ`-prefixed step scheme**, per clause 4 — *Step Λ8* is NOT the existing *Step 8*), driver modes `--witness`/`--floor`/`--census`/`--validate` (`w4/ltwo.py`) | the Λ-compression's quadric; (OUT) = the outer-line criterion, *Step 5a*; (since LTWO) the branch calculus on `G°` alone, the companion-cycle lemma and the size floor realizing item (vii)'s two-hub-interior population at all four patterns | (Λ1) an identity over the function field; (K-Λ) refuted as an independent gap; **(Λ4)–(Λ8) proven-informally** (Steps Λ8–Λ12, direction LTWO) — item (vii) REALIZED at a proven size floor, `(K-wit)` residual recomputed not re-graded, Λ-completeness unchanged |
| §(K-dom) | `DM-` ✓ | **(D1)**–(D4), **(DM-5)–(DM-11)**; Steps D0–D14; driver modes `--cap`/`--jac`/`--far`/`--validate` (`w4/dominance.py`) + `--index`/`--gate`/`--sim`/`--gen`/`--validate` (`w4/dsat.py`) | the dominance spike, differential of `H ↦ V_bc`; and, since *Steps D8–D14* (2026-09-03, direction DSAT), **the C2 satisfiability trace** — the conjunct's index set pinned to the degree-2 triples, the `dim V_bc = dim mot(G−a) − dim mot(G)` identity, and the combinatorial UNSAT gate | (D1)–(D3) proven, C1 refuted as a route; (DM-5)'s structural half / (DM-6) / (DM-7) proven, (DM-8)–(DM-10) measured, (DM-11) source-derived; **C2 struck as a uniform carry** |
| §(K-σ) | `σ` ✓ | (σ1)–(σ7); Steps σ0–σ6, σ4b; hunt pools H4/H5 | the polarity as a symmetry of the split; **route σ** | (σ7) proven; route σ a CANDIDATE (its field scope settled by §(K-clos)) |
| §(K-clos) | `AC-` ✓ | (AC-1)–**(AC-9)**; Steps Z0–Z8; driver blocks AC-C0/AC-E/AC-S/AC-U/AC-X/AC-Q/AC-R2/AC-F/AC-2c/AC-P (`closure.py`) | the over-`ℂ̄` question: the polarity's field scope, the σ-fixed grid locus, the `⋆`-eigen decoupling, the route-σ collapse, the char-0 descent | (AC-6) **refuted** as a class statement, open on the tight stratum; the rest proven-informally. **(AC-9)** (minted 2026-08-06, re-baselining slice S2): every σ-fixed body of degree `≥ 3` carries a coincident hinge line — **proven** by pigeonhole against *Step Z3*'s two-ruling-lines cap, measured 0/64 by the composite guard; it **qualifies (AC-3)** without weakening it |
| §(K-ann) | `ANH-` ✓ | (ANH-1)–(ANH-8); the two residual inputs **(ANH-R1)**, **(ANH-R2)**; Steps A1–A9; driver modes `--stress`/`--rate`/`--supp`/`--recipe`/`--census`/`--validate` (`annih.py`); **since 2026-08-06 (direction R)** (ANH-9)–(ANH-12), Steps A10–A13, and driver modes `--census`/`--bad`/`--comb`/`--validate` (`shrink.py`); **since 2026-08-06 (direction Q)** (ANH-13)–(ANH-16), Steps A14–A17, driver modes `--types`/`--reduce`/`--size`/`--frame`/`--witness`/`--validate` (`anhr1.py`) and M2 blocks (ANH-Q0)–(ANH-Q4) (`anhr1.m2`) | the annihilator as a self-stress of the contracted framework `H/P`: the reciprocity identity, the named move, the `k = 4` Tay circuit, the one-bracket recipe. **(ANH-8) is promoted to the *Shared dictionary* as (SD-6)** — that is the only copy | (ANH-1)–(ANH-6), (ANH-8) proven / proven-informally; (ANH-7) true-modulo-named-gap; **(ANH-R1) open** |
| §(K-out) | `OC-` ✓  ; **since 2026-08-19 (direction SIGZ, eighth fan-out)** (OC-35)–(OC-39), Steps O31–O36, driver modes `--reduce`/`--spans`/`--budget`/`--slack`/`--theta`/`--p21`/`--hunt` (`w4/sigz.py`), the Kirchhoff-flow form and the `slack`/`δ`/`ρ` ledger  ; **since 2026-08-19 (direction OSCHU, eighth fan-out)** (OC-29)–(OC-34), Steps O25–O30, driver modes `--restate`/`--gtarget`/`--rekey`/`--census1`/`--census2` (`w4/oschu.py`), pools POOL-OS / POOL-OQ / POOL-OG / POOL-OR / POOL-OC2  ; **since 2026-08-25 (direction OQRANK, single dispatch)** (OC-40)–(OC-44), Steps O37–O41, driver modes `--controls`/`--range A B`/`--census1`/`--census2`/`--validate` (`w4/oqrank.py`), pool POOL-OQ2 — the ⋆-eigen split with forced (1,2) profile, the per-block criterion and Veronese dictionary, the (OC-42) WALL, the 174/174 hunted census, and the openness theorem (OC-44); the SIGZ-returned (OC-40) re-claimed here  ; **since 2026-09-02 (direction OWALL, single draft-only dispatch)** (OC-50)–(OC-55), Steps O47–O51, driver modes `--controls`/`--agree A B`/`--full A B`/`--splits A B`/`--first A B`/`--synth`/`--validate` (`w4/owall.py`), pool POOL-OW  ; **since 2026-09-03 (direction OBAR, one direction of a concurrent round of four)** (OC-56)–(OC-61), Steps O52–O57, driver modes `--validate`/`--admis`/`--onerow`/`--hinge`/`--conic`/`--splits` (`w4/obar.py`) — the `b`–`c` attachment identity `corank R(H ⊕_A bc) = corank R(H) + dim(A ∩ V_bc^{⊥_E})`, the NEGATIVE admissibility gate on `H ∪ {bar along M}`, the pointwise identification of U3's target with (T3), the hinge reading's pointwise refutation, and the redundant-bar Klein conic. **The tail declared for the next reservation is (OC-62) / *Step O58*** — (OC-62)–(OC-65) and O58–O60 were reserved and RETURNED UNUSED — the two-direction-network model with the apolarity/discriminant dictionary, the exact matroid criterion for `Q(g) ≠ 0`, the three confinement certificates (W)/(C)/(Z), the logical redundancy of (OC-44)(iii)'s wall-avoidance conjunct, the cap-free 8 514-colouring census and the 98-pair split probe, and the reduction of (OC-44)(iii) to (OW) | (OC-1)–**(OC-16)**; Steps O1–O12; the **pools** POOL-C / POOL-G / POOL-S / POOL-B and (since direction O, 2026-08-06) POOL-CW / POOL-A / POOL-W / POOL-SL; driver modes `--comb`/`--pool`/`--shapes`/`--build` (`outerline.py`) and `--wide`/`--adv`/`--wrench`/`--slide` (`outerwide.py`) + `outerwide.m2`; **since 2026-08-19 (direction OCON)** (OC-17)–(OC-22), Steps O13–O18, driver modes `--validate`/`--check`/`--control` (`w4/ocon.py`), pools POOL-OV / POOL-OC / POOL-OZ; **since 2026-08-19 (direction ZNEQ, seventh fan-out)** (OC-23)–(OC-28), Steps O19–O24, driver modes `--factor`/`--sweep`/`--reject`/`--transfer` (`w4/zneq.py`), pools POOL-ZF / POOL-ZQ / POOL-ZN / POOL-ZT / POOL-ZR | (OUT)'s hypothesis measured: the exact hinge-rate reading, the ambient-generic map, the never-automatic negative, the constructed silent point, the two pool distributions, the sampler defect, and the residual; (since OCON) the hard-stratum target-rank qualifier is free, and the (OC-8) residue reduces to a `Z ≠ ∅` + chart-irreducibility + one-chart-point reduction; (since ZNEQ) input (a) `Z ≠ ∅` itself factors into a necessary-for-`hK` half dominated by §(K-grid) (GR-10) and a target-rank half whose failure is a codimension-2 Schubert jump, with a self-refuted-and-corrected closed form and a 138/138 witness census | **(OC-3)** proven-informally and load-bearing; (OC-1) proven-informally; (OC-2)/(OC-5)/(OC-6)/(OC-7) measured; (OC-4) exhibited; **(OC-8) open**. **(OC-7) is a harness item**, `notes/scripts/README.md` *Harness debt* 4 — **CLEARED 2026-08-06** by the re-baselining round, whose slice S2 also minted **(OC-9)** here (the FIELD half of the coincident-hinge guard's adversarial test: the guard rejects 58/357 and its rejection set strictly contains the two-end diagnostic's 39). **(OC-17)–(OC-21) proven-informally** (Steps O13–O16, direction OCON); **(OC-22) an assessment**; **(OC-8) OPEN, reshaped** — the hard-stratum qualifier struck as free, two named inputs (`Z ≠ ∅`, chart irreducibility) added rather than removed. **(OC-23)–(OC-25) proven-informally, (OC-26) proven-informally (its own first closed form refuted by construction and corrected), (OC-27) measured (138/138 witnesses), (OC-28) proven-informally (a conditional domination on the open §(K-grid) gap (GR-10), the boundary exhibited at `P21`)** (Steps O19–O24, direction ZNEQ); **input (a) OPEN as a class-uniform statement, NOT an independent gap; (OC-8) OPEN, unchanged**. **(OC-50)–(OC-53) proven-informally, (OC-54) measured, (OC-55) a reduction** (Steps O47–O51, direction OWALL) — the wall-avoidance conjunct of (OC-44)(iii) shown **logically redundant**, (Z) accounting for **19 of OQRANK's 20** second-confinement points (one unmatched; the populations are not directly comparable), (OC-44)(iii) restated as **(OW)**, still OPEN; **no gap-map status moves** |
| §(K-ind) | `IN-` | (I0)–(I4); Steps I0–I6 | numerical invariant along the generating moves | refuted as a route; (I3) a positive by-product |
| §(K-Δ) | `DL-` | **(M1)**, **(M2)**, **(M3)**; (N1), (N2) | the Δ-matroid literature hunt: (M1)–(M3) are the **three hypothesis tests**, (N1)/(N2) the two readings bought | NO HIT; discharged |
| §(K-bare-ext) | `BE-` ✓ | **(BE-1)–(BE-9)**, Steps BE1–BE8, driver modes `arith`/`danger`/`optc` (`kbare/breakhunt.py`) *(probe KBARE-FALSIFY, 2026-08-20)*; **since 2026-08-26 (direction BATTAIN)** **(BE-10)–(BE-14)**, Steps BE9–BE13, driver modes `model`/`cone`/`census`/`attain`/`indep`/`hunt`/`decide`/`localcone`/`probe` (`w4/battain.py`); (K-bare-ext) *(named here)* | the bare-half kernel off feasibility: the arbitrary-seed insertion lemma and its refutation; then the motive characterized off the Lean bodies, unconditional bare realizability, the hub-determinant form, the cone rank law `6(|V|−1) − def₂(G)`, and the direct-attainment statement | **(K-bare-ext) REFUTED as stated** (a *route* finding — `hbareSplit` UNTOUCHED and still pinned); (BE-10)/(BE-11)/(BE-12) **proven**; (BE-13) **proven-informally**, exact at 68/68; **(BE-14) OPEN**, measured 774/774, hard step isolated to `Y° ⊄ Z(G)`; **since 2026-08-26 (direction BTWOCUT)** **(BE-25)–(BE-29)**, Steps BE24–BE28, driver modes `wcheck`/`spqr`/`earfix`/`moduli`/`crosspair`/`hunt`/`probe`/`validate` (`w4/btwocut.py`) — the strengthened statement **PINNED** (S-mark closes, S-all does not, with the cost of each stated), the simultaneity worry proved **VACUOUS** by lower semicontinuity, a new elementary theorem (3-connected **minus one edge** still has `def₂ = def₃ = 0`) making the leaf base free, BINDUC's 56 ear misses **cleared as a constructor artifact**, the general-position half **dissolved on everything swept** (16/16, hunt empty at 13 484), and the induction's one genuinely-new obligation **named**: cross-pair welding; **since 2026-08-26 (direction BINDUC)** **(BE-20)–(BE-24)**, Steps BE19–BE23, driver modes `base`/`flatwit`/`gate`/`twocut`/`rank2`/`ear`/`hubplane`/`force`/`validate` (`w4/binduc.py`) — the FREE base (3-connected ⇒ `def₂ = 0`, exhaustive at 226 891), the exact 2-cut `max`-law **refuting BZAVOID's asserted `− 6`**, the rank-half composition criterion, the hub-plane construction (5 824 per-graph theorems) and the **generalized forcing mechanism** which strictly generalizes (BE-15)'s triangle rule and **fires empty as MEASURED** — **which is also the scope correction to (BE-15)(ii)**: its cap-free closure covers the TRIANGLE-forced mechanism, not the general one; **since 2026-08-26 (direction BZAVOID)** **(BE-15)–(BE-19)**, Steps BE14–BE18, driver modes `tri`/`crit`/`cap`/`pn`/`flat`/`sq`/`glue`/`validate` (`w4/bzavoid.py`) — the generalized forced-class cap and the **cap-free closure of the falsification arm at every graph**, the **planar-atom molecular identification** off the Lean bodies, the landed `G²` apparatus and the transversality count both **CLOSED**, and (BE-14) reduced to 2-connected graphs: **(BE-15)(ii)/(BE-16)(i)(ii)(iv)/(BE-17)(i)(ii)/(BE-18) proven, (BE-15)(i) proven-informally, (BE-16)(iii) proven on the distinct-adjacent-points locus, (BE-17)(iii) measured; (BE-14) still OPEN, `hbareSplit` untouched**; **since 2026-08-27/28 (directions BIMAGE, BEARCASE, BEARFULL, BSHARP — this clause repairs an index gap the first three left)** **(BE-30)–(BE-48)**, Steps BE29–BE47, drivers `w4/bimage.py`, `w4/bearcase.py`, `w4/bearfull.py`, `w4/bsharp.py` — the ear's image classified on the Klein quadric, (α) closed with the reach formula proved for `m ≥ 3`, the short-cycle law, and the (b1)-sharpening **dichotomy**; **since 2026-08-28 (direction BRULE)** **(BE-49)–(BE-53)**, Steps BE48–BE52, driver modes `dom`/`sep`/`domin`/`wit`/`hunt`/`validate` (`w4/brule.py`) — (b3)'s honest domain, the **separation theorem** making (b3) free wherever a BSHARP mechanism fires, the (R)/(Z) dominance correcting (BE-37)(ii)'s inference, and the one-witness-per-shape discharge; **since 2026-08-29 (direction BWIN)** **(BE-54)–(BE-58)**, Steps BE53–BE57, driver modes `dec`/`sweep`/`exc`/`cls`/`wide`/`validate` (`w4/bwin.py`) — the modular-law reformulation, the end-choice lemma and rank-one budget, the excess law, **the window identity PROVED as a CLASS THEOREM**, and job 3's window-is-not-the-barbells census; **since 2026-09-01 (direction BRNODE)** **(BE-59)–(BE-63)**, Steps BE58–BE62, driver modes `law`/`rec`/`carve`/`route`/`validate` (`w4/brnode.py`) — the boundary-pair lemma, the **decorated-skeleton law**, the complete SPQR recursion, the (BE-22)(vi) carve-out as a checkable condition on `B`, and the routing verdict relocating the R-node's content to the achievable decorations; **since 2026-09-01 (direction BDECOR)** **(BE-64)–(BE-68)**, Steps BE63–BE67, driver modes `prod`/`theta`/`small`/`chart`/`attain`/`validate` (`w4/bdecor.py`) — the **branch-product theorem** (at fixed hub flags the configurations of ANY piece are a literal product of ear chains, so per-child sets past ears are never needed), the flag base identified with §(K-chart)'s tower, the theta child's generic dimension law with welded attainment FREE, the small-`m` confinement propagating THROUGH the P-node, and half (B) at 28/28 peels as per-piece theorems; **since 2026-09-01 (direction BPEEL)** **(BE-69)–(BE-73)**, Steps BE68–BE72, driver modes `open`/`indep`/`law`/`force`/`gate`/`validate` (`w4/bpeel.py`) — the **dichotomy** (the good locus is Zariski-open on an irreducible chart, hence dense or empty, so the class statement is ONE generic invariant one draw computes), the **peel-independence theorem** (no topological branch crosses a 2-cut, so the two sides are disjoint coordinate blocks sharing only the flag pair — which is what RETIRES the exhaustiveness obligation), the shared-flag classification with the Klein-**ruling** candidate examined and set aside, the proviso `G` **closed on (CH-1)'s class**, and the **correction to (BE-66)(iv)** with the enumeration behind it (3 497 forced R-node-shaped peels, all with `min(δ₁,δ₂) = 0`) re-ranking the SPREAD step; **since 2026-09-01 (direction BSPREAD)** **(BE-74)–(BE-78)**, Steps BE73–BE77, driver modes `lemma`/`chain`/`peel`/`validate` (`w4/bspread.py`) — the **block-absorption lemma** (a block of an optimal partition absorbs at most TWO points of an outside vertex's closed star, and the closure admits on THREE), which proves **(BE-32)(+) OUTRIGHT** for the aggressive operator and three widenings of it, **retires** the star-2/SPREAD split rather than closing its second half, contains (BE-32)(ii)/(iii) as its `|B| = 1` case, makes the coordinator's closure-restriction hypothesis **MOOT**, confirms **(BE-41)(ii) REFUTED as stated** (five surfaces annotated) and confines cross-cut-only forcing at a 2-cut to **`δ₁ = δ₂ = 1`**, which exposes BPEEL's census-3 zero as vacuous; **since 2026-09-08 (direction BSERIES)** **(BE-164)-(BE-171)**, Steps BE163-BE170, driver modes `peel`/`conf`/`sweep`/`tools`/`budget`/`b1`/`board`/`validate` (`w4/bseries.py`) - the ONE-END peel, the two SELF-CONJUGATE confinements `Λ²π_v` and `Σ_{p_v}` meeting exactly in `Π_v`, the one-end excess law with a kill budget of TWO, the reduction of (b2) to (b1) **conditional on (PENCIL-SATURATES) at side-degree `≥ 2`**, the no-peel habitat, and the re-scoping of (BE-58)(iv) to **two items plus a corner**; **since 2026-09-08 (direction BGPROP)** **(BE-180)–(BE-187)**, Steps BE179–BE186, driver modes `geom`/`reduce`/`crit`/`validate` (`w4/bgprop.py`) — the proper → generic bridge read at source and found to TRANSPORT one step SHORTER than at `k = 1`, the reduction `Π_x(p) = Σ_p ∩ Ω^⊥` turning the family into products of **α-planes**, Lemma A's quadric dichotomy with its 2-space *vertex-pinning* refinement, the incidence bound delivering the route's first **class-uniform** properness positive (53/99), the codimension-6 **floor** REFUTING (BE-149)(v)'s own successor lemma at 10/99 by a proof, the `0 → R₀ → Γ → A → 0` extension bound, and the finding that properness is the **wrong target** where it fails (the containment forced, the clause POINTWISE, the population unable to exhibit a violation); **since 2026-09-08 (direction BRANKV)** **(BE-188)–(BE-195)**, Steps BE187–BE194, driver modes `ceil`/`arc`/`hunt`/`validate` (`w4/brankv.py`) — the framing correction (the pointwise target is **strictly stronger** than the clause, (BE-149)(iii) being one-directional), two proved ceilings turning the clause's conclusion into the combinatorial `dist ≥ 6`, the **arc-length-2 impossibility** (`c₁ ≁ y ∧ c₂ ≁ y`, cap-free), the **arc-length-3 RADICAL theorem** forcing coplanarity and `π_x = τ` hence `q_y ∈ π_x`, the **refutation of the pointwise clause** at 24/24 fully gated chart points, and the **first GENERIC closure of half (B)'s item 0(a) at side-degree `≥ 2`** on the arc-`≤ 3` strata (15/99) with the rank-4 boundary named; **since 2026-09-08 (direction BLONGARC)** **(BE-196)–(BE-203)**, Steps BE195–BE202, driver modes `form`/`perp`/`ladder`/`pop`/`validate` (`w4/blongarc.py`) — the object corrected (`Π_x` already contains `ℓ_j`, so the containment is ONE membership inside the **α-space** `α_x = p_x ∧ K⁴`), the dispatch's question answered **NO** (`det(B|_U) = (ac)²`, `rank = 2·rank(Y)` always even and **4** generically), (BE-193)(iv)'s hyperbolicity warrant made **unconditional** by the arc's own splitting `⟨ℓ₁,ℓ₂⟩ ⊕ ⟨ℓ₃,ℓ₄⟩` with both `P¹`-rulings **constructed**, the **perp-reduction** relocating the radical's habitat to `U ∩ ℓ_j^⊥`, the **arc-4 theorem** (exactly two candidates, one forbidden, the other forcing `q_z ∈ π_x`) with the pointwise clause **refuted again** at 24/24 gated arc-4 chart points, the **master invariant** `dim(U ∩ α_x) = max(1, min(|arc|,6) − 3)` subsuming (BE-190)/(BE-191)/(BE-193)/(BE-200) as four cases of one count and closing item 0(a) generically at arc `≤ 5` (**48 of 99**), and the **exact structural boundary** `|arc| = 6` — which is (BE-189)(iii)'s own threshold, so the path-bound method class closes precisely the strata where the clause is vacuous and provably cannot reach the 51 where it has content; the owning section's continuation verdict blocks are authoritative for every label listed in this row - **their count is deliberately NOT written here** (`grep -c '^## §(K-bare-ext) — continuation' notes/Pencil-informal.md`), because the figure this clause carried, *fourteen*, was stale by ten at the 2026-09-08 BSERIES landing: that is the **third** stale count in this one clause, and the round's *name the last ordinal, never a count* rule applies to it. *(Both counts in this clause's predecessor were stale — it said "eight continuation verdict blocks" and "all thirty-nine labels"; the block count is recomputed here (13, `grep -c '^## §(K-bare-ext) — continuation'`) and the label count is replaced by a pointer rather than silently recounted, per the 2026-09-01 `5ef8d70b` precedent for a disclosed stale count.)* |
| §(K-mech) | `MX-` ✓ | (MX-1)–(MX-9); driver modes `--flex`/`--wide`/`--inc`/`--sigma`/`--sweep` (`mech.py`) | the mechanisms of the residual (W2)/(W4) anomalies: the realizable-load space `Ω`, α-confinement, pole-cluster loads, the welded flex, the 6v11e rescue, the σ rider | (MX-1)/(MX-2) proven; (MX-3)–(MX-7) proven-informally; (MX-8) settled-NO in the probed family; (MX-9) measured |
| §(K-grid) | `GR-` ✓  ; **since 2026-08-19 (direction GTMPL, eighth fan-out)** (GR-79)–(GR-84), Steps G98–G103, driver modes `--charge`/`--frame`/`--tpl`/`--min`/`--wit`/`--e1`/`--lam`/`--val` (`w4/gtmpl.py`), the `n_hub = 16` **witness shape** and its 30-member family  ; **since 2026-08-19 (direction GFLOW, eighth fan-out)** (GR-85)–(GR-90), Steps G104–G109, driver modes `--model`/`--chain`/`--exact`/`--desc`/`--big`/`--adv`/`--validate` (`w4/gflow.py`), the clauses **(GR-R1)** and **(GR-C2)**  ; **since 2026-08-19 (direction GCOLL, eighth fan-out)** (GR-91)–(GR-96), Steps G110–G115, driver modes `--slack`/`--dem`/`--tf`/`--suff`/`--big8`/`--bigp`/`--wit`/`--dfg`/`--adv` (`w4/gcoll.py`), the Petersen witness family | (GR-1)–(GR-6); Steps G0–G7; driver blocks GR-D1–GR-D5 (`grid.py`); **since 2026-08-06 (direction G)** (GR-7)–(GR-11) + the primed successor **(GR-4′)** (recorded under (GR-4) as its repaired form, per L4 no-renaming), Steps G8–G13, driver modes `--formula`/`--treetriple`/`--wide`/`--validate` (`gridwit.py`); **since 2026-08-07 (direction E)** (GR-12)–(GR-15), Steps G14–G18, driver modes `--restate`/`--hard`/`--sep`/`--exemplar`/`--validate` (`packmm.py`); **since 2026-08-07 (direction TCOL)** (GR-16)–(GR-20), Steps G19–G23, driver modes `--branch`/`--runs`/`--pack`/`--hier`/`--wide`/`--validate` (`w4/gridcol.py`; `m2/gridcol.m2` not needed); **since 2026-08-07 (direction CFLANK)** (GR-21)–(GR-26), Steps G24–G28, driver modes `--law`/`--adv`/`--cubic`/`--lam`/`--lam6`/`--dens`/`--tight`/`--validate` (`w4/cflank.py`; `m2/cflank.m2` not needed, `§(K-prof)`/`PF-` unopened); **since 2026-08-13 (direction GCAP)** (GR-27)–(GR-28), Steps G29–G33, driver modes `--probe`/`--law`/`--cap`/`--flip`/`--adv`/`--validate` (`w4/gcap.py`; `m2/gcap.m2` not needed, `§(K-gcap)`/`GC-` unopened); **since 2026-08-13 (direction GUNIF)** (GR-29)–(GR-31), Steps G34–G37, driver modes `--menu`/`--ledger`/`--wit`/`--repair`/`--validate` (`w4/gunif.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened, `§(K-unif)`/`GU-` still not minted); **since 2026-08-13 (direction GEXIST)** (GR-32)–(GR-35), Steps G38–G42, driver modes `--exh`/`--charge`/`--repair`/`--adv`/`--validate` (`w4/gexist.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a third time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-13 (direction GORIENT)** (GR-36)–(GR-39), Steps G43–G47, driver modes `--hall`/`--kill`/`--hot`/`--adv`/`--validate` (`w4/gorient.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a fourth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-15 (direction GDEV)** (GR-40)–(GR-42), Steps G48–G52, driver modes `--charge`/`--bound`/`--adv`/`--hunt`/`--validate` (`w4/gdev.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a fifth time, `§(K-unif)`/`GU-` still not minted) *(clause BACKFILLED at the GADM landing — the GDEV landing recorded its claim only in the narrative entry below)*; **since 2026-08-17 (direction GADM)** (GR-43), Steps G53–G57, driver modes `--nk`/`--free`/`--balance`/`--adv`/`--validate` (`w4/gadm.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a sixth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-18 (direction GPSA)** (GR-44)–(GR-45), Steps G58–G62, driver modes `--sdr`/`--balance`/`--odd`/`--adv`/`--validate` (`w4/gpsa.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a seventh time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-18 (direction GDESC)** (GR-46)–(GR-48), Steps G63–G67, driver modes `--stuck`/`--cases`/`--opt`/`--adv`/`--validate` (`w4/gdesc.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened an eighth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-19 (direction GBAL)** (GR-49)–(GR-54), Steps G68–G73, driver modes `--zform`/`--oracle`/`--two`/`--split`/`--thm`/`--adv`/`--validate` (`w4/gbal.py`; the argument stayed inside §(K-grid)'s own family again, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a ninth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction YLOC, seventh fan-out)** (GR-61)–(GR-66), Steps G80–G85, driver modes `--loc`/`--fibre`/`--par`/`--coll`/`--fit`/`--cert`/`--adv`/`--validate` (`w4/yloc.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a tenth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction BALB, seventh fan-out)** (GR-67)–(GR-72), Steps G86–G91, driver modes `--anchor`/`--flip`/`--ceil`/`--exh`/`--big`/`--adv`/`--validate` (`w4/balb.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, an eleventh time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction AGLU, seventh fan-out)** (GR-73)–(GR-78), Steps G92–G97, driver modes `--pool`/`--pin`/`--kill8`/`--lam8`/`--adv`/`--val` (`w4/aglu.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a twelfth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened) | the tight-stratum residual of (AC-6): eigen-blocks as conic direction networks / generalized-spline systems, the counting obstruction families ((GR-3); unified as **(GR-8)** sub-multigraph cycle spaces), chart-image membership, the 907-shape census, the interpolation factorization (GR-7), the tree-triple certificate theorem (GR-9), the merged residual (GR-10), the ε-adic fallback (GR-11), the branch-level reduction to the hub multigraph (GR-16), the circuit run law (GR-17), the 6-spanning-tree packing statement (GR-18), the collapse-order hierarchy (GR-19), the excess law (GR-21), the five sparsity caps (GR-22), the flip injection (GR-23), the private-branch repair theorem (GR-24), the cut criterion (GR-25), the 40 742-shape exhaustive hunt (GR-26), the block-additive exact computation of the (GR-8) maximum (GR-27), the closed defect formula and `g ≤ 1` cap (GR-28), the exhaustive dart-menu budget ledger (GR-29), the exact-boundary refutation of the all-`k` cap (GR-30), the per-shape survival + sweep-local repair-distance measurement (GR-31), the capacity theorem (GR-32), the weakness/orientation lemma (GR-33), the union-bound refutation + rung-minority rule (GR-34), the submodularity/uncrossing lemma (GR-35), the structural interior-adjacency charge (GR-36), the (c,m) selection model and its cut-space parity obstruction (GR-37), the exact slack identity / attachment lemma / intersection kill (GR-38), the capacity-tight structure theorem with its saturation kills (GR-39), the corner charge (GR-40), the parity floor (GR-41), the pentagon-necklace refutation family (GR-42), the odd-cycle-packing shift floor (GR-43), the exact parity-layer selection formula with its automatic Hall/SDR discharge (GR-44), the balance-move calculus (GR-45), its one-move transitivity (GR-46), the (X, φ, T) normal form (GR-47), the stuck-case escape catalogue (GR-48), the z-form bijection (GR-49), the orientation criterion (GR-50), the weight criterion (GR-51), the parity theorem (GR-52), the splitting lemma (GR-53), the balance theorem (GR-54), the z-form translation of the chunk invariants (GR-61), the degree-predicate refutation (GR-62), the parity-step audit (GR-63), the collision bound (GR-64), the fit identity (GR-65), the GBAL-certificate measurement (GR-66), the M-anchored z-form and parity law (GR-67), the closed-form legal-move price (GR-68), the imbalance ceiling with its exact boundary (GR-69), the reduction to one availability clause with its exhaustive stratum verification and T1 refutation (GR-70), the beyond-stratum extension with cap-free certificates (GR-71), the slack-0 degree lemma and its J-charge extension to arbitrary branch sets (GR-73), the `n_hub = 8` AA-glue pinning to a single template (GR-74), the `n_hub = 8` intersection-kill theorem (GR-75), the general-`n` W-charge forcing `n_hub ≥ 10` (GR-76), the `n_hub = 8` binding-non-laminarity census (GR-77), and the exhaustive `n_hub = 8` fully-good-colouring census (GR-78) | reduction proven; (GR-2) a proven refutation of the former (AC-6) close-route sentence; **(GR-4) refuted-as-stated, repaired as (GR-4′), off the critical path; (GR-9) proven; (GR-12)/(GR-13)/(GR-14) proven-informally — the (GR-10) min-max REFUTED as posed, (GR-10) itself open (exhaustively certified where swept); (GR-16)–(GR-19) proven — the branch reduction, circuit run law, 6-tree packing and collapse hierarchy — collapse order 4 measured at all 18 habitat separators; (GR-21)–(GR-25) proven — the excess law, five sparsity caps, flip injection, private-branch repair, cut criterion — TCOL's two named flank sites both CLOSED AS A ROUTE, (GR-26) exhaustive over 40 742 shapes with no hit; **(GR-27) proven; (GR-28)(i)–(iii) proven, (GR-28)(iv) REFUTED at `k ≥ 3` with an exact boundary — a THEOREM at `n_hub ≤ 6` (GR-29's ledger), FALSE from `n_hub = 8` on (GR-30's four witnesses, `g` up to 3) — the certificate-3 target still proven per swept shape at every `D = 0` shape checked; per-shape (GR-15) HOLDS at all four new witnesses and *Step G32*'s ≤ 2-flip repair law is sweep-local, breaking at `n_hub = 16` (GR-31)**; **(GR-32)–(GR-33) and (GR-35) proven — the capacity theorem (whole graph exactly critical, every proper chunk one unit slack), the weakness lemma (binding needs ≥ 2 aligned per-hub weaknesses; the all-even case is a pure orientation problem) and the uncrossing lemma (defect submodular) reduce the uniform target to a minority-dart orientation problem; (GR-34) REFUTES the uncorrelated union-bound mechanism by a constructed witness (`CL10`) while a correlated rung-minority rule closes the whole ladder family — GEXIST is an honest MISS, no g-flank found**; **(GR-36)–(GR-39) proven — the structural charge (the corrected obstruction family is the binding-capable chunks, strictly larger than capacity-tight), the (c,m) selection model (matching-based colourings, cut-space parity obstruction), the intersection kill (settled VACUOUSLY STRONG at `n_hub ≤ 6` — binding is laminar, no crossing same-block pairs), and the hot-hub structure theorem + kills (0 fully-hot hubs, now EXHAUSTIVE over all 4920 shapes) — GORIENT is an honest MISS, re-anchoring the target on a bounded-deviation selection principle (W3 the sticking instance, needing `d = 3` against `d ≤ 2` elsewhere), no g-flank found**; **(GR-40)–(GR-42) proven (direction GDEV) — the corner charge (tight at W3M, where (GR-36) prices 0), the parity floor (deviations bounded below by the coset invariant `φ*`), and the pentagon necklaces: the bounded-deviation selection form is REFUTED AS POSED (`d ≥ m/2` unbounded; every member rank-certified fully-good — a form-refutation, never a flank); the layer split measured, `d_fg = d_adm` at 133/133**; **(GR-43) proven (direction GADM) — the odd-cycle-packing shift floor: `d_par = d_adm = d_fg = m` EXACTLY at NK(2)/6/8/10 (rank-certified at the optimum, up to `n_hub = 50`), so the shift-metric layer is UNBOUNDED and the growth law's bounded-correction reading is REFUTED while the (a′) `d_fg = d_adm` law SURVIVES its first large-`d` test; ledger entry 5 (per-shape admissibility) settled as a separate OPEN statement ((GR-37)(iii)'s balance clause statement-beyond-proof); the W3 stick corrected to a 1-shift + 1-balance split — an honest MISS on (a′)-as-a-theorem, no g-flank found**; **(GR-44)–(GR-45) proven (direction GPSA) — the Hall/SDR step AUTOMATIC and `d_par(M) = w_M` EXACT (entry 5's parity half PROVEN, (GR-37)(iii) repaired there; the balance clause stays statement-beyond-proof), plus the cut-move calculus with its exact flip formula — entry 5's balance half true-modulo-named-gap (the descent lemma's stuck case), exhaustively true at 97 censused shapes, entry 5 NOT a HIT, no g-flank found**; **(GR-46)–(GR-48) proven (direction GDESC) — the move family is ONE-MOVE TRANSITIVE, so the descent lemma over the FULL family is EQUIVALENT to entry 5's balance half (the stuck case no smaller residual; a full-family demotion witness would be E1 clause (v)); the (X, φ, T) normal form restates balance as matching flexibility; the escape catalogue's PROVEN {T1, T2} kill is REALIZED at n = 30 — the bounded {T1, T2} descent route DEMOTED BY WITNESS while {T1, T2, K3} stays unbeaten, entry 5 still OPEN and NOT a HIT with its residual named input (X), (b′)'s unmeasured half measured, no g-flank found**; residual = (GR-15), OPEN unchanged, no flank found, the route re-anchored on the growth-law form — (a′) primary with its sticking case named (fixed-μ exchange insufficient); GADM's shift-metric routing of the thirteenth was OVERRIDDEN by the accepted 2026-08-18 recon verdict (GPSA, ledger entry 5 — LANDED 2026-08-18; GDESC, the descent lemma's stuck case — LANDED 2026-08-18); (GR-49)–(GR-54) proven (direction GBAL, one of five in the sixth fan-out) — the z-form absorbs the (c, m)/coset/SDR/matching apparatus into one bit per branch, balance becomes a degree-constrained orientation decided EXACTLY in polynomial time, the two-sided Hall condition collapses to a local weight inequality, a parity contradiction shows one monochromatic-pair hub per side is harmless, and a finite exhaustion over the maximal constraint structures shows one always suffices — chaining to **the balance theorem**: **entry 5 is PROVEN in BOTH halves, a HIT** (the parity half re-derived without Petersen, `d_par(M) = w_M` untouched), **E3 ARMED but does NOT fire** (entry 1's (a′) stays open), the (GR-45)–(GR-48) apparatus subsumed not contradicted, no g-flank found — the certificate-3 uniformity ROUTE stays dead as posed**; **(GR-61)–(GR-66) proven-informally (direction YLOC, one of five in the seventh fan-out)** — the pinned GBAL-localization route DEMOTED BY WITNESS (GR-62): full goodness is not a function of the (GR-50) degree data, so no (GR-51)-shaped criterion applies to the chunk system; the coordinator's predicted break point REFUTED as stated (GR-63) — (GR-52) localizes for free, the chain actually breaking two links earlier, at (GR-50)→(GR-51); the positive content is a colouring-free collision bound on `d_fg` (GR-64) and a coordinate-free fit identity unifying `dist(m, M)` and `z_mono(S)` (GR-65); GBAL's own certificate measured against (Y), missing both constraints (GR-66) — input (Y) stays OPEN, not hit, **E3 (ARMED by GBAL) does NOT fire**, no g-flank found; **(GR-67)–(GR-72) proven (direction BALB, one of five in the seventh fan-out)** — the M-anchored z-form gives the PARITY LAW (every per-matching layer gap EVEN) and is the perfect-matching instance of the landed (GR-65)(i) fit identity, independently re-derived and corroborating it (GR-67); every legal move is priced in closed form, matching branches and whole 2-factor cycles FREE, PROVING (b′)'s price half outright (GR-68); the imbalance ceiling `\|δ\| ≤ 2 min(k, ⌊n_hub/4⌋)` is a THEOREM at `n_hub ≤ 6` and FALSE from `n_hub = 8` at an explicit Wagner-graph witness (GR-69); (b′) reduces to one availability clause, verified EXHAUSTIVELY on the whole stratum in its landed T1-only instance, which is REFUTED from `n_hub = 8` with stuck witnesses each repaired at price 0 by a named mixed-pair successor (GR-70); (b′) extended to 536 exact shapes at `n_hub = 8/10/12` with cap-free per-matching certificates at `n = 30` (GR-71) — **(b′) stays OPEN, NOT a HIT**, residual Clause A′'s doubly-blocked case; no g-flank found; **(GR-73)–(GR-78) proven/measured (direction AGLU, one of five in the seventh fan-out)** — ledger attack (c) is **SETTLED NEGATIVE at `n_hub = 8`**: the AA-glue configuration is pinned to a single 10-branch template (GR-74) and proven NOT realizable there, independently certified by an EXHAUSTIVE, uncapped scan of the complete stratum that reproduces (GR-38)'s own `n_hub ≤ 6` headline exactly, so the (GR-38) intersection kill is a **THEOREM at `n_hub = 8`, non-vacuously** (GR-75); a general-`n` charge pushes the open case to **`n_hub ≥ 10`**, a three-template question (GR-76); the dispatch's predicted consequence is **REFUTED** — outright binding laminarity is FALSE at `n_hub = 8` (3 774 crossing same-block binding pairs, EXHAUSTIVE, against 0 at `n_hub ≤ 6`), so only the **maximal** family's uncrossing survives (GR-77); the (GR-15) counting-side target holds EXHAUSTIVELY over the whole `n_hub = 8` stratum with no cap, 86.9 % of colourings fully good, no g-flank (GR-78) — a HIT on the not-realizable branch; no gap-map status moves, (GR-15) OPEN modulo (GR-4′), class uniformity untouched  ; **since 2026-08-25 (direction GFLIP, single dispatch)** (GR-97)–(GR-99), Steps G116–G119, driver modes `--form`/`--lemma`/`--thm`/`--wit`/`--validate` (`w4/gflip.py`) — the demand form of the (GR-51) criterion, the cubic counting lemma, and the selection theorem (at most `b` A-branches blocked); **(GR-R1) PROVEN**, so (GR-89)(ii)'s `n`-free `≤ 12` is a THEOREM; (GR-100)/(GR-101)/Step G120 returned to the tail  ; **since 2026-08-25 (direction GCHEAP, single dispatch)** (GR-100)–(GR-104), Steps G120–G124, driver modes `--cap`/`--sel`/`--bnd`/`--validate` (`w4/gcheap.py`) — the lone-dart identity + blocked-end capacity, the selection corollary (every-step (GR-C2) PROVEN for `n_hub < 6|δ|`, so (b′) at the constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum), the stall tax, the `n_hub = 12` boundary witness (per-configuration (GR-C2) REFUTED, boundary exact both ways), and the price-form residual (GR-104); the GFLIP-returned (GR-100)/(GR-101)/Step G120 re-claimed here  ; **since 2026-08-25 (direction GPRICE, single dispatch)** (GR-105)–(GR-109), Steps G125–G129, driver modes `--cell`/`--seed`/`--hunt`/`--mech`/`--validate` (`w4/gprice.py`) — the colour-swap identity `f(p) = f(p̄)`, the reversal-set normal form at `O ⊆ M` (`dist = n − |R|` exact, `f` computable in `2^n`), the reachability theorem (affine pattern-subspaces, the linkage obstruction), the minted **balance law (GR-108)** — (GR-104)(i) a THEOREM at `2k = 2`, every `n`, modulo it alone — and the status statement (GR-109)  ; **since 2026-08-25 (direction GBLAW, single dispatch)** (GR-110)–(GR-114), Steps G130–G134, driver modes `--form`/`--conn`/`--recomb`/`--strand`/`--validate` (`w4/gblaw.py`) — the arc-transversal normal form, the recombination theorem (maximum-family connectivity, the universal-linkage refutation shape), the escape lemma (**(GR-108) ⟸ existential escape**), the measured escape verdict (universal escape REFUTED at the `n = 16` strand witness; existential escape 0 failures at 1 099 pairs), and the status statement (GR-114)  ; **since 2026-08-26 (direction GXESC, single dispatch)** (GR-115)–(GR-119), Steps G135–G139, driver modes `--ledger`/`--closure`/`--hunt`/`--verify`/`--strand`/`--validate` (`w4/gxesc.py`) — the reversal-label ledger (M-closed ⟹ balance-valid at every `2k`), the **refutation of (GR-108) and existential escape by four verified witnesses from `n = 16`**, the gap-2 law (⟺ (GR-104)(i) at the cell, proven except at the all-(2,2) case), the measured record, and the status statement (GR-119) |
| §(K-res) *(in `notes/Pencil-informal-grid.md`, end of file)* | `RS-` ✓ (2026-08-28, direction RESGRID) | (RS-1)–(RS-6), *Steps RS1–RS10*; (RS-7)–(RS-10) returned; driver modes `--audit`/`--dimz`/`--rank`/`--theta`/`--validate` (`w4/resgrid.py`); **since 2026-09-03 (direction RPOOL)** (RS-11)–(RS-15), *Steps RS11–RS16*, driver modes `--pool`/`--sweep`/`--proof`/`--witness`/`--law` (`w4/rpool.py`, no `--validate`: the five legs are past the 600 s foreground budget together) — RESGRID's returned (RS-11)/(RS-12) re-reserved here, (RS-16)–(RS-18) returned | the residual-habitat transport audit: (RS-1) the habitat-free rank identity, (RS-2) the slack law, (RS-3) the forced core witness + rigidity-covers-excess, (RS-4) the transported discharge, (RS-5) the (K-res) grid residual ((GR-15)'s criterion, quantifier widened), (RS-6) the deficient-fringe refutation (θ(2,3,7)); (RS-11) the **per-block floor law** (`h₊ = h₋ = c`, the two slacks sum to `index`, `dim Z_± ≥ max(0, g_± − s_±)`), (RS-12) the 255-pool census (**102** `def = 0` members), (RS-13) **the refutation of (RS-5)** with the witness `R20 = family_g(5,(0,0,2),(4,4,4))` (**30 of the 102 refute it, 72 carry exact-point proofs**), (RS-14) the mechanism ((RS-3)(ii) bounds the SUM, the witness lives in BOTH blocks), (RS-15) the covering law `flank ⟺ index < 2·g_forced` | (RS-1)–(RS-4), (RS-6) proven-informally; **(RS-5) REFUTED 2026-09-03** (its per-shape proofs at `W19`/`S29`/`NT21c3` stand); (RS-11)/(RS-13)/(RS-14) proven, (RS-12) measured-exhaustive over the recorded pool, (RS-15) measured at 153 shapes with 0 counterexamples; the repaired statement OPEN and the `index < 2·g_forced` members ROUTELESS; the (K-res) wave a user call, re-priced |
| §(K-frame) | `FR-` ✓ | (FR-1)–(FR-7); the residual input **(FR-R1)**; Steps FR0–FR6; driver modes `--rulings`/`--pattern`/`--transport`/`--outer`/`--validate` (`framedom.py`) and M2 blocks (FR-M0)–(FR-M3) (`framedom.m2`); **since 2026-08-07 (direction PEX)** (FR-8)–(FR-14), Steps FR7–FR11, driver modes `--frame`/`--recipe`/`--strat`/`--kill`/`--validate`/`--recon` (`w4/patexist.py`; `m2/patexist.m2` not needed); **since 2026-08-19 (direction FRES)** (FR-15)–(FR-17), Steps FR12–FR15, no driver ((FR-18) reserved and unused) | the shared chart-to-frame dominance residue of §(K-out) (OC-16) / §(K-ann) (ANH-14): the minimal non-containment lemma, the ruling decomposition and determinant law at grid points, the `G′`-regridding transport, the 1904-site pattern battery, the θ(3,4,5) constructed witnesses, (since PEX) the bare-cycle stratum's finiteness + exhaustive enumeration, and (since FRES) the chart-map-vs-chart-variety correction that closes the residue with no rider | (FR-1)/(FR-2)/(FR-3) proven / proven-informally; (FR-4) superseded by **(FR-17)**, proven-informally with **no named gap**; (FR-5) measured (each certificate a per-site proof); (FR-6) exact per point, retro-certified by (FR-16); **(FR-R1) PROVEN** (Steps FR7–FR11, direction PEX); **(FR-15)–(FR-17) proven-informally** (Steps FR12–FR15, direction FRES) — no rider remains |
| §(K-chart) | `CH-` ✓ | (CH-1)–(CH-8); Steps CH1–CH8; driver modes `--empty`/`--guard`/`--fibre`/`--all` (`w4/cirr.py`) | *(new, 2026-08-19, direction CIRR)* the pencil chart of `G′` proven irreducible, ℚ-rational, a tower of affine-linear fibres: the constant-fibre-dimension restriction identified as `IsNondegPencilRealization` conjunct 3 ((CH-6)), the closure argument that makes the restriction cost nothing ((CH-4)), the nonemptiness clause and its girth ≥ 4 correction to §(K-frame) *Step FR13* ((CH-5)), and the consumer audit of §(K-out) (OC-19) / §(K-slide) (S1)(e) / §(K-dom) (D4) / §(K-ann) (ANH-9)(ii) ((CH-7)); (CH-8) is a pointer to the landed, strictly stronger `not_pencilNondegFeasible_of_triangle_two_hubs` | (CH-1)–(CH-7) proven-informally, no named gap; (CH-3)/(CH-6) proven; **a HIT** — all four consumers clean; no gap-map status moves |
| §(K-shear) | `SH-` ✓ | (SH-1)–(SH-6); Steps SH1–SH5; driver modes `--iso`/`--bed`/`--inv`/`--prod`/`--validate` (`w4/zshear.py`) | *(new, 2026-08-26, direction ZSHEAR — the first section minted from an EXTERNAL idea source rather than an internal residual)* the Witt shear of `notes/Pencil-strategy.md` §9's (ZH-1) settled: the shear group identified as the `Λ²`-image of the affine translations, `Q` as its own defining invariant, the §(K-tight) criterion proved **equivariant entry-for-entry**, the coordinator-offered per-body repair decided in both readings, and the general symmetry-vs-deformation dichotomy | **(SH-1)–(SH-6) proven** — (SH-1)/(SH-2)/(SH-5)(i) **symbolic identities** in `ℚ[…]`, no sampling; **(ZH-1) REFUTED / STRUCK from the shelf**, a HIT of the negative kind. **No gap-map row moves.** Durable residue: `Q(r̃) ≠ 0` is `PGL(4)`-invariant, so **no gauge-fixing or frame normalization can ever supply it** |
| §(K-jac) | `JC-` ✓ | (JC-1)–(JC-6); Steps JC1–JC5; driver modes `--sym`/`--tan`/`--codim`/`--validate` (`w4/zjacob.py`; no M2 leaf, barred for stated mathematical reasons) | *(new, 2026-08-26, direction ZJACOB — the SECOND section minted from the external §9 shelf)* the Jacobian / singular-locus route of `notes/Pencil-strategy.md` §9's (ZH-4) settled: the polynomial presentation of the motion cone and its zero-section Jacobian `[0 \| A(y)]`, the corank stratification identity `dim 𝒞 = max_k(dim B_k + 6 + k)`, the direction and input-dependence of the classical height bounds on ideals of minors, the criterion's blindness to fibre-quadratic (pure-condition) data, and the faithful re-encoding of §(K-tight) *Steps 2.1/2.4* | **(JC-1)–(JC-6) proven / proven-informally** — (JC-1)(b) and (JC-4) **symbolic identities** in `ℚ[pts]`, no sampling; **(ZH-4) REFUTED / STRUCK from the shelf, and its refutation ABSORBS (ZH-3)**. A HIT of the negative kind. **No gap-map row moves.** Durable residue: the determinantal/scheme package is a **conservation law** — it converts expected codimension *into* structure and has no theorem *producing* it over a non-generic base |

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
| §(SAFE-RES), direction WTRI | `TF-` | **(TF-1)–(TF-6)**; ***Steps TF1–TF6*** | the triangle-freeness cost (T), **LANDED 2026-09-02, reservation consumed EXACTLY (6/6, no remainder)**: (TF-1) the two landed feasibility *transfers* `Step 4` had not inventoried, (TF-2) the pendant triangle's anatomy + `2EC ⟹ deg z ≥ 4`, (TF-3) the `deg z ≥ 5` case by `PencilNondegFeasible.mono`, (TF-4) the `deg z = 4` case by the delete-one-then-steer chain, (TF-5) **(T) IS A THEOREM**, (TF-6) verification / the four Lean obligations / the by-product one-plane feasibility criterion. Owning section is authoritative |
| §widened kernels (routes 1/3), direction WELOC | `EL-` | **(EL-1)–(EL-5)**; ***Steps EL1–EL6*** | the (E-loc) gap, **LANDED 2026-09-02, reservation consumed 5 of 6 — (EL-6) RETURNED unconsumed**, its step carrying no new labelled claim: (EL-1) the hub-degree law (every hub of a feasible `G` has ≤ 2 hub neighbours), (EL-2) the count identity `f = 5c − |W| + 1` and the anatomy of a minimal dependent set, (EL-3) a brick is a hub `C₄`/`C₅`, (EL-4) **no residual carries a brick** (shape 2 impossible), (EL-5) **(E-loc) is REFUTED** by `T32`. *Step EL6* carries the consumer trace, the successor (E-pair) and (V). Owning section is authoritative |
| §widened kernels (routes 1/3), direction WPAIR | `PAIR-` | **(PAIR-1)–(PAIR-6)**; ***Steps PR1–PR6*** | the (E-pair) obligation: **all six consumed, LANDED 2026-09-02** (identity / contraction criterion / seed lemma / `e₀ = 0` stratum / seed condition / (V)). `EP-` rejected on the (L5) substring rule (`STEP-1`/`STEP-4`) |
| §widened kernels (routes 1/3) | `WK-` | (E-loc) — **REFUTED**; **(E-pair)** (minted 2026-09-02, WELOC); **(K-res)** | the routes-1/3 kernel widening; (E-pair) is (E)'s successor target, *two adjacent degree-`2` vertices*; (K-res) is the widened kernel carried as a byte-identical sibling of `hK` |

## Registry — `notes/Pencil-strategy.md`, `Phase39.md`, `Phase39-design.md`

| owner | labels in use | what the family is |
|---|---|---|
| strategy §4 | **C1**, **C2**, **C3** | the three candidate stronger inductive invariants (C1 = dominance of the `V_bc` map, run and struck; C2 = the general-position conjunct, trace run 2026-09-03 and **struck as a uniform carry** — UNSAT off the class, §(K-dom) (DM-7)/(DM-8)) |
| strategy §4.7 | tag **`AV-`**, tokens **(AV-1)–(AV-8)**; ***Steps AV1–AV6***; driver modes `--supply`/`--census`/`--betti`/`--forced`/`--avoid`/`--count`/`--validate` (`w4/avoidgen.py`) | probe **C3-AVOID**'s pricing of C3's *"reduce avoiding `S`"* gate against the landed generation theorem (Thm 4.9): the degree-2 supply lemma (AV-1), the conservation law and the `2 μ(G)` capacity ceiling (AV-2)/(AV-4), the `\|S\| ≤ 2` threshold theorem (AV-3), the refutation of every structural hypothesis on `S` (AV-5), the contraction-free classification (AV-6), the necessary-not-sufficient scope line (AV-7), the board verdict (AV-8). **Reservation consumed exactly; §(K-avoid) never opened.** Owning section is authoritative |
| strategy §4.6 | **U1**, **U2**, **U3** | the three ranked live class-uniformity successors |
| strategy §9 | tag **`ZH-`**, tokens **(ZH-1)–(ZH-6)** | the six external-technique-transfer candidates from the Zheng body–pin preprint (minted 2026-08-21, verified 0-hit across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2`; **unpriced** and not on §8's board — the owning section is authoritative, and the source is unrefereed) |
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
| **(D1)–(D4)** | §(K-dom) claims | §(K-dom) *Steps* D0–**D14** | §(K-slide-comb) *Steps* D0–D5; **`notes/Phase23-design.md`'s Phase-23f item-4 *Steps* D1–D8** *(found 2026-09-03, direction DSAT: bare `D8` is 4 hits / 2 files there and in `model-experiment-archive.md`)* |
| **(M1)–(M4)** | §(K-Λ) `lambda1.m2` driver blocks | §(K-Δ) the three hypothesis tests | — |
| **(P1)–(P7)** | §(K-Λ) `lambda0.m2` driver blocks | §(K-pure) *Steps* P0–P9 | — |
| **(R1)–(R6)** | *Shared dictionary* rigid-graph facts (R1)–(R5) | R1/R2/R3 the opening recon questions | `Pencil-strategy.md` §4.6's six refutations (R1)–(R6) — **and (ANH-R1)/(ANH-R2)**, §(K-ann)'s two residual inputs, which are *prefixed precisely to stay out of this row* |
| **(T)** | §(K-pitch) (T1)–(T5) transfer claims | W4 §(SAFE-RES) (T) — triangle-freeness, **PROVED 2026-09-02** (*Step TF5*); the token stays ambiguous, so keep qualifying it | — |
| **(W1)–(W4)** | §(K-slide) limit-system conditions | the phase's **work packages** W0–W5 (**W4 = `hcontract`**) | — |
| **(N1), (N2)** | §(K-Δ) the two readings | N8/N9/N10/N10b the W4 gates | — |
| **(F1)** | §(K-flank) claim / *Steps* F0–F7 | `dispatch-log.md` F-rows (F5, F11, F12, …) | — |
| **(σ5)** | §(K-σ) claim (σ5) | §(K-σ) *Step σ5* (the four obligations) | — |
| **(S1)–(S5)** | §(K-slide) claims | `S29` test shape (distinct form; noted for completeness) | — |
| **(E1)–(E5)** | §(K-grid)'s **termination-ledger** codes (E1)/(E2)/(E3) — `E3` is *armed*, so the family is LIVE | the molecular program's **brick** codes in live Lean doc-comments: (E2) `chainData_or_cycleData_of_noRigid`, (E4) the ENTRY binder reshape, (E5) `cycle_realization` | §(K-bare-ext) **(E4)**, BARCH's two-sided clause — **REFUTED 2026-09-08 (BFOUR)**; found 2026-09-08, and see the debt note under (L6) |

The two most dangerous in live prose are **(W4)** — because "W4" reads as
`hcontract` everywhere in `Phase39.md` and as the limit-system condition
everywhere in §(K-slide)/§(K-pure) — and **(C6)/(C7)**, which have already
caused one landed fixup.

## Reserved namespace — direction BONEONE (2026-09-01, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved 2026-09-01 for the single direction BONEONE** (ordinal 56, the arc's
sixty-fourth direction; `notes/Pencil-fanout.md` §"BONEONE") — **can an
R-node-shaped 2-cut peel have `δ₁ = δ₂ = 1`?**, which is the whole of what
BSPREAD reduced job 2 to ((BE-77)(iv)). Coordinator-set, single dispatch —
**not** a fan-out, so this reservation protects against the *existing corpus*
only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BONEONE** | §(K-bare-ext) — **extends**, no new section | **(BE-79)–(BE-83)** | **BE78–BE82** | `w4/boneone.py` (expected — extend `bspread.py`, and through it `bpeel`/`bearfull`/`btwocut`/`bimage`/`bzavoid` and the rest of the chain, by read-only import) |

**CONSUMED IN FULL at the landing (2026-09-01).** Labels **(BE-79)–(BE-83)** and
*Steps BE78–BE82* are all used, in order, by the section's BONEONE
continuation; **nothing is returned**. Label preservation in the `(K-bare)`
gap-map row was verified by **scripted set-diff** against `HEAD`, not by eye:
`(BE-79)`–`(BE-83)` added, and `(BE-78)` re-attached after the recompute had
dropped it.

**(L6) landing-time grep, RUN.** `BONEONE` / `boneone` / `(BE-79)`–`(BE-83)` /
*Steps BE78–BE82* hit only this landing's own files. The direction minted **no
new parenthesized token**: *the factorization*, *the size bound*, *the
11-vertex floor*, *path side*, *side* / *glue*, *skeleton of a side* and
*genuineness* are prose, following BSPREAD's precedent. Two short handles were
minted and then **renamed before commit**: the witnesses were drafted as
`W11` / `W16`, both 0-hit but reading as if they belonged to the live `W4`
family, and they ship as **`WIT11` / `WIT16`**. That is the (L5) reader-side
rule catching what a bare grep passes — the same objection that ruled out
`BRPEEL` at reservation time, and the second time it has fired for this
direction.

The reservation opens at **(BE-79) / Step BE78**, exactly the tail BSPREAD
declared; BSPREAD consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` with `.git`/`.lake`/`__pycache__` excluded: `BONEONE`, `boneone`,
`(BE-80)`–`(BE-83)` and *`Steps BE79–BE82`* each **0-hit**. **`(BE-79)` and
*`Step BE78`* have two hits each** — this file's BPEEL tail line and BSPREAD's
own tail sentence — both opened and confirmed to be tail POINTERS, not consumed
labels: the same carve-out the six preceding reservations needed.

**Checked and NOT chosen:** `BRPEEL` (0-hit, but a **reader-side** collision —
it is one inserted letter from the landed `BPEEL`, and this registry's whole
purpose is that a code is unambiguous *when read*, which the (L5) substring rule
formalizes for greps and cannot for eyes); `BFLEX` and `BDELTA`, both 0-hit but
naming a *hypothesis* — "both sides flexible", "the `δ` shape" — rather than the
question's site, which `RESEARCH-ARC.md` §7 warns against and BSPREAD's own
reservation already rejected `BINDEP` for. `BONEONE` names the `(1,1)` shape,
which is exactly what the question asks about.

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the
returned draft; the reservation check sees prefixes and step ranges only.
BSPREAD's landing is the live precedent for the **prose-name** habit that avoids
the problem outright: it minted *block-absorption lemma*, *edge route*, *path
route*, *`[v]`-end*, *peel factorization* and *witness split* as prose rather
than as parenthesized tokens, and so minted nothing new at all.

**CONSUMED IN FULL at the 2026-09-01 landing.** (BE-79) the per-side reduction and
the witness, (BE-80) why both of (BE-77)(iv)'s tiers had `0` chances, (BE-81) the
forcing test and (BE-66)(iv)'s refuted conclusion, (BE-82) the price and the
residue; *Steps BE78–BE82*. **Nothing returned.** The next reservation on this
section's tail opens at **(BE-84) / Step BE83** — BGENUINE reserved
(BE-84)–(BE-88) / *Steps BE83–BE87* on 2026-09-01, in the section below. *(This
consumption record and the tail pointer were added by the coordinator at the
BGENUINE prep: the landing updated the section heading to CONSUMED but left the
body without either, which is the one thing a successor's 0-hit check reads.)*


## Reserved namespace — direction BGENUINE (2026-09-01, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved 2026-09-01 for the single direction BGENUINE** (ordinal 57, the arc's
sixty-fifth direction; `notes/Pencil-fanout.md` §"BGENUINE") — **is the
coincidence BONEONE re-opened GENUINE, and does it BITE?**, the price BONEONE
itself named ((BE-82)). Coordinator-set, single dispatch — **not** a fan-out, so
this reservation protects against the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BGENUINE** | §(K-bare-ext) — **extends**, no new section | **(BE-84)–(BE-88)** | **BE83–BE87** | `w4/bgenuine.py` (expected — extend `boneone.py` for the witness family and `bdecor`/`bpeel` for the chart/`ρ̄` instruments, by read-only import) |

The reservation opens at **(BE-84) / Step BE83**, exactly the tail BONEONE
declared; BONEONE consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`,
`*.py`, `*.m2` with `.git`/`.lake`/`__pycache__` excluded: `BGENUINE`,
`bgenuine`, `(BE-85)`–`(BE-88)` and *`Steps BE84–BE87`* each **0-hit**.
**`(BE-84)` and *`Step BE83`* have one hit each** — the tail sentence in
BSPREAD's section, opened and confirmed to be a POINTER, not a consumed label.

**Checked and NOT chosen:** `BREACH` — rejected on the **(L5) substring rule**
(`breach` hits **5** files, and `reach` is itself a live technical term in this
arc, `reach = min(δ₁+δ₂,6)`, which is exactly the kind of overlap (L5) exists to
catch). `BBITE` and `BSHORT` are both 0-hit but name the **second** sub-question
only; the *gating* one is genuineness, and a code should name what the direction
is about first. `BGENUINE` names the question, **not a predicted answer** —
`RESEARCH-ARC.md` §7's warning is about baking in a *prediction*, and this
direction may well return *not genuine*.

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the
returned draft. **This direction is the arc's first GEOMETRIC one in six**, so
the temptation to mint configuration-level tokens is higher than it has been:
prefer prose names, as BSPREAD and BONEONE both did.

**CONSUMED IN FULL at the landing (2026-09-01).** Labels **(BE-84)–(BE-88)** and
*Steps BE83–BE87* are all used, in order, by the section's BGENUINE
continuation: (BE-84) the genuineness theorem and the certificate census,
(BE-85) the chart of a forced witness plus the (CH-1) check and the new `(10,5)`
row, (BE-86) the criterion without (BE-22)(iii)'s hypothesis and the `0`
shortfall, (BE-87) what half (B) is left with and the vacuous job 3, (BE-88) the
board. **Nothing is returned.** Label preservation in the `(K-bare)` gap-map row
was verified by **scripted set-diff** at every one of the four recompute passes,
never by eye: `(BE-84)`–`(BE-88)` added, **zero lost**, row 1 475 → **1 545**
words against the 1 600 cap (the ear-case and BONEONE history blocks rewritten
as current state, per F21 and BPEEL's precedent).

**(L6) landing-time grep, RUN.** `BGENUINE` / `bgenuine` / `(BE-84)`–`(BE-88)` /
*Steps BE83–BE87* hit only this landing's own files. The direction minted **no
new parenthesized token**. Three prose handles were minted — ***hinge-pair
certificate***, ***attainment loss*** (`a_i`), and the ***confinement*** /
***freedom*** controls — and the first is a **deliberate reuse**, not a new
term: *"hinge pair"* already names the pair of hinge lines at a body
(`repin.hinge_coincidences`), and *"coincident hinge pair"* already names the
degeneracy this certificate's guard excludes. The reuse is stated at
(BE-84)(i) so a reader meeting *"hinge-pair certificate"* is pointed at the
existing vocabulary rather than at a second meaning. **`a₁`/`a₂` are
single-letter and therefore (L5)-risky**; they are scoped explicitly to *"the
side's own attainment loss at the chosen configuration"* at every use, and the
gap-map row spells the gloss out rather than carrying the bare symbol.

**The next reservation on this section's tail opens at (BE-89) / Step BE88.**


## Reserved namespace — direction WTRI (2026-09-01, **CONSUMED 2026-09-02 — the direction LANDED; kept as the minting record**)

**Reserved 2026-09-01 for the single direction WTRI** (ordinal 58; `notes/Pencil-fanout.md`
§"WTRI") — **W4 / `hcontract`, route 3's cost (T): is a feasible residual `G`
triangle-free?** Coordinator-set, single dispatch — **not** a fan-out, so this reservation
protects against the *existing corpus* only.

**This is the sequence's FIRST W4-side direction**, so two things differ from every
reservation above it and both are deliberate:

- **The owning file is `notes/Pencil-W4-informal.md`, not `notes/Pencil-informal.md`.**
  The `(BE-…)` family belongs to §(K-bare-ext) and **must not be extended here**; the W4
  workbook's own families are `NG-`, `SR-` and `WK-` (registry table below).
- **There is NO gap-map row for the W4 side, and this direction does not open one.** The
  *State of (K)* map is the **(K) arc's** status object by its own header; W4's status
  lives in the W4 workbook's per-section confidence verdicts and in `notes/Phase39.md`
  *Blockers*. `notes/check-gapmap-cells.py` therefore will not fire on this landing —
  which is a fact to state in the commit message, not a gate to skip silently.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **WTRI** | `notes/Pencil-W4-informal.md` §(SAFE-RES) — **extends**, no new file | **(TF-1)–(TF-6)** — **all six consumed, no remainder** | **TF1–TF6** — all six used | `w4/wtri.py` **SHIPPED** (`--validate`/`--audit`/`--regress`): it does *not* hunt for a triangle-carrying residual (impossible in principle) but audits the theorem's side conditions on the blind-spot family and regression-tests the new (TF-6) certificate against the 255 recorded inhabitants |

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded: `WTRI`, `wtri`, `(TF-1)`–`(TF-6)` and
*`Steps TF1–TF6`* each **0-hit**. The `TF-` tag is new and topic-tagged, which is the shape
`notes/Pencil-labels.md`'s own diagnosis says has **never** collided.

**Checked and NOT chosen:** extending the `SR-` family — `(T)` already lives there as a
bare single letter, and the **collision table** in this file records `(T)` as ambiguous
(§(K-pitch)'s transfer claims vs W4's triangle-freeness). Minting `(T1)`, `(T2)`, … beside
it would make that collision worse, which is exactly what clause (L4) forbids. `TF-` is
disjoint and self-describing, and the direction should **qualify every citation of the
bare `(T)`** with its owner, per (L3).

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the returned
draft, and note that the W4 workbook has its own single-letter families ((C1)–(C8), (E),
(T), (V)) which are **already** in the collision table — a new bare letter here is the
worst-case mint in the whole doc set.


## Reserved namespace — direction WELOC (2026-09-02, **CONSUMED 5/6 — LANDED, (EL-6) RETURNED**)

**Reserved 2026-09-02 for the single direction WELOC** (ordinal 59; `notes/Pencil-fanout.md`
§"WELOC") — **W4 / `hcontract`, the gap (E-loc)**: *every residual `G` has a degree-`2`
vertex `v₀` with `E(G − v₀)` independent in the `(6,6)` count matroid.* The **second**
W4-side direction; the conventions WTRI's reservation established for that side bind here
unchanged and are **not restated** (owning file `notes/Pencil-W4-informal.md`, the
`(BE-…)` family **not** extended, **no gap-map row** and none opened, so
`notes/check-gapmap-cells.py` will not fire — state that rather than skip it).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **WELOC** | `notes/Pencil-W4-informal.md` §widened kernels (routes 1/3) — **extends**, no new file | **(EL-1)–(EL-6)** | **EL1–EL6** | `w4/weloc.py` *(conditional, as WTRI's was — see the spec on why this question's 255/255 is **not** in (T)'s blind spot but has a different limitation)* |

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded: `WELOC`, `weloc`, `(EL-1)`–`(EL-6)` and
*`Steps EL1–EL6`* each **0-hit**. `EL-` is topic-tagged and multi-letter, the shape this
file's own diagnosis records as never having collided; it sits beside `TF-` (WTRI) in the
W4 registry table.

**Checked and NOT chosen:** `WCOUNT` (0-hit, but it names the *instrument* — the count
matroid — rather than the question, and the question is about **which vertex**, not about
counting); extending `WK-`, the existing tag of §widened kernels, because `(E-loc)` and
`(K-res)` already live there as **bare** tokens and a fresh numbered family beside them
would invite exactly the ambiguity clause (L3) exists to prevent. **Qualify every citation
of the bare `(E)` with its owner** — this file's collision table does not yet list `(E)`,
and this direction is the first to use it heavily.

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the returned
draft. Two single-letter risks specific to this question: **`f`** (the count function) and
**`v₀`** are already in arc-wide use and must stay glossed at each use, and the
supermodularity argument will want names for the two obstruction shapes — **prefer prose
names**, as WTRI and BSPREAD both did.

**LANDED 2026-09-02.** **(EL-1)–(EL-5)** consumed; **(EL-6) returned unconsumed** — *Step
EL6* is the consumer trace and carries no claim that wanted a label. The two obstruction
shapes took **prose** names as instructed (*brick* and *shape 1*), and one new token was
minted outside this family: **(E-pair)**, in §widened kernels' own bare-token neighbourhood
beside (E-loc)/(K-res), registered in the `WK-` row above. `T32` follows the `W19`/`S29`
witness-naming convention and is defined in `notes/Pencil-W4-informal.md` §widened kernels
*Step EL5*, its canonical home.


## Reserved namespace — direction WPAIR (2026-09-02, **CONSUMED 6/6 — LANDED, nothing returned**)

**Reserved 2026-09-02 for the single direction WPAIR** (ordinal 60;
`notes/Pencil-fanout.md` §"WPAIR") — **(E-pair)**: *every residual carries two adjacent
degree-`2` vertices.* The **third** W4-side direction; WTRI's W4-side conventions bind
unchanged and are **not restated** (owning file `notes/Pencil-W4-informal.md`, `(BE-…)`
not extended, **no gap-map row** and none opened, so `notes/check-gapmap-cells.py` will
not fire — state it, do not skip it).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **WPAIR** | `notes/Pencil-W4-informal.md` §widened kernels (routes 1/3) — **extends** | **(PAIR-1)–(PAIR-6)** | **PR1–PR6** | `w4/wpair.py` (conditional, as WTRI's and WELOC's were) |

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded: `WPAIR`, `wpair`,
`(PAIR-1)`–`(PAIR-6)` and *`Steps PR1–PR6`* each **0-hit**.

**`EP-` was CHECKED AND REJECTED, and it is the (L5) substring rule's cleanest catch
yet.** The obvious tag for (E-pair) is `EP-`, and `(EP-1)`/`(EP-2)`/`(EP-4)` are **not**
0-hit: they occur as substrings of **`STEP-1`**, **`STEP-4`** and `perp-transport` in
`notes/Phase23b.md`, `notes/Phase23d.md` and `notes/model-experiment-archive.md`. None is
a *label* collision — every hit is an innocent substring — which is precisely the failure
(L5)'s substring half exists to catch, because a future grep for `(EP-4)` would surface
Phase-23 prose. **`PAIR-` is topic-tagged, multi-letter and 0-hit**; the *step* prefix is
**`PR`** rather than `PAIR` only to keep *Step* names short, and `Steps PR1–PR6` are
0-hit too. Also checked and 0-hit but not chosen: `AJ-`, `D2-` (both opaque at the point
of use — a reader meeting `(D2-3)` cannot tell what family it is, and this file's own
collision table already carries a `(D1)–(D4)` row).

**(L6) reminder for the landing.** Run the landing-time bare-token grep. The live risk on
this question is **`(E)`** and **`(E-pair)`** themselves: `(E)` is a bare single letter
not yet in the collision table, and `(S1)`–`(S5)` **are** in it — (SAFE-RES′)'s clauses
versus §(K-slide)'s claims versus §(K-bare-ext)'s window conditions, three owners for one
token. **Qualify every one of them with its owner** (L3); the WELOC landing left one
unqualified `(S1)/(S2)` and the coordinator repaired it at the WPAIR prep.

**LANDED 2026-09-02.** **(PAIR-1)–(PAIR-6)** and *Steps PR1–PR6* all consumed, nothing
returned: (PAIR-1) the deficit identity, (PAIR-2) the contraction criterion at a general
rigid set, (PAIR-3) the seed lemma, (PAIR-4) the proved `e₀ = 0` stratum, (PAIR-5) the seed
condition (E-pair) reduces to, (PAIR-6) (V) as a theorem given (E-pair). Two new **named
objects** took prose/symbol names rather than labels, per WTRI's and WELOC's precedent: the
**hub graph `Λ = G[hubs]`** and the **hub boundary `∂_hub U`** (with `∂U` its unrestricted
form), both glossed at every *Step* that uses them; and **`e₀`/`σ`** are the two counting
statistics of (PAIR-1). No new bare single-letter token was minted. Every citation of `(E)`,
`(E-pair)`, `(T)`, `(V)` and `(S1)`/`(S2)` in the landed prose is owner-qualified per (L3);
the landing-time bare-token grep was run.

## Reserved namespace — direction WGROW (2026-09-02, **LANDED**)

**LANDED 2026-09-02: all six labels and all six steps CONSUMED, nothing returned.**
**(GROW-1)** the localized deficit identity, **(GROW-2)** the hub-multigraph
rigidity criterion + hub closure, **(GROW-3)** the rigid parts of a
minimum-excess partition, **(GROW-4)** the seed dichotomy, **(GROW-5)** `K₂,₃`
refuting (PAIR-5) as stated, **(GROW-6)** **(E-pair) is a theorem**; *Steps
GW1–GW6* in `notes/Pencil-W4-informal.md` §widened kernels.

**Reserved 2026-09-02 for the single direction WGROW** (ordinal 61;
`notes/Pencil-fanout.md` §"WGROW") — the target is **(PAIR-5)**, the *seed condition*:
every simple, 2EC, triangle-free, `hcard` graph whose degree-`2` vertices are independent
and which carries a proper rigid subgraph has a rigid `U` with `3 ≤ |U| ≤ |V| − 2` and
`|∂_hub U| ≤ 2`. The **fourth** W4-side direction; WTRI's W4-side conventions bind
unchanged and are **not restated** (owning file `notes/Pencil-W4-informal.md`, `(BE-…)`
not extended, **no gap-map row** and none opened, so `notes/check-gapmap-cells.py` will
not fire — state it, do not skip it).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **WGROW** | `notes/Pencil-W4-informal.md` §widened kernels (routes 1/3) — **extends** | **(GROW-1)–(GROW-6)** | **GW1–GW6** | `w4/wgrow.py` (conditional, as WTRI's / WELOC's / WPAIR's were) |

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in both cases**: `WGROW`, `wgrow`,
`wgrow.py`, `(GROW-`, `GROW-`, `(GROW-1)`–`(GROW-6)` and the raw step tokens `GW1`–`GW6`
each **0-hit**.

**The codename names the ATTACK, not the target, and that is deliberate but not a
commitment.** *Step PR5*'s named attack is to **grow** a rigid set along a `Λ`-run; the
*target* is (PAIR-5) whichever way it is attacked, and per `RESEARCH-ARC.md` §7 the
attack is a coordinator hypothesis to be tested, not inherited. Precedent for
attack-named directions: BPEEL, BSPREAD, BWIN, BTWOCUT.

**`SEED-` was CHECKED AND REJECTED — the (L5) substring rule firing a second time in two
directions, and this time on the LOWERCASE half.** The obvious tag for the *seed*
condition is `WSEED` / `(SEED-n)`. The minted forms `(SEED-1)`–`(SEED-6)` are 0-hit, but
two innocent substring families are not: the bare string `(SEED` has **11 hits**, every
one the Python expression `random.Random(SEED)` in five tracked drivers
(`w4/{ltwo,ogeom,sigz,resgrid,repin}.py`); and **`wseed` has 9 hits as a local variable
name in `w4/kslide.py`**, which would have made the driver `w4/wseed.py` un-greppable.
Neither is a label collision — which is exactly what (L5)'s substring half exists to
catch. WPAIR's rejection of `EP-` (inside `STEP-1`/`STEP-4`) is the same catch on the
uppercase half; the pair of them is why the check runs in **both** cases, and that is now
written into the clause above. Also checked and 0-hit but not chosen: `(RUN-` / `RN1`–`RN6`
(bare `RUN` is common prose, so a `RUN`-grep is noisy even though `(RUN-` is clean) and
`(SC-` / `(WS-` (opaque at the point of use).

**(L6) reminder for the landing.** Run the landing-time bare-token grep. The live risks
are the three WPAIR flagged, unchanged: **`(E)`** and **`(E-pair)`** (bare, and `(E)` is a
single letter not in the collision table); and **`(S1)`–`(S5)`**, which have **three**
owners — (SAFE-RES′)'s clauses, §(K-slide)'s claims, §(K-bare-ext)'s window conditions.
Qualify every one with its owner (L3). New objects this direction is likely to need
(`Λ`-run, dangling `Λ`-end, `Λ`-component) already have prose/symbol names from WPAIR —
**re-use them, do not mint labels for them**, per WTRI's and WPAIR's precedent.

## Reserved namespace — direction BBASE (2026-09-02, **CONSUMED IN FULL — LANDED 2026-09-02**)

**Reserved 2026-09-02 for the single direction BBASE** (ordinal 62, the arc's seventieth
direction; `notes/Pencil-fanout.md` §"BBASE") — **the flag base off the no-adjacent-hubs
class** ((BE-65)(i)/(BE-68)(ii) item 1), candidate 1 of the (BE-14) thread and the smaller
of half (B)'s two residue items. Coordinator-set, single dispatch — **not** a fan-out, so
this reservation protects against the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BBASE** | §(K-bare-ext) — **extends**, no new section | **(BE-89)–(BE-93)** | **BE88–BE92** | `w4/bbase.py` (expected — extend `bdecor.py`'s chart instruments and `bsharp`/`widened`'s samplers by read-only import) |

The reservation opens at **(BE-89) / Step BE88**, exactly the tail BGENUINE's registry row
declared; BGENUINE consumed its reservation in full and returned nothing.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in both cases**: `BBASE`, `bbase`,
`bbase.py`, `(BE-90)`–`(BE-93)` and the raw step tokens `BE89`–`BE92` each **0-hit**.
**`(BE-89)` and *`Step BE88`* have one hit each** — the tail sentence in BGENUINE's
registry row, opened and confirmed to be a **pointer**, not a consumed label. (Same shape
as BGENUINE's own `(BE-84)` / *Step BE83* check.)

**`BFLAG` was CHECKED AND NOT CHOSEN, on two independent grounds.** It is **no longer
0-hit** — BSHARP's prep rejected it in 2026-08-28 and both that reservation and the
fan-out section record the rejection, so the token now appears twice — and BSHARP's
recorded **reason still stands**: *"it names the apparatus (the point-plane flag
`Π_u = p_u ∧ π_u`) rather than the question"*. Re-using a name whose rejection is on the
record would also make the registry ambiguous about which direction it belonged to. Also
checked: `BREAL` (0-hit, but it names the *object* `B_real` in a way that reads as a
variable rather than a question), `BPATH` (0-hit uppercase but names a **predicted case
split** — `RESEARCH-ARC.md` §7's warning about baking in a prediction, and the path case is
exactly the coordinator reading most likely to be wrong), and `BFREE` (`bfree` hits **15**
files, an (L5) substring rejection). **`BBASE` names the object the question is about and
not a predicted answer**, per BGENUINE's precedent.

**(L6) reminder for the landing.** Run the landing-time bare-token grep on the returned
draft. Live risks: **`(S1)`/`(S2)`**, which have **three** owners — (SAFE-RES′)'s clauses,
§(K-slide)'s claims, §(K-bare-ext)'s window conditions — qualify every one (L3); and
**`B_real`**, which is a prose/symbol name, not a label, so **do not mint one for it**.
Prefer prose names for new configuration-level objects, as BSPREAD, BONEONE and BGENUINE
all did; the objects this direction is likely to need (a `B_real`-component, a `Λ`-run, a
flag chain) already have prose names in the corpus.

**Gap-map note (F21) — PAID at the landing.** The `(K-bare)` row was at
**1 544 / 1 600 words**, 56 spare; **recomputed to 1 385** (215 spare) while absorbing
(BE-89)–(BE-93), label preservation verified by **scripted set-diff — 93 codes in, 98 out,
zero dropped**, three inline code spans dropped and each verified body-present
(`` `2` `` at *Step BE74*, `` `δ = 1` `` at *Steps BE78–BE81*, and `` `def₂ = def₃` ``,
which survives inside the larger span `{3-connected} ∪ {max deg ≤ 2} ∪ {def₂ = def₃}` and
was a regex artifact rather than a drop). `notes/check-gapmap-cells.py` **GREEN**.

**Consumption, at the landing.** All five labels **(BE-89)–(BE-93)** and all five steps
**BE88–BE92** are consumed; **nothing is returned**. The driver landed at the reserved path
`notes/scripts/w4/bbase.py`. The (L6) bare-token grep was run on the draft: `(S1)`/`(S2)`
appear nowhere in the new section (its window conditions are cited as *"§(K-bare-ext)'s own
two window conditions"*, and the one pre-existing unqualified use in `notes/Phase39.md` was
qualified in the same commit), and **no label was minted for `B_real`** or for any of the
new configuration-level objects (the flag base, a `B_real`-component, the collinear
stratum), which keep prose names as BSPREAD / BONEONE / BGENUINE did.

## Reserved namespace — direction BUNIF (2026-09-02, **CONSUMED IN FULL**)

**Reserved 2026-09-02 for the single direction BUNIF** (ordinal 63, the arc's seventy-first
direction; `notes/Pencil-fanout.md` §"BUNIF") — **half (B)'s LAST residue**, the class
quantifier (BE-67)(iii), i.e. *`reach(H;x,y) = min(δ₁+δ₂,6)` at every internal R-node piece
and peel*. Coordinator-set, single dispatch — **not** a fan-out, so this reservation
protects against the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BUNIF** | §(K-bare-ext) — **extends**, no new section | **(BE-94)–(BE-98)** | **BE93–BE97** | `w4/bunif.py` (expected — extend `bpeel.py`'s reach instruments, `bdecor.py`'s chart layer, `bgenuine.py`'s census and `bbase.py`'s flag tower, by read-only import) |

The reservation opens at **(BE-94) / Step BE93**, the tail BBASE consumed to. **BBASE
consumed (BE-89)–(BE-93) and *Steps BE88–BE92* in full and returned nothing**, and its own
registry row did not declare the next tail — recorded here so the pointer is not lost, and
the omission noted rather than glossed. (BGENUINE's row still carries the *now-consumed*
"(BE-89) / Step BE88" pointer; it is a dated record of that reservation, not a live one.)

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in both cases**: `BUNIF`, `bunif`,
`bunif.py`, `(BE-94)`–`(BE-98)` and the raw step tokens `BE93`–`BE97` each **0-hit**. Note
the contrast with the last two openings: this tail is **entirely clean**, with no pointer
hit to open and confirm, because BBASE declared none.

**`BREACH` STAYS REJECTED and `BCLASS` is rejected the same way.** BGENUINE's prep already
struck `BREACH` on the **(L5) substring rule** — `breach` hits **5** files, and `reach` is
itself this arc's live technical term (`reach = min(δ₁+δ₂,6)`), exactly the overlap (L5)
exists to catch — and that reasoning applies with more force here, where `reach` is the
direction's own subject. `BCLASS`/`bclass` hit **7** and **21** files (the drivers'
`class_shape` family). **`BUNIF` names the question — uniformity — and not a predicted
answer**, per BGENUINE's and BBASE's precedent.

**(L6) reminder for the landing.** Run the landing-time bare-token grep. Live risks:
**`(S1)`/`(S2)`**, three owners — (SAFE-RES′)'s clauses, §(K-slide)'s claims,
§(K-bare-ext)'s window conditions; BBASE's landing avoided the token entirely by writing
*"§(K-bare-ext)'s own two window conditions"*, which is the habit to copy. **`reach`**,
**`Good`**, **`A₁`/`A₂`** and the **flag pair** are existing prose/symbol names — reuse
them, mint nothing for them.

**Gap-map note (F21).** The `(K-bare)` row stood at **1 385 / 1 600 words** after BBASE's
recompute, 215 spare — comfortable, but **recompute-to-a-target still applies** and label
preservation is verified by **scripted set-diff**, never by eye.

**LANDED 2026-09-02 — the reservation is CONSUMED IN FULL and nothing is returned.**
Labels **(BE-94)–(BE-98)** and *Steps BE93–BE97* all used, in §(K-bare-ext) as reserved
(extended, no new section); driver `notes/scripts/w4/bunif.py` at the reserved path. The
**(L6) landing grep** was run: the risky token **`(S1)`/`(S2)`** appears only in the
qualified form *"§(K-bare-ext) *Step BE56* / (BE-57)(iv)'s own two conditions"*, with the
three owners named in the same sentence — a step past BBASE's habit, which avoided the
token rather than qualifying it. **`reach`, `Good`, `A₁`/`A₂` and the flag pair** were
reused as prose/symbol names and nothing was minted for them. **Two new
configuration-level objects took PROSE names**, per the reservation's preference: the
**block profile** `c_i(U)` of a side at a flag pair, and the successor condition
**(NO-DOUBLE-PENCIL)** — the latter is a *named condition*, not a label, and is
0-hit-verified across the doc set at landing time. The **next tail is (BE-99) / *Step
BE98***, declared here so the omission BBASE's row made is not repeated. **Gap-map
outcome:** the `(K-bare)` row was recomputed to **1 472 / 1 600** (128 spare), scripted
set-diff **101 labels in, 112 out, ZERO dropped**.

## Reserved namespace — direction BDOUBLE (2026-09-02, **CONSUMED IN FULL**)

**Reserved 2026-09-02 for the single direction BDOUBLE** (ordinal 64, the arc's
seventy-second direction; `notes/Pencil-fanout.md` §"BDOUBLE") — **(NO-DOUBLE-PENCIL)**
((BE-97)(iii)), the one place BUNIF's 14 per-side inequalities are tight. Coordinator-set,
single dispatch — **not** a fan-out, so this reservation protects against the *existing
corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BDOUBLE** | §(K-bare-ext) — **extends**, no new section | **(BE-99)–(BE-103)** | **BE98–BE102** | `w4/bdouble.py` (expected — extend `bunif.py`'s block/profile/margin instruments and `bpeel.py`'s reach layer, by read-only import) |

The reservation opens at **(BE-99) / Step BE98**, exactly the tail **BUNIF declared** — the
habit BBASE's row omitted and BUNIF restored. Both tokens have **one hit each**, opened and
confirmed to be that declaration, not a consumed label.

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in both cases**: `BDOUBLE`, `bdouble`,
`bdouble.py`, `(BE-100)`–`(BE-103)` and the raw step tokens `BE99`–`BE102` each **0-hit**.

**Checked and NOT chosen:** `BTIGHT` (0-hit both cases, but it names a **measured
property** — that the `Π_x` block is tight at 8 of 92 rows — rather than the question, and
(BE-97)(iv) is precisely about how far that measurement generalizes); `BPENCIL` (0-hit, but
*pencil* is the **phase's own subject**, so the code would read as being about
`PencilPair` rather than about one block of one peel). **`BDOUBLE` names the condition and
not a predicted answer**, per BGENUINE's, BBASE's and BUNIF's precedent.

**(L6) reminder for the landing.** Run the landing-time bare-token grep. Live risks:
**`(S1)`/`(S2)`** with three owners — BBASE's and BUNIF's habit of writing
*"§(K-bare-ext)'s own two window conditions"* is the one to copy. **Mint nothing** for
`Π_x`, `c_i(U)`, `margin`, `blockcap`/`blockdeg`, the 16 stable subspaces or the double
pencil itself: all are existing prose/symbol names from BUNIF's landing, and this section
has now gone four directions without minting a configuration-level token.

**Gap-map note (F21).** The `(K-bare)` row stands at **1 472 / 1 600 words** after BUNIF's
recompute — **128 spare, the tightest in three landings**, so a **recompute to a target** is
required rather than optional, with label preservation by **scripted set-diff**.

**LANDED 2026-09-02 — the reservation is CONSUMED IN FULL and nothing is returned.**
Labels **(BE-99)–(BE-103)** and *Steps BE98–BE102* all used, in §(K-bare-ext) as reserved
(extended, no new section); driver `notes/scripts/w4/bdouble.py` at the reserved path. The
**(L6) landing grep** was run: **`(S1)`/`(S2)`** appears only in the qualified form
*"*Step BE56* / (BE-57)(iv)'s **(S1)**/**(S2)**"*, inside a sentence that names the item
it belongs to — BUNIF's habit, kept. **Nothing was minted** for `Π_x`, `c_i(U)`, `margin`,
`blockcap`/`blockdeg`, the 16 stable subspaces or the double pencil itself, per the
reservation's explicit constraint; all are reused as BUNIF's prose/symbol names. **One new
configuration-level object took a PROSE name**: the per-side condition
**(PENCIL-SATURATES)** — *`c_i(Π) = 2 ⟹ ρ_i = 6`*, which is (BE-38)(iii)'s third clause
contrapositively — 0-hit-verified across the doc set at reservation time and now the
direction's named residual. **(NO-DOUBLE-PENCIL) is retained as a token** even though the
condition is **refuted**: it names the statement, and the refutation is recorded against
it at (BE-97)(iii) and (BE-99); it is **not** recycled. The **next tail is (BE-104) /
*Step BE103***, declared here per BUNIF's habit; both tokens verified **0-hit** across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` at landing time. **Gap-map outcome:** the
`(K-bare)` row was recomputed to **1 546** words while absorbing a full direction
(~110 words of pre-existing prose compressed away against ~186 added), scripted set-diff
**129 codes in, 144 out, ZERO dropped**; the row then joined `check-gapmap-cells.py`'s
`SPECIAL_CAPS` at **1 630 / 150** — **withdrawn by the coordinator the same day**, the
row being compliant at 1 546 under the generic 1 600. The recompute stands; the ceiling does
not move. Reason in `check-gapmap-cells.py`'s docstring.

## Reserved namespace — direction BSATUR (2026-09-02, **CONSUMED IN FULL**)

**Reserved 2026-09-02 for the single direction BSATUR** (ordinal 65, the arc's
seventy-third direction; `notes/Pencil-fanout.md` §"BSATUR") — **(PENCIL-SATURATES)**,
*`dim(ρ̄_i ∩ Π) = 2 ⟹ ρ_i = 6`*, the clause BDOUBLE's redundancy theorem ((BE-101)) is
conditional on. Coordinator-set, single dispatch — **not** a fan-out, so this reservation
protects against the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSATUR** | §(K-bare-ext) — **extends**, no new section | **(BE-104)–(BE-108)** | **BE103–BE107** | `w4/bsatur.py` (expected — extend `bdouble.py`'s four modes and `bunif.py`'s block/profile instruments by read-only import) |

The reservation opens at **(BE-104) / Step BE103**, exactly the tail **BDOUBLE declared**.
Both tokens have **two hits each**, opened and confirmed to be that declaration in its two
homes — this registry's BDOUBLE row and `notes/Pencil-fanout.md` §"BDOUBLE" — not consumed
labels. (BDOUBLE declared its tail in **both** places, which is one better than BUNIF's one
and two better than BBASE's none; the habit is worth keeping.)

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in both cases**: `BSATUR`, `bsatur`,
`bsatur.py`, `(BE-105)`–`(BE-108)` and the raw step tokens `BE104`–`BE107` each **0-hit**.

**Checked and NOT chosen:** `BSAT` (0-hit both cases, but it reads as *satisfiability*, a
different subject the corpus does discuss) and `BPTRAP` (0-hit, but it names the
**coordinator's reading** — that the target may be (BE-33)'s (P) trap read as vacuity —
rather than the target, which is exactly what `RESEARCH-ARC.md` §7 warns against baking
into a code; the reading is offered as a candidate for the **INAPPLICABLE** kind and may
well die). **`BSATUR` names the condition, not a predicted answer.**

**(L6) reminder for the landing.** Run the landing-time bare-token grep. Live risks:
**`(S1)`/`(S2)`**, three owners — write *"§(K-bare-ext)'s own two window conditions"* as
BBASE, BUNIF and BDOUBLE all did. **Mint nothing** for `Π_x`, `c_i(U)`, `ρ_i`, the
**(P)/(Z)/(R)** traps, `margin`, `blockcap`/`blockdeg` or the double pencil: all existing
prose/symbol names, and this section has now gone **five** directions without minting a
configuration-level token.

**Gap-map note (F21) — read the gate's docstring first.** The `(K-bare)` row was at
**1 546 / 1 600 words**, 54 spare. BDOUBLE recomputed to that and then added a
`SPECIAL_CAPS` entry at 1 630; **the coordinator withdrew it** the same day — the row was
**compliant**, and every other entry in that table exists for a row that had *exceeded* its
cap, each with a density argument. The docstring states the rule: **no overflow, no bump.**

**LANDED 2026-09-02.** Labels **(BE-104)–(BE-108)** and ***Steps BE103–BE107*** are
**consumed in full**; nothing returned. The driver landed at the reserved path
`notes/scripts/w4/bsatur.py`, and one further script — `notes/scripts/gapdiff.py`, the F21
set-diff BDOUBLE did not retain — is shipped with it. **One** name minted, a *condition*
rather than an object: **(PENCIL-SATURATES-GEN)** (0-hit at reservation time and at
landing). Nothing minted for `Π_x`, `c_i(U)`, `ρ_i`, the (P)/(Z)/(R) traps or the double
pencil; `Σ_x` is BUNIF's existing symbol and *"the bad plane"* is plain prose. **(L6)
landing grep run**: `(S1)`/`(S2)` written as *"§(K-bare-ext)'s own two window conditions"*.
**F21 discharged**: the `(K-bare)` row recomputed **1 546 → 1 466** words (134 spare, no
`SPECIAL_CAPS` entry added), label preservation by scripted set-diff — **130 in, 137 out,
ZERO dropped**. **The tail this direction declares, for the next reservation:
(BE-109) / Step BE108.**

## Reserved namespace — direction GPACK (2026-09-02, **LANDED**)

**Reserved 2026-09-02 for the single direction GPACK** (ordinal 66, the arc's
seventy-fourth direction; `notes/Pencil-fanout.md` §"GPACK") — **(GR-18)(iii)**, the
grouping problem, and **the arc's first `hK`-side direction in 22 dispatches**.
Coordinator-set, single dispatch — **not** a fan-out, so this reservation protects against
the *existing corpus* only.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GPACK** | §(K-grid) (`notes/Pencil-informal-grid.md`) — **extends**, no new section | **(GR-129)–(GR-133)** | **G149–G153** | `w4/gpack.py` (expected — extend `gridcol.py`'s `--pack` and `packmm.py`/`gridwit.py` by read-only import) |

**This is the first reservation on the `GR-` tail since GMINM (ordinal 36, 2026-08-26)** —
21 directions on other namespaces — and it opens exactly where GMINM **returned**. GMINM
reserved (GR-125)–(GR-129) and *Steps G145–G149*, consumed only through **(GR-128)/G148**,
and its registry row states: *"(GR-129) and Step G149 were NOT needed and are RETURNED — the
live tail is therefore (GR-129)+ / Step G149+."*

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in both cases**: `GPACK`, `gpack`,
`gpack.py`, `(GR-131)`–`(GR-133)` and the raw step token `G151` each **0-hit**.
**`(GR-129)`/`(GR-130)` and `G149`/`G150` have hits — every one opened and confirmed to be
the RETURN RECORD**, in GMINM's registry row, its fan-out section, and one
*checked-and-not-chosen* note; none is a consumed label.

**Checked and NOT chosen.** **`GGROUP`** (0-hit) — *group* now collides with a **live
technical object in the sibling thread**, BUNIF's stabilizer `S(ϕ) ⊆ PGL₄` and its maximal
torus, so a `GGROUP`-tagged claim would read ambiguously in a corpus where both threads are
cited together; that is exactly the (L5) overlap the rule exists to catch, and it is the
first time a *cross-thread* collision has driven a naming decision. **`GBIS`** (0-hit) —
names the **coordinator's framing** (*equitable bisection*) rather than the target, which
§7 warns against. **`GPACK` names the object the two freedoms act on**, and not a predicted
answer.

**(L6) reminder for the landing.** Run the landing-time bare-token grep. Live risks on this
namespace: bare **`(C6)`/`(C7)`** (this file's oldest recorded collision, §(SAFE-RES) vs
§(K-slide-comb)); **`(R1)`/`(C1)`/`(C2)`**, renamed to `(GR-R1)`/`(GR-C1)`/`(GR-C2)` by the
2026-08-20 user call — **do not re-mint the bare forms**; and `A(β)`, `C_β`, `J`, `Ĝ`,
`D_β`, which are *Step G21*'s own symbol names — **reuse them, mint nothing**.

**LANDED 2026-09-02 — the whole reservation CONSUMED, nothing returned.** (GR-129)–(GR-133) and *Steps G149–G153* are all written, in `notes/Pencil-informal-grid.md` §(K-grid), which the direction **extends** exactly as reserved; driver `w4/gpack.py` as named. **(L6) landing grep run**: the bare `(C6)` appears three times in the new steps, twice written `§(K-slide-comb) (C6)` and once inside a direct quotation of that result's own remark (c), in a sentence that names §(K-slide-comb) twice — unambiguous, no rename; `(C7)`, `(R1)`, `(C1)`, `(C2)` **0-hit**. *Step G21*'s symbols `A(β)`, `C_β`, `J`, `Ĝ`, `D_β` reused and nothing re-minted; the newly named objects are `σ(F)` (the sparsity slack), the signing `s`, `H₀`, `N₃` and *the split graph*, which is deliberately left **unlettered** because `P` was already carrying two jobs in §(K-grid) ((GR-8)'s subgraph, and this direction's own signing subset `P ⊆ O`). **F21 discharged**: the `(K-grid)` row recomputed to an explicit target of **≤ 2 500** status words and landing at exactly **2 500 / 2 715** (close-it **980 / 985**), no `SPECIAL_CAPS` entry proposed and none needed — the row was under cap before and after; label preservation by `notes/scripts/gapdiff.py`, **135 in, 141 out, ZERO dropped, 6 added**. **The tail this direction declares, for the next reservation: (GR-134) / Step G154.**

**Gap-map note (F21) — this is the corpus's biggest row.** `(K-grid)` stood at **2 390 /
2 715 status words** at reservation time (**2 500** after this landing), the one row with a `SPECIAL_CAPS` entry, bumped three times and every
time **because it had overflowed**. **Recompute to a target**; label preservation by
`python3 notes/scripts/gapdiff.py`, now mandated by `notes/CLAUDE.md` for any recompute.
**No overflow, no bump** — the gate's docstring records a bump proposed and **withdrawn**
on 2026-09-02 for exactly that reason.

## Reserved namespace — direction BSIGMA (2026-09-02, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved and consumed on 2026-09-02 for the single direction BSIGMA** (ordinal 67, the
arc's seventy-fifth direction; `notes/Pencil-fanout.md` §"BSIGMA") — **(BE-107)(iii)**,
BSATUR's own named residual. **This reservation was never a separate commit**: BSIGMA ran
**draft-only** in parallel with a committing direction, so its spec and its labels were
carried in the invocation prompt and land here with the write-up. That is
`RESEARCH-ARC.md` §2's serial-landing pattern, and this row is its registry record.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSIGMA** | §(K-bare-ext) — **extends**, no new section | **(BE-109)–(BE-113)** | **BE108–BE112** | `w4/bsigma.py` (six modes) |

**0-hit verification, at reservation time** (coordinator-run, before dispatch), across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`/`__pycache__` excluded, **in
both cases**: `BSIGMA`, `bsigma`, `bsigma.py`, `(BE-110)`–`(BE-113)` and the raw step tokens
`BE109`–`BE112` each **0-hit**; `(BE-109)` and `BE108` had one hit each, opened and confirmed
to be BSATUR's tail declaration. `BKILL` was checked (0-hit) and **not chosen** — it names a
**predicted outcome**, which `RESEARCH-ARC.md` §7 warns against baking into a code, and the
direction could equally have returned a clean miss.

**CONSUMED IN FULL.** (BE-109)–(BE-113) and *Steps BE108–BE112* all used; **nothing
returned**. **One** name minted, a *condition* and not an object, mirroring BSATUR's
precedent: **(PENCIL-SATURATES-CHART)**. Nothing minted for `Σ_x`, `Π_x`, `ρ̄_i`, `c_i(U)` or
the flag regime — *the tail stratum* and *the projected pair lines* stay plain prose. The
section has now gone **seven** directions without a configuration-level token.

## Reserved namespace — direction BPROPER (2026-09-02, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved and consumed on 2026-09-02 for the single direction BPROPER** (ordinal 69;
`notes/Pencil-fanout.md` §"BPROPER") — (BE-113)(i) item 1's own designated successor target.
Like BSIGMA, **this reservation was never a separate commit**: BPROPER ran **draft-only** in
parallel with a committing dispatch, so its spec and its labels were carried in the
invocation prompt and land here with the write-up (`RESEARCH-ARC.md` §2).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BPROPER** | §(K-bare-ext) — **extends**, no new section | **(BE-114)–(BE-121)** | **BE113–BE120** | `w4/bproper.py` (eight modes) |

**0-hit verification, at reservation time** (coordinator-run, before dispatch) **and re-run
by the direction as its first action**, across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2`:
`BPROPER`, `bproper`, `bproper.py`, `(BE-115)`–`(BE-121)` and the raw step tokens
`BE114`–`BE120` each **0-hit**; `(BE-114)` and `Step BE113` had exactly one hit each, opened
and confirmed to be BSIGMA's own tail declaration. **`BSWEEP` was checked (0-hit) and NOT
chosen** — it names the *method* the coordinator predicted (sweeping the projected pair
lines), which the direction did not use; `BPROPER` names the **property being decided**, not
a predicted answer and not a predicted route, which is what `RESEARCH-ARC.md` §7 asks.

**CONSUMED IN FULL.** (BE-114)–(BE-121) and *Steps BE113–BE120* all used; **nothing
returned**. **Nothing is minted** — not for the core space `A`, the pendant reduction, the
incidence lemma, or the `p_x`-sweep input, all of which stay plain descriptive prose, per
the constraint BSATUR and BSIGMA both honoured. The section has now gone **eight**
directions without a configuration-level token. **(L6) landing grep run** over the new
steps: no bare `(X<digit>)` token is minted anywhere; `(C6)`/`(C7)`, `(R1)`/`(C1)`/`(C2)`
all **0-hit** in the new text.

**The next tail is (BE-122) / *Step BE121***, 0-hit verified at landing.

**Gap-map note (F21) — the set-diff earned its keep a THIRD time, and in a NEW way.**
`notes/scripts/gapdiff.py` has now caught a dropped label (BSIGMA) and, on this landing, a
**malformed row**: the direction's first assembly of the recomputed row omitted the row's
trailing `` ` |` `` delimiter, so the gate's parser resolved only the status cell and
reported *3 DROPPED* — (BE-57), (BE-57)(iv), (BE-97)(iv), **all three of which live in the
close-it cell**. `notes/check-gapmap-cells.py` **passed** on the same malformed row.
Repaired before return; the gates then read **1 538 → 1 499 words, 143 in, 155 out, ZERO
dropped, 12 added**, against an explicit target of ≤ 1 500 (≥ 100 words of headroom, up from
62). Two lessons for a successor: the set-diff is a **shape** check as well as a content
check, and a row assembled programmatically must be **round-tripped through the gate's own
parser** before it is quoted.

**A second mechanics finding, and it is about this file's own discipline.** A draft-only
dispatch running beside a committing sibling must **diff against `HEAD`, never against the
working tree**. BPROPER did that correctly for the gap map (`gapdiff.py K-bare HEAD`) and
*incorrectly* for the phase note, reading `notes/Phase39.md`'s line and status-word counts
off a sibling's **uncommitted** edits. The gap-map work was sound for exactly that reason.
The **session scratchpad is likewise shared** between concurrent dispatches — two files
under generic names were overwritten mid-round — so **prefix every scratch file with the
direction code**, and **re-verify any scratch input against `HEAD` immediately before
consuming it**. Both belong to `RESEARCH-ARC.md` §2, which today covers only tracked-file
contention.

**Gap-map note (F21) — and the set-diff earned its keep on its second outing.** The draft's
own Appendix B **dropped the citation `(BE-107)(iii)`** from the status column — the very
residual this direction realized. `check-gapmap-cells.py` passed; **`gapdiff.py` failed**
(*137 in, 142 out, 1 DROPPED*). Repaired at landing by keeping the citation with its new
status. The coordinator's **own** first compression attempt was then thrown away for
dropping the same label *and lengthening the row*; the row finally went **1 466 → 1 538 /
1 600, zero dropped**, by folding superseded mechanism prose rather than history. **No
`SPECIAL_CAPS` entry proposed or added.**

## Reserved namespace — direction GLIST (2026-09-02, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved 2026-09-02 for the direction GLIST** (ordinal 68; `notes/Pencil-fanout.md`
§"GLIST") — **(GR-132)'s hub list-colouring at the `ℓ = 2`-rich shapes**, the `hK` lane's own
named successor and rank 1 of `notes/Pencil-strategy.md` §8's corrected ranking. The
**committing** dispatch of a concurrent pair; the sibling ran **draft-only on the (BE-14)
thread**, so this reservation protects against the existing corpus *and* against one live
sibling on a disjoint prefix.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GLIST** | §(K-grid) (`notes/Pencil-informal-grid.md`) — **extends**, no new section | **(GR-134)–(GR-138)** | **G154–G158** | `w4/glist.py` |

**It opens at exactly the tail GPACK declared** (*"the tail this direction declares, for the
next reservation: (GR-134) / Step G154"*).

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2`
with `.git`/`.lake`/`__pycache__` excluded: `GLIST` and `glist` each **0-hit as raw
substrings**; `(GR-135)`–`(GR-138)` and the raw step tokens `G155`–`G158` each **0-hit**.
**`(GR-134)` and `Step G154` had two hits, both opened and confirmed to be GPACK's TAIL
DECLARATION** — one in its registry row above, one in its fan-out landing paragraph — not
consumed labels. `GLIST` was checked for the substring hazard (L5) and is clean; *list* alone
would not have been (hundreds of hits inside "listed" / "colouring-existence" prose), which is
why the code carries the topic tag.

**LANDED 2026-09-02 — the whole reservation CONSUMED, nothing returned.** (GR-134)–(GR-138)
and *Steps G154–G158* are all written, in `notes/Pencil-informal-grid.md` §(K-grid), which the
direction **extends** exactly as reserved; driver `w4/glist.py` as named. **(L6) landing grep
run**: **no bare `(X<digit>)` token is minted anywhere in the new steps** — the newly named
objects are the two hub functions `α`, `γ`, the two lists `P_β`/`Q_β`, and the words *pure
hub*, *cross* and *leaf-covering*, all deliberately **unlettered**; *Step G21*'s `A(β)`,
`B(β)`, `C_β`, `D_β`, `J`, `Ĝ` and *Step G149*'s `σ(F)` are **reused, nothing re-minted**.
The bare `(C6)` appears once, written `§(K-slide-comb) (C6)` — qualified per (L3), no rename.
**F21 discharged**: the `(K-grid)` row recomputed to explicit targets set before the edit —
status **≤ 2 530**, landing at **2 528 / 2 715**; close-it **≤ 950**, landing at **949 / 985**
— with the status target set honestly rather than generously *because no landing is queued on
this row* (the concurrent sibling is on `(K-bare)`), and with **135 words compressed out of
nine already-landed entries before a word of new content was added**. No `SPECIAL_CAPS` entry
proposed and none needed. Label preservation by `notes/scripts/gapdiff.py`: **141 in, 146 out,
ZERO dropped, 5 added**. **The tail this direction declares, for the next reservation:
(GR-139) / Step G159.**

## Reserved namespace — direction GGLOB (2026-09-02, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved 2026-09-02 for the direction GGLOB** (ordinal 71; `notes/Pencil-fanout.md`
§"GGLOB") — **(GR-138)'s successor 1, the GLOBAL `(α, γ)` CSP at `D = 0`**, the `hK` lane's
own named successor one direction after GLIST. The **committing** dispatch of a concurrent
pair; the sibling ran **draft-only on the (BE-14) thread**, so this reservation protects
against the existing corpus *and* against one live sibling on a disjoint prefix.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GGLOB** | §(K-grid) (`notes/Pencil-informal-grid.md`) — **extends**, no new section | **(GR-139)–(GR-144)** | **G159–G164** | `w4/gglob.py` |

**It opens at exactly the tail GLIST declared** (*"the tail this direction declares, for the
next reservation: (GR-139) / Step G159"*).

**0-hit verification, at reservation time**, across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2`
at `HEAD` (never against the working tree — the concurrent sibling leaves it dirty, which is
`RESEARCH-ARC.md` §2's first new hazard): `GGLOB` and `gglob` each **0-hit as raw
substrings**; `(GR-140)`–`(GR-144)` and the raw step tokens `G160`–`G164` each **0-hit**.
**`(GR-139)` and `G159` had two hits each, both opened and confirmed to be GLIST's TAIL
DECLARATION** — one in its registry row above, one in its fan-out landing paragraph — not
consumed labels. `GGLOB` was checked for the substring hazard (L5) and is clean.

**LANDED 2026-09-02 — the whole reservation CONSUMED, nothing returned.** (GR-139)–(GR-144)
and *Steps G159–G164* are all written, in `notes/Pencil-informal-grid.md` §(K-grid), which the
direction **extends** exactly as reserved; driver `w4/gglob.py` as named. **(L6) landing grep
run**: the only `(X<digit>)`-shaped token anywhere in the new steps is **`(F11)`**, the
dispatch-log finding code the *Verification* block cites by long-standing convention (GLIST's
own block does the same) — **no label is minted in that shape**. The newly named objects are
the **cell** `h(u)`, the row/column pair `(P, Q)`, *head*/*tail*, *head-independent*, and the
three **tiers**, all deliberately **unlettered**; `α`, `γ`, `P_β`, `Q_β`, `C_β`, `D_β`, `J`,
`T_j`, `H`, `σ(F)` are **reused, nothing re-minted**. The bare `(C6)` does not appear.
**F21 discharged**: the `(K-grid)` row was recomputed to explicit targets set *before* the
edit — status **≤ 2 680**, landing at **2 679 / 2 715**; close-it **≤ 970**, landing at
**964 / 985** — with the targets set honestly rather than generously because **no landing is
queued on this row** (the concurrent sibling is on `(K-bare)`), and with **two landed clauses
compressed before a word of new content was added**. No `SPECIAL_CAPS` entry proposed and
none needed. Label preservation by `notes/scripts/gapdiff.py K-grid HEAD`: **146 in, 154 out,
ZERO dropped, 8 added**. **The tail this direction declares, for the next reservation:
(GR-145) / Step G165.**

## Reserved namespace — direction BOPEN (2026-09-02, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved and consumed on 2026-09-02 for the single direction BOPEN**
(ordinal 72; `notes/Pencil-fanout.md` §"BOPEN") — (BE-121)(i) item 1's own
designated successor, *"the passage from proper to generic … a chart question
rather than a configuration hunt"*. Like BSIGMA and BPROPER, **this
reservation was never a separate commit**: BOPEN ran **draft-only** in
parallel with a committing dispatch, so its spec and its labels were carried
in the invocation prompt and land here with the write-up (`RESEARCH-ARC.md`
§2).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BOPEN** | §(K-bare-ext) — **extends**, no new section | **(BE-122)–(BE-128)** | **BE121–BE127** | `w4/bopen.py` (eight modes) |

**It opens at exactly the tail BPROPER declared** (*"The next tail is (BE-122)
/ Step BE121, 0-hit verified at landing"*).

**0-hit verification, re-run by the direction as its first action**, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` with `.git`/`.lake`/`__pycache__`
excluded: `BOPEN`, `bopen`, `bopen.py`, `(BE-123)`–`(BE-129)` and the raw step
tokens `BE122`–`BE127` each **0-hit**; `(BE-122)` and `BE121` had exactly one
hit each, opened and confirmed to be **BPROPER's own tail declaration**
(`notes/Pencil-labels.md:3232`), not consumed labels. **`BGENERIC` was checked
and NOT chosen** — it names the **predicted answer**, which `RESEARCH-ARC.md`
§7 warns against baking into a code; `BOPEN` names the **question** (the
passage from proper to generic, i.e. whether the good locus is *open*), and
the direction's answer is that openness is the wrong property, which a code
naming the answer would have prejudged.

**CONSUMED IN FULL.** (BE-122)–(BE-128) and *Steps BE121–BE127* all used;
**nothing returned**. **Nothing is minted** as an object name — not for the
bad loci `B`/`B_str`, the rotation fibre, the tower slide or the condition
`(∗)`, all of which stay plain descriptive prose (`(∗)` is a *marker*, not a
label: it is a bare asterisk in parentheses, matched by no registry regex, and
it is qualified as *"§(K-bare-ext) (BE-127)(ii)'s `(∗)`"* wherever it is cited
outside its own step). The section has now gone **nine** directions without a
configuration-level token. **(L6) landing grep**: no bare `(X<digit>)` token is
minted anywhere in the new steps; `(C6)`/`(C7)`, `(R1)`/`(C1)`/`(C2)` all
**0-hit** in the new text.

**The next tail is (BE-129) / *Step BE128***, 0-hit verified at this landing.

**Gap-map note (F21).** The `(K-bare)` row was recomputed to an **explicit
target set before the edit — ≤ 1 500 words, i.e. ≥ 100 of headroom**, the same
target BPROPER met and honest rather than generous **because no landing is
queued on this row** (the concurrent sibling is on `(K-grid)`). It lands at
**1 499 / 1 600**, i.e. **exactly level with `HEAD`** — the whole of a
theorem-sized landing absorbed by folding **mechanism superseded as headline**
(BUNIF's stabilizer derivation, BDOUBLE's realization narrative, BSATUR's and
BSIGMA's refutation mechanisms, BPROPER's incidence count), **never history**:
every label those passages carried is still cited. Verified by round-tripping
the assembled row through **both gates' own code** — `iter_row_cells` and
`gapdiff.labels_of`/`CODE`, in memory, since a draft-only dispatch may not
touch the tracked file — at **155 in, 171 out, ZERO dropped, 16 added**. The
convention-0 hazard fired **again and was caught the same way**: the first
assembly dropped the row's trailing `` ` |` `` and the set-diff reported **3
DROPPED** ((BE-57), (BE-57)(iv), (BE-97)(iv)) while the cap gate passed — the
**third** time that shape has been caught by the set-diff and the second by
this exact mechanism.

**A gate artifact, recorded so the next recompute is not surprised by it.**
`notes/check-gapmap-cells.py`'s default mode detects a changed row by
comparing **word counts**, not text — so a recompute that lands at *exactly*
the pre-edit count is invisible to it and it reports *"0 gap-map row(s)
checked"*. That is what happened here (1 499 → 1 499). It is not a failure —
the cap is satisfied either way — but it means the default run **certifies
nothing** about such a row: run `python3 notes/check-gapmap-cells.py --all`
(28 rows, all within cap, run at this landing) and rely on
`notes/scripts/gapdiff.py`, which compares **label sets** and did see the
change (155 in, 171 out). Two gates, two different notions of "changed"; a
row can be invisible to one and not the other.

## Reserved namespace — direction BLINE (2026-09-02, **CONSUMED IN FULL at the landing; nothing returned**)

**Reserved and consumed on 2026-09-02 for the single direction BLINE**
(ordinal 73; `notes/Pencil-fanout.md` §"BLINE") — BOPEN's own designated
residue, *prove or refute §(K-bare-ext) (BE-127)(ii)'s `(∗)`*, which
`notes/Phase39.md` *Hand-off* item 0(a) carries as half (B)'s last open
sub-item. A **single, committing** dispatch: no sibling was in flight, so
the tree was clean at reservation time and the corpus check had nothing to
protect against but the corpus itself.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BLINE** | §(K-bare-ext) — **extends**, no new section | **(BE-129)–(BE-135)** | **BE128–BE134** | `w4/bline.py` (six modes) |

**It opens at exactly the tail BOPEN declared** (*"The next tail is (BE-129)
/ Step BE128"*).

**0-hit verification, re-run by the direction as its first action**, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`** (`git grep`, not a
working-tree grep — `RESEARCH-ARC.md` §2's first concurrency hazard, obeyed
even though no sibling was running, because the run itself dirties the tree
with the new driver): `BLINE` and `bline` each **0-hit as raw substrings**;
`(BE-130)`–`(BE-135)` and the raw step tokens `BE129`–`BE134` each
**0-hit**. **`(BE-129)` has two hits and `BE128` one, all three in BOPEN's
own reservation block** (`notes/Pencil-labels.md:3369` — its excluded-range
line — and `:3390`, its tail declaration): a **declaration**, not a consumed
label. `BLINE` was checked for the substring hazard (L5) and is clean; it
names the **object** (`L_c`, the fixed line the whole condition is
quantified over) and not the answer, which `RESEARCH-ARC.md` §7 warns
against — the answer turned out to be *refuted on a stratum*, which a code
naming a predicted verdict would have prejudged in either direction.

**CONSUMED IN FULL.** (BE-129)–(BE-135) and *Steps BE128–BE134* are all
written, in `notes/Pencil-informal.md` §(K-bare-ext), which the direction
**extends** exactly as reserved; driver `w4/bline.py` as named. **Nothing is
minted** as an object name: `z`, `W`, `B`, `b`, `V`, `L_c`, `Σ_t`, `Λ²π'`,
`A` are all **reused or plain symbols**, and BOPEN's convention that **`(∗)`
is a marker, not a label** is kept — it is still a bare asterisk in
parentheses, matched by no registry regex, still qualified as *"§(K-bare-ext)
(BE-127)(ii)'s `(∗)`"* wherever cited outside its own step. The section has
now gone **ten** directions without a configuration-level token. **(L6)
landing grep run** over the new text: the only `(X<digit>)`-shaped tokens
anywhere in it are **`(E1)`/`(E2)`/`(E3)`** (the termination ledger's own
codes) and **`(F13)`** (a dispatch-log finding code) — both long-standing
citation conventions that BOPEN's block uses identically, and **no label is
minted in that shape**. `(C6)`, `(C7)`, `(R1)`, `(C1)`, `(C2)` are all
**0-hit** in the new text.

**The next tail is (BE-136) / *Step BE135***, 0-hit verified at this
landing.

**Gap-map note (F21).** The `(K-bare)` row was recomputed to an **explicit
target set before the edit — ≤ 1 540 words, i.e. ≥ 60 of headroom** (BOPEN
targeted ≤ 1 500 and landed at 1 499; this direction's own content is a
refutation plus a classification plus a correction to two surfaces, so the
target is 40 words looser and still honest, no landing being queued on the
row). It lands at **exactly 1 540 / 1 600**, i.e. **+41 on `HEAD`**, with
**every one of those 41 words paid for**: roughly two dozen landed passages
were compressed in the same pass, all of them **mechanism
superseded as headline** (the (BE-122)/(BE-123) semicontinuity argument, the
(BE-124) tower sentence, the (BE-125) rotation, the (BE-94)/(BE-96)
stabilizer split, the (BE-89)–(BE-93) flag-base derivation, the (BE-84)–(BE-88)
hinge-pair narrative) and **never history** — every label those passages
carried is still cited. Verified by `notes/scripts/gapdiff.py K-bare HEAD`:
**171 in, 180 out, ZERO dropped, 9 added**.

**And the set-diff caught a real drop, on the first assembly** — the third
time this file records that shape. The compression pass dropped **`(K-bare-ext)`
and `(K-chart)`**, both of them *section* labels sitting inside prose the
recompute shortened (*"§(K-bare-ext)'s two window conditions"*,
*"§(K-chart)'s tower"*), while `notes/check-gapmap-cells.py` passed and the
word count looked healthy. A section label is the easiest kind to lose,
because it reads as scenery rather than as a citation. Both were restored
in the same pass, at a cost of two words.

## Reserved namespace — direction BDEGTWO (2026-09-03, **CONSUMED IN FULL at the landing; two labels returned**)

**Reserved and consumed on 2026-09-03 for the single direction BDEGTWO**
(ordinal 74; `notes/Pencil-fanout.md` §"BDEGTWO") — *does half (B)'s item 1
close at side-degree `≥ 2`, and what exactly is missing?*, i.e. BLINE's own
two named residues (BE-134)(i)/(ii). One of a **concurrent pair**; the
sibling ran the **(K-res)** lane and shares no section, label family or
driver, so the reservation protects against the corpus rather than against a
sibling — but the tree was **dirty** for the whole run (the sibling's own
untracked driver), which is why every check below is against `HEAD`
(`RESEARCH-ARC.md` §2's first concurrency hazard).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BDEGTWO** | §(K-bare-ext) — **extends**, no new section | **(BE-136)–(BE-143)**, of which **(BE-136)–(BE-141)** consumed | **BE135–BE142**, of which **BE135–BE140** consumed | `w4/bdegtwo.py` (six modes) |

**It opens at exactly the tail BLINE declared** (*"The next tail is (BE-136)
/ Step BE135"*). **Two labels and two steps are RETURNED UNUSED**:
(BE-142)/(BE-143) and *BE141*/*BE142* were reserved against a wider result
than the direction needed, and are **available**.

**0-hit verification, re-run by the direction as its first action**, across
`*.md`, `*.py` (and by the same `git grep` over `*.tex`/`*.lean`/`*.m2`)
**at `HEAD`**: `BDEGTWO` and `bdegtwo` each **0-hit as raw substrings**;
`(BE-137)`–`(BE-143)` and the raw step tokens `BE136`–`BE142` each
**0-hit**. **`(BE-136)` has exactly one hit and `BE135` three** — BLINE's
own tail declaration (`notes/Pencil-labels.md:3470`) carries both, and the
two further `BE135` hits are `notes/Pencil-strategy.md`'s **`BE129–BE135`**
range citations (its §9 thread line and its §8 board row), i.e. a
**declaration plus two citations of a WRONG range**, not consumed labels —
see the citation repair below. `BDEGTWO` was checked for the substring hazard (L5) and is
clean; it names the **stratum** (side-degree `≥ 2`) and not a method or a
verdict, `BSWEEP` having been rejected by this registry for naming a
*predicted method* — which was the right call twice over, since the sweep
turned out to be the **easy** half and a code named for it would have
implied the direction was about building one.

**A citation repaired at this landing.** `notes/Pencil-strategy.md` recorded
BLINE as *"Steps BE129–BE135"* in **two** places (§9's thread line and §8's
`(K-bare)` board row). That is BLINE's **label** range; its **step** range is
*BE128–BE134*. Both are corrected, and both now read *BDEGTWO (Steps
BE135–BE140)*. The confusion is exactly what clause (L2) — *never label a
step* — exists to prevent: the two ranges are offset by one throughout this
section, because a step `BEn` carries label `(BE-(n+1))`.

**CONSUMED IN FULL.** (BE-136)–(BE-141) and *Steps BE135–BE140* are all
written, in `notes/Pencil-informal.md` §(K-bare-ext), which the direction
**extends** exactly as reserved; driver `w4/bdegtwo.py` as named. **Nothing
is minted** as an object name: `Bad`, `F`, `A_sharp`, `W`, `M`, `B`, `r`,
`s`, `a(m)`, `N` are all **plain symbols or reused**, and BOPEN's convention
that **`(∗)` is a marker, not a label** is kept. The section has now gone
**eleven** directions without a configuration-level token. **(L6) landing
grep run** over the new text: the only `(X<digit>)`-shaped tokens anywhere in
it are **`(E1)`/`(E2)`/`(E3)`** (the termination ledger's codes), **`(F13)`**
(a dispatch-log finding code) and **`(L2)`/`(L5)`/`(L6)`** (this file's own
clause codes, cited only in this block); **no label is minted in that
shape**, and `(C6)`, `(C7)`, `(R1)`, `(C1)`, `(C2)` are all **0-hit** in the
new text.

**Gap-map note (F21), and the set-diff caught a drop for the FOURTH time.**
The `(K-bare)` row was recomputed to an **explicit target before the edit —
≤ 1 545 words, i.e. ≥ 55 of headroom** (BLINE targeted ≤ 1 540 and the row
stood at 1 554 at `HEAD` after the liveness round; this direction's own
content is one dissolved gap, one closed-form criterion and one located
obstruction, so ~105 new words were budgeted and paid for by compressing
**fourteen** landed passages, every one of them *mechanism superseded as
headline* — the (BE-122) semicontinuity clause, the (BE-124) tower sentence,
the (BE-125) rotation, the (BE-129)/(BE-131) classification narrative, the
(BE-45)/(BE-99)–(BE-101) corner derivation, the (BE-69) openness warrant,
the (BE-94)–(BE-96) stabilizer split, the (BE-84)–(BE-86) hinge-pair
narrative — and **never history**). It lands at **1 539 / 1 600**, i.e.
**−15 on `HEAD`**, beating the target. Verified by
`notes/scripts/gapdiff.py K-bare HEAD`: **180 in, 186 out, ZERO dropped, 6
added**.

**The drop it caught, on the first assembly**, was **two** labels:
`(BE-124)(i)` — carried only by the sentence *"no `p_x`-sweep exists at
`k ≥ 2` ((BE-124)(i)'s own hypothesis)"*, which this direction **refutes as
an obstruction claim**, so the natural edit deleted the citation along with
the claim — and `(BE-45)(ii)`, lost to the *abbreviation* `(BE-45)(i)/(ii)`,
which `gapdiff`'s `CODE` regex reads as `(BE-45)(i)` plus a bare `(ii)`.
Both were restored (`(BE-45)(i)/(BE-45)(ii)`, spelled out; and (BE-124)(i)
re-cited inside the refuting clause, *"(BE-124)(i)'s hypothesis was not
load-bearing"*), at a cost of eleven words. **Two new shapes for this file's
list:** a label lost because *the claim carrying it was refuted* — the
refutation is exactly when the citation matters most, since a reader must be
able to find what was refuted — and a label lost to a **slash
abbreviation** of two sub-items of the same label, which reads as one
citation and parses as one and a half.

**The next tail is (BE-142) / *Step BE141***, 0-hit verified at this landing
(the pair returned unused above), so a successor opens there and **not** at
(BE-144). **CONSUMED 2026-09-03 by direction BSCOND — see the block below.**

**Reserved and consumed on 2026-09-03 for the single direction BSCOND**
(ordinal 76; `notes/Pencil-fanout.md` §"BSCOND") — *prove or refute
(BE-57)(iv)'s two window conditions (S1) and (S2)*, the ninth strategy
pass's rank 1 and half (β)'s only residue since BWIN (ordinal 51). A
**single** dispatch, so the reservation protects only against the corpus;
every check below is nonetheless against `HEAD`, per `RESEARCH-ARC.md` §2's
first concurrency hazard.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSCOND** | §(K-bare-ext) — **extends**, no new section | **(BE-142)–(BE-149)**, of which **(BE-142)–(BE-148)** consumed | **BE141–BE148**, of which **BE141–BE147** consumed | `w4/bscond.py` (eight modes) |

**It opens at exactly the tail BDEGTWO declared** (*"The next tail is
(BE-142) / Step BE141"*), and **not** at (BE-144). **One label and one step
are RETURNED UNUSED**: **(BE-149)** and ***Step BE148***, reserved against a
wider result than the direction needed, and **available**.

**0-hit verification, re-run by the direction as its FIRST action**, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`**: `BSCOND` and
`bscond` each **0-hit as raw substrings** (case-insensitively);
`(BE-145)`–`(BE-149)` and the raw step tokens `BE143`–`BE148` each **hard
0-hit**. **The carve-out the coordinator flagged is CONFIRMED in its
conclusion and CORRECTED in its counts:** the prep said `(BE-142)`/`(BE-143)`
and `BE141`/`BE142` had *"exactly one hit, in `notes/Pencil-labels.md`
only"*; the re-run at `HEAD` measured **`(BE-142)` 2, `(BE-143)` 3,
`(BE-144)` 1, `BE141` 2, `BE142` 3** — **all in this file only, and all
declarations**: BDEGTWO's reservation range row, its two-labels-returned-
unused note, its *"The next tail is (BE-142) / Step BE141"* pointer and its
*"and **not** at (BE-144)"* clause. **None is a consumed label**, so the
conclusion stands. **The CAUSE the landing gave for the discrepancy is WRONG,
and is corrected here by the coordinator (2026-09-03), because the lesson it
drew is the wrong check to teach.** It read *"the prep's check predated the
ninth strategy pass's own commit (`3c49ce60`) … a live instance of diff
against `HEAD`, never a stale check"*. The prep's check was **not** stale — it
ran at `HEAD = 3c49ce60`, and the counts are **byte-identical at `89eb1fdb`
and `3c49ce60`** (re-measured both: `(BE-142)` 2, `(BE-143)` 3, `(BE-144)` 1,
`BE141` 2, `BE142` 3 at each), so that commit moved none of them. The real
cause is a **metric conflation in the coordinator's own command**: the prep
ran `git grep -c -- TOKEN | wc -l`, which counts **files containing a match**,
and reported the result as **hits**. One file, five different hit counts — the
number was a file count throughout, and the *conclusion* (one file, all
declarations) was right for exactly that reason. **The check to teach:
`git grep -c | wc -l` counts FILES; `git grep -o | wc -l` counts HITS — and a
reservation must say which metric it reports.** Recorded rather than silently
fixed, because a wrong cause on this file's reservation discipline would have
future directions re-running a check that was never the problem.

**`BSCOND` was checked for the substring hazard (L5)** and is clean; it names
the **object** (the window's *side conditions*), not a method and not a
verdict. **`BMID` was REJECTED at reservation** for priming the answer — and
this registry had rejected the same token once before, **at BWIN's own
reservation**, for the same reason. That is now two rejections of one token
on one ground, which is worth stating as a pattern: *a code naming the
object the claim is ABOUT is safe; a code naming the object the claim
PREDICTS is not* (`BSWEEP`, rejected at BDEGTWO, is the third instance and
the one where the rejection was vindicated).

**CONSUMED IN FULL.** (BE-142)–(BE-148) and *Steps BE141–BE147* are all
written, in `notes/Pencil-informal.md` §(K-bare-ext), which the direction
**extends** exactly as reserved; driver `w4/bscond.py` as named. **One object
name is minted**: **`Σ_p := p ∧ K⁴`**, and it is **deliberately not new** —
it is the same object (BE-114)/(BE-116) already write `Σ_x` for on the
half-(B) side, at a different vertex, and the *Standing notation* says so at
its definition rather than presenting it as a fresh construction. `σ`, `q`,
`W`, `V`, `L`, `M`, `λ`, `μ`, `t` are **plain symbols or reused**, and
BOPEN's convention that **`(∗)` is a marker, not a label** is kept (the
marker does not appear in the new text at all). The section has now gone
**twelve** directions without a configuration-level token.

**(L6) landing grep run** over the new text: the only `(X<digit>)`-shaped
tokens anywhere in it are **`(S1)`/`(S2)`** (§(K-bare-ext)'s own inherited
names, minted at BWIN — bare here because this is their owning section, per
(L3); *do not confuse with the `(K-slide)/(S1)` gap-map row*), the
`(BE-nnn)` family, **`(b1)`** ((BE-37)(ii)'s clause), **`(GR-15)`**,
**`(E1)`/`(E2)`/`(E3)`** (the termination ledger's codes) and the sub-item
letters `(a)`/`(b)`. **No label is minted in that shape**; `(C6)`, `(C7)`,
`(R1)`, `(C1)`, `(C2)` are all **0-hit** in the new text.

**Gap-map note (F21) — the row was RECOMPUTED to an explicit target and BEAT
it, and the set-diff again earned its place.** The `(K-bare)` row stood at
**1 539 / 1 600** words at `HEAD`. Target set **before the edit: ≤ 1 530,
i.e. ≥ 70 words of headroom** — strictly more than BDEGTWO left (61), because
this direction's own content is a *decided pair* (seven labels) rather than a
single verdict, and §8's rank 2 is already queued into the same row. It
lands at **1 530 / 1 600 — `−9` on `HEAD`** with the pair added, paid for by
compressing **twenty-two** landed passages, every one of them *mechanism
superseded as headline* (the (BE-30)/(BE-31)/(BE-33)/(BE-34) geometry
paragraph, the (BE-39)/(BE-40)/(BE-74)/(BE-75)/(BE-76) short-cycle law, the
(BE-84)–(BE-93) hinge-pair and flag-base narrative, the (BE-104)–(BE-113)
(PENCIL-SATURATES) chain, the (BE-117)–(BE-124) hunt-verdict passage, the
(BE-59)–(BE-67) R-node and reduction paragraphs, the (BE-136)–(BE-140)
BDEGTWO narrative and the close-it cell's own tail) — and **never history**.
Verified by `notes/scripts/gapdiff.py K-bare HEAD`: **186 in, 195 out, ZERO
dropped, 9 added**. The section column moves `BE1–BE140 → BE1–BE147`.

**The drop it caught, on the first assembly**, was **`K-bare-ext`** — the
row's own section token, carried *only* by the phrase *"**MODULO**
§(K-bare-ext)'s two window conditions"*, which this direction **discharges**,
so the natural edit deleted the citation along with the modulo. Restored by
re-citing the section inside the replacement sentence (*"§(K-bare-ext)'s TWO
WINDOW CONDITIONS ARE DECIDED"*), at a cost of two words. **A third shape for
this file's list**, and the sharpest one yet: a label lost because *the
sentence that carried it was the one being discharged* — the same family as
BDEGTWO's *refuted-claim* drop, but on the row's **own section name**, which
is the one token a reader most needs and the one an author is least likely to
notice, since it reads as prose rather than as a citation.

**The next tail is (BE-149) / *Step BE148***, 0-hit verified at this landing
(the pair returned unused above), so a successor opens there and **not** at
(BE-150).

## Reservation — GLEAF (arc ordinal 80, 2026-09-03, the same CONCURRENT ROUND OF FOUR — its LAST)

**Scope: §(K-grid), which GLEAF *extends* — no new section.** The direction is the ninth
strategy pass's **rank 3**, (GR-144)'s successor 4: *does every 6-tree-partition-carrying
cubic multigraph admit one in which a prescribed set of hubs are each a leaf of some part,
and does the landed Phase-12/13/14 machinery reach that?* Its three siblings (BARCH
§(K-bare-ext), OBAR §(K-out), DSAT §(K-dom)) own disjoint sections and disjoint tags, so
the reservation protects against the corpus and against them.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **GLEAF** | §(K-grid) — **extends**, no new section | **(GR-145)–(GR-152)** (spec offered `(GR-146)`–`(GR-153)`), all eight consumed | ***Steps G165–G172*** (spec offered `G166`–`G173`), all eight consumed | `w4/gleaf.py` (seven modes) |

**DEVIATED DOWN BY ONE to the DECLARED TAIL — this is reservation defect shape FOUR of the
round**, whose diagnosis is in the *Coordinator reservation defects* block below and is
**not duplicated here**. What this row adds is the disposition: GGLOB's landing declares
*"the tail declared for the next reservation is (GR-145) / Step G165"* **verbatim in two
places** (this file and `notes/Pencil-fanout.md` §"GGLOB"), so the opening token was
`(GR-145)`, and the spec's range skipped it. Nothing is renamed (L4); the spec's
`(GR-153)` / *Step G173* are simply **RETURNED UNUSED**. Shape **five** (OBAR, off by two
in §(K-out)) is the *same* error, which is what promoted the diagnosis from five incidents
to one habit.

**The tail declared for the next reservation is (GR-153) / *Step G173***, 0-hit verified at
this landing (the pair returned unused above), so a successor to §(K-grid) opens **there**
and **not** at (GR-154). *Declared verbatim in two places, per the defects block's own
root-cause fix: here, and in `notes/Pencil-fanout.md` §"GLEAF".*

**0-hit verification, re-run by the direction as its FIRST action and again after `HEAD`
moved mid-round**, across `*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`**,
reporting **HITS** (matching lines) and **FILES** separately and covering **every token in
the range rather than sampled endpoints** (shapes 1 and 2's fixes): `gleaf` **0/0**;
`(GR-146)`–`(GR-149)`, `(GR-151)`–`(GR-153)` and every bare `GR-146`–`GR-149`,
`GR-151`–`GR-153` **all 0/0**; `G166`–`G173` **all 0/0**; **`(GR-145)` and bare `GR-145`
2 hits / 2 files**, and **`G165` 2 hits / 2 files**, all four being GGLOB's own tail
declaration — a **declaration, not a consumption**, under the `(BE-149)`/`(DM-5)`/`(OC-56)`
precedent; **`(GR-150)` and bare `GR-150` 1 hit / 1 file**, `notes/gapmap.py:216`'s
docstring example, **repaired in advance by the coordinator** (`a5d8101c`, re-worded to the
unmintable `(GR-15<digit>)`) so the range is clean and nobody need re-find it; and
**`GLEAF` 3 hits / 3 files**, all three the coordinator's own in-flight round-state
notices. **Reservation clean.**

**`HEAD` MOVED DURING THE RUN, and that is a check this file had not had to state.** The
round lands serially, so a draft-only direction's `HEAD` is not fixed: GLEAF's first check
ran at `53bc9740` and its second at `0db16ce3`, after BARCH landed. `RESEARCH-ARC.md` §2's
hazard is *"diff against `HEAD`, never the working tree"*; the mirror image is that **`HEAD`
itself is a moving reference for every direction but the first**, so a reservation check is
re-run at landing time and says which commit it reports.

**Code and basename**: `GLEAF` names the question — the **G**rid section's **LEAF**-covering
successor. The (L6) landing-time bare-token check: every mint is `GR-`-prefixed, and the
landing introduces **no** bare `(X<digit>)` token of its own — the only ones in the new steps
are `(F11)`/`(F13)`, the dispatch-log finding codes the *Verification* block cites by
convention, and `(L7)`, cited from this file. The new objects are deliberately
**unlettered**: the *leaf assignment*, the *cover graph*, the *slack law*, and the criterion's
three *forms*.

## Reservation — DSAT (arc ordinal 79, 2026-09-03, the same CONCURRENT ROUND OF FOUR)

**Scope: §(K-dom), which DSAT *extends* — no new section.** The direction runs
the satisfiability trace `notes/Pencil-strategy.md` §8.2's **C2** row had been
demanding of itself: *is the strengthened motive — the four landed
`IsNondegPencilRealization` conjuncts plus `V_bc` general position —
satisfiable at the objects the induction's consumer hands it?* Its three
siblings (BARCH §(K-bare-ext), OBAR §(K-out), GLEAF §(K-grid)) own disjoint
sections and disjoint tags, so the reservation protects against the corpus and
against them.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **DSAT** | §(K-dom) — **extends**, no new section | **(DM-5)–(DM-11)** (spec offered `(D8)`–`(D14)`), all seven consumed | **D8–D14**, all seven consumed | `w4/dsat.py` (five modes) |

**DEVIATED to the CORRECT FAMILY — this is reservation defect shape THREE of
the round**, whose diagnosis is in the *Coordinator reservation defects* block
below and is **not duplicated here**. What this row adds is the disposition: the
spec's `(D8)`–`(D14)` were abandoned and **`(DM-5)`–`(DM-11)`** minted instead,
continuing §(K-dom)'s claim numbering past `(D4)` in the tag this file assigns
that section, per clause **(L1)** and its own worked example. The reserved
**step** names `D8`–`D14` were **kept** — (L2) writes a step as *Step D8*, never
as `(D8)`, so the step namespace is untouched by the label change. Nothing is
renamed (L4).

**Adjudication — bare `D8` is TAKEN BUT UNRELATED, and stays.**
`git grep -nIwF D8` gives **4 hits / 2 files**: `notes/Phase23-design.md:4012`
and `:4019`, where **Phase 23f's item-4 decomposition runs *Layer* steps
D1–D8**, plus the two `notes/model-experiment-archive.md` rows (`:2078`,
`:2079`) citing `D1–D8`. This is the **grandfathered cross-file collision**
case, resolved by qualification and not by renumbering — the same precedent
`(L1)`/`(L6)`/`(L7)` use: every citation of these steps outside §(K-dom) is
written **`§(K-dom) *Step D8*`** (clause L3), and the collision table above
gains `notes/Phase23-design.md`'s D-range as a fourth colliding home for the
bare `D` family. Phase 23f is a **closed** phase and its steps predate these by
months, so nothing there moves.

**The tail declared for the next reservation is (DM-12) / *Step D15***, 0-hit
verified at this landing (**HITS 0 / FILES 0** for `(DM-12)`, bare `DM-12`,
`(DM-13)`, and bare `D15` at word boundary), so a successor to §(K-dom) opens
**there** — and **not** at `(D15)`, which is not this section's family, nor at
`(DM-13)`. *Declared verbatim in two places, per the defects block's own root-cause
fix: here, and in `notes/Pencil-fanout.md` §"DSAT".*

**0-hit verification, re-run by the direction as its FIRST action**, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`**, reporting **HITS**
(matching lines) and **FILES** separately and covering **every token in the
range rather than sampled endpoints** (shapes 1 and 2's fixes): `dsat` **0/0**;
`(DM-6)`–`(DM-11)` and bare `DM-6`–`DM-11` **all 0/0**; `(D8)`–`(D14)` **all
0/0**; bare `D9`–`D14` **all 0/0**; **`(DM-5)` and bare `DM-5` 1 hit / 1 file**,
this file's own (L1) worked example at `:84` — a **prescription**, not a
consumption, under the `(GR-145)`/`(BE-149)`/`(OC-56)` precedent; **`DSAT` 2
hits / 2 files**, both the coordinator's own in-flight round-state notices in
`Pencil-fanout.md` and this file; and bare **`D8` 4 hits / 2 files**,
adjudicated above. **Reservation clean.**

**(L7) fired again, on the very next range, and in the direction it predicted.**
BARCH minted (L7) because a sampled-endpoint check is *"systematically blind at
the one end where a hit is guaranteed"* — the range's **opening** token. This
range's opening token is `(DM-5)`, and it has **1 hit**: the clause that tells
§(K-dom) to use this tag. A check sampling `(DM-8)` and `(DM-11)` would have
reported 0/0 and missed it. Benign in the same way `(BE-149)`'s and `(OC-56)`'s
hits were — a declaration about the token, not a use of it — but the **method**
point stands, and this is **(L7)'s second confirmation on the day it was
minted**, in a section it had never touched.

**Code and basename**: `DSAT` names the question — the **D**ominance section's
**SAT**isfiability trace. The (L6) landing-time bare-token check: every mint is
`DM-`-prefixed, and the landing introduces **no** bare `(X<digit>)` token of its
own. The bare tokens it *cites* — `(D1)`–`(D4)`, `(T1)`, `(T5)`, `(S1)`,
`(W1)`–`(W4)` by reference, `(PC-Z)`, `(SD-6)`, `(ANH-1)` — are grandfathered or
already tagged, and the bare ones are written L3-qualified at first use outside
their owner (`§(K-pitch) (T1)`, `§(K-dom) (D3)`). **No new section name and no
new tag were minted** — `DM-` was already this section's assigned tag and had
simply never been used, which is exactly how the spec came to offer the wrong
family.

## Reservation — OBAR (arc ordinal 78, 2026-09-03, the same CONCURRENT ROUND OF FOUR)

**Scope: §(K-out), which OBAR *extends* — no new section.** The direction is the
ninth strategy pass's U3 gate, *is `H ∪ {bar along M}` an admissible (OC-35)
subgraph, and what does the unrun ledger say on it?* Its three siblings (BARCH
§(K-bare-ext), GLEAF §(K-grid), DSAT §(K-dom)) own disjoint sections and
disjoint tags, so the reservation protects against the corpus and against them.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **OBAR** | §(K-out) — **extends**, no new section | **(OC-56)–(OC-65)**, of which **(OC-56)–(OC-61)** consumed | **O52–O60**, of which **O52–O57** consumed | `w4/obar.py` (six modes) |

**DEVIATED DOWN, and this is reservation defect shape FIVE of the round.** The
dispatched spec offered **(OC-58)–(OC-65) / O53–O60**. But this file **declares
§(K-out)'s tail verbatim** at OWALL's landing — *"the live tail is therefore
**(OC-56)+ / Step O52+**"* — so the correct opening was **(OC-56) / *Step O52***,
and the spec skipped it **by two labels and one step**, with **no other §(K-out)
direction in the round** to hold `(OC-56)`/`(OC-57)`/`O52`. OBAR opened at the
declared tail and recorded the deviation, per this file's standing lesson
(*"the registry outranks a coordinator's spec on label naming"*) and GLEAF's
same-round precedent of deviating **down** by one. **Shape relative to the four
recorded above:** it is shape 4's *"misread a scan's maximum"* with the sign
flipped — a scan that saw `(OC-56)`/`(OC-57)`/`O52` **present** (in OWALL's own
tail declaration and 0-hit record, 3 hits in this file) and read them as
**consumed** when they were **declarations**. Same root cause: **derived by
scanning the corpus instead of reading the declared tail.** *The defects
block's own count is coordinator-owned and still reads FOUR; this entry is the
fifth instance and is flagged for that increment rather than taken.*

**One label range and one step range are RETURNED UNUSED**: **(OC-62)–(OC-65)**
and ***Steps O58–O60***, reserved against a ten-label span that came in at six,
and **available**. **The tail declared for the next reservation is (OC-62) /
*Step O58***, 0-hit verified at this landing, so a successor opens there and
**not** at (OC-66) — and not at (OC-58) either, which this pass consumed.

**0-hit verification, re-run by the direction as its FIRST action**, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`**, reporting **HITS**
(occurrences, via `git grep -o | wc -l`) and **FILES** separately, and covering
**every token in the range rather than sampled endpoints** (shapes 1 and 2's
fixes): at the dispatch's `HEAD` (`53bc9740`) `OBAR`/`obar` and all of
`(OC-58)`–`(OC-65)` / `O53`–`O60` were **0/0**. Re-run at `HEAD` after the
deviation and after two siblings' round-state commits: `obar` **0/0**;
`(OC-58)`–`(OC-65)` and `O53`–`O60` **0/0**; **`(OC-56)`/`(OC-57)`/`O52`
3 hits / 1 file**, all three inside this file's own OWALL block — two the tail
**declaration**, one OWALL's own 0-hit **record** — hence declarations, not
consumptions, under the `(GR-145)`/`(BE-149)`/`(BE-150)` precedent; and **`OBAR`
5 hits / 3 files**, every one the coordinator's own in-flight round-state
notice in `Pencil-fanout.md`, `Pencil-labels.md` and `Phase39.md`. **Reservation
clean.**

**Code and basename**: `OBAR` names the direction's own object — the **bar**
along the meet line, the `O` from §(K-out)'s tag. The (L6) landing-time
bare-token check: every mint is `OC-`-prefixed inside the reservation, and the
draft introduces **no** bare `(X<digit>)` token of its own. The bare tokens it
*cites* — `(T1)`, `(T3)`, `(C6)`, `(M1)`, `(D3)`, `(R3)`, `(σ2)`, `(σ5)`,
`(σ7)`, `(Λ0d)` — are all grandfathered and all written L3-qualified at first
use (`§(K-pitch) (T1)`, `§(K-slide-comb) (C6)`, `§(K-Δ) (M1)`, `§(K-dom) (D3)`,
`§(K-σ) (σ7)`). **No new section name and no new tag were minted.**

## Reservation — BARCH (arc ordinal 77, 2026-09-03, a CONCURRENT ROUND OF FOUR)

**Scope: §(K-bare-ext), which BARCH *extends* — no new section.** The direction
is the ninth strategy pass's **rank 2**, *does any `p_x`-free-subspace method
survive at side-degree `≥ 2`, and is the 12-block residue reachable without
(PENCIL-SATURATES-CHART) at all?*. Its three siblings (GLEAF §(K-grid), OBAR
§(K-out), DSAT §(K-dom)) own disjoint sections and disjoint tags, so the
reservation protects against the corpus and against them.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BARCH** | §(K-bare-ext) — **extends**, no new section | **(BE-149)–(BE-156)**, of which **(BE-149)–(BE-155)** consumed | **BE148–BE155**, of which **BE148–BE154** consumed | `w4/barch.py` (five modes) |

**It opens at exactly the tail BSCOND declared** (*"The next tail is (BE-149) /
Step BE148"*), and **not** at (BE-150). **One label and one step are RETURNED
UNUSED**: **(BE-156)** and ***Step BE155***, reserved against an eight-label
section that came in at seven, and **available**. **The next tail is (BE-156) /
*Step BE155***, 0-hit verified at this landing, so a successor opens there and
**not** at (BE-157).

**0-hit verification, re-run by the direction as its FIRST action**, across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`**, reporting **HITS**
(matching lines) and **FILES** separately: `BARCH`/`barch` **0/0**; `BE149`,
`BE150`–`BE155`, `(BE-151)`–`(BE-156)` all **0/0**; `(BE-150)` **1 hit / 1
file**, the BSCOND tail clause immediately above — a **declaration, not a
consumed label**; and `(BE-149)`/`BE148` **6 hits / 3 files**, all six being
this reservation's *own* declaration across `Pencil-fanout.md`,
`Pencil-informal.md` and this file. Reservation clean.

### CLAUSE (L7), minted here: check EVERY token in a reserved range, not sampled endpoints

**The coordinator's prep reported `(BE-149)` and `BE148` as 0/0; the direction
measured 6 hits in 3 files.** The prep's *conclusion* held — every hit is a
declaration — but its *method* did not: it verified `(BE-150)`, `(BE-156)`,
`BE149` and `BE155`, i.e. the range's **interior and closing** tokens, and
**never `(BE-149)` or `BE148`, the range's actual OPENING tokens** — which are
precisely the tokens the *previous* landing had to write down in order to hand
the tail over. So the sampled-endpoint method is **systematically blind at the
one end where a hit is guaranteed**.

> **(L7).** A reservation check enumerates **every** token in the reserved
> range — both label forms (`(BE-n)` and the bare `BE-n`) and every raw step
> token — and reports **HITS and FILES separately**. Sampling endpoints is not
> a check; sampling the *closing* endpoints is the worst case, because the
> opening ones are the ones a predecessor's tail-declaration names.
>
> *(Numbered (L7): `(L5)` and `(L6)` are both taken. This draft first minted it
> as `L5` and the registry's own index caught the collision at landing — clause
> (L1) firing on the file that states it. `(L7)` is **not** globally 0-hit —
> `notes/Phase22i.md` uses `L0`–`L10` for its **Layers** and carries two `(L7)`
> hits — but neither are `(L1)` or `(L6)`, which hit the same file the same way.
> That is a pre-existing cross-file homonym in a **closed** phase's note, in a
> different namespace, and it is the `BE-`-is-not-globally-0-hit case this file
> already adjudicated: the `L` clause numbers are this registry's own tag, and
> a citation crossing into Phase-22i qualifies itself under clause (L2).)*

**This is the SECOND coordinator reservation defect in two rounds, and they are
DIFFERENT shapes — recorded separately rather than merged**, because a merged
lesson would lose the one that is actually mechanical:

1. **2026-09-03, `53bc9740` — a METRIC conflation.** The check counted *files*
   and reported them as *hits*. The verdict was right, the cause was wrong. Fix:
   name the metric.
2. **2026-09-03, this landing — a COVERAGE gap.** The check named its metric
   correctly and *did not check the range's opening tokens at all*. Fix: L5,
   enumerate the range.

A check can satisfy (1) and still fail (2), which is what happened here — so
the two are independent clauses, not two readings of one lesson.

### A SIXTH SHAPE, found 2026-09-08 (direction BFOUR) — a token minted INSIDE the reservation, which a RANGE check structurally cannot see

**This one is the coordinator's, not the direction's, and it is a different
shape from all five below.** Every recorded defect so far is about the reserved
**range** — its metric (1), its coverage (2), its family (3). BARCH's `(E4)` was
never in a range: it was minted *inside* a clean, correctly-enumerated
reservation as a **sub-clause name**, and a range check — however exhaustive
over `(BE-149)`–`(BE-156)` and `BE148`–`BE155` — **cannot** see it, because it
is not one of those tokens. That is precisely the gap **(L6)** exists to close,
and (L6) either was not run at BARCH's landing or was run without leaving the
draft. **Fix: (L6)'s grep runs over the whole repository and a `*.lean`
doc-comment hit counts** — the clause text is sharpened in place above, with
the measured `(E4)` case and the coordinator's settled *no-rename*
disposition. **Recorded separately rather than merged with (2)** for the same
reason (1) and (2) are separate: a check built to enumerate a range perfectly
still misses this, so it is an independent clause.

## Coordinator reservation defects — FIVE instances in ONE round (2026-09-03)

Recorded together because they arrived in one four-direction round, all in the
**coordinator's** pre-dispatch checks, and because each would pass a check built to
catch the previous one. The conclusions survived all three; the *procedure* is what
failed.

1. **Metric conflation** (BSCOND; corrected `53bc9740`). `git grep -c` piped to
   `wc -l` counts **files containing a match**, reported as **hits**. Fix: `git grep -o`
   piped to `wc -l` counts hits, and a reservation **says which metric it reports**.
2. **Coverage gap** (BARCH; corrected at its landing, `d1efc63d`). The check sampled the
   range's interior and closing tokens — `(BE-150)`, `(BE-156)`, `BE149`, `BE155` — and
   never `(BE-149)`/`BE148`, its **opening** tokens, which carry 6 hits in 3 files (all
   declarations). Fix: **check every token in a reserved range, not sampled endpoints.**
   Note this check *satisfied* shape 1 and still failed.
3. **Wrong FAMILY** (DSAT, this round — the worst of the three, because it makes the
   0-hit result meaningless rather than merely imprecise). The reservation offered
   `(D8)`–`(D14)` for §(K-dom), derived from a max-integer scan of `\(D(\d+)\)`. But
   **§(K-dom)'s label family is `(DM-N)`** — clause (L1)'s own worked example in this
   file says a new §(K-dom) claim becomes **`(DM-5)`, not `(D5)`** — so the reserved
   tokens were 0-hit for the entirely uninteresting reason that they were never the
   family. DSAT **deviated correctly**, minting `(DM-5)`–`(DM-11)` against the spec and
   citing (L1); the reserved **step** names `D8`–`D14` were kept, with `D8` itself
   adjudicated as taken-but-unrelated (4 hits / 2 files, `notes/Phase23-design.md`'s
   Phase-23f *Layer* steps) under the same precedent as `(L1)`/`(L6)`/`(L7)`.
   **Fix, and it subsumes the other two: derive the family from THIS FILE's stated
   convention for the owning section, never from a regex scan of integers — then check
   every token, reporting hits and files separately.** A max-integer scan cannot tell a
   label family from a coincidence of shape.

**The standing lesson for the dispatch side:** a direction that finds its reservation
contradicted by this file should **follow this file and say so in its return**, as DSAT
did. The registry outranks a coordinator's spec on label naming.

4. **Off-by-one against a DECLARED TAIL** (GLEAF). The reservation offered
   `(GR-146)`–`(GR-153)` / `G166`–`G173`. But GGLOB's landing **declares the tail
   verbatim in two places** — *"the tail declared for the next reservation is (GR-145) /
   Step G165"* — so the correct opening was **(GR-145)**, and the spec skipped it because a
   max-integer scan saw `(GR-145)` present and read it as **consumed** when it was the
   **declaration**. GLEAF **deviated DOWN correctly**, using `(GR-145)`–`(GR-152)` /
   *Steps G165–G172*, returning `(GR-153)`/*Step G173* unused. It also found
   **`(GR-150)` is not 0-hit**: 1 hit in `notes/gapmap.py:216`, a **docstring example** in
   the boundary-matching helper — a live label form inside a tool's docstring, **re-worded
   to the unmintable `(GR-15<digit>)` by the coordinator in advance of the landing**
   (`a5d8101c`), so the range landed clean; the narrow rule it leaves is that a tool-file
   example naming an **unminted** label becomes a false hit the moment a direction mints it.

5. **Off-by-TWO against a declared tail** (OBAR) — **the increment OBAR flagged rather
   than took, applied here by the coordinator.** Detail is in OBAR's own reservation block
   above and is **not duplicated**: the spec offered `(OC-58)`–`(OC-65)` / `O53`–`O60`
   while this file declares §(K-out)'s tail verbatim at OWALL's landing as **`(OC-56)+ /
   Step O52+`**, so the spec skipped two labels and a step that **no direction in the round
   was holding**. OBAR opened at the declared tail and recorded it.

**WHAT THE FIFTH INSTANCE ADDS, and it is why the count matters more than the taxonomy.**
Shapes 4 and 5 are the *same* error — a scan seeing a declared tail *present* and reading
it as *consumed* — committed **twice in one round, in two different sections**, and fixed
both times by a **dispatched direction deviating DOWN to the declared tail** (GLEAF by one,
OBAR by two). Two independent directions applying the same correction to the same
coordinator is the signature of a **systematic** procedure failure, not five incidents; the
taxonomy above is therefore a diagnosis of one habit, not a checklist of five.

**THE ROOT CAUSE, and it unifies all five.** Every one of these came from **deriving a
reservation by scanning the corpus** instead of **reading the tail this registry
declares**. Shape 1 mis-metered a scan, shape 2 under-covered a scan, shape 3 scanned the
wrong family, and shape 4 misread a scan's maximum as consumed rather than declared. The
registry states the next tail explicitly at nearly every landing, precisely so that no
reservation has to be computed. **So: READ THE DECLARED TAIL for the owning section and
open there. Use a scan only to CONFIRM it, checking every token in the range and naming
the metric — never to DERIVE it.** Concretely, the coordinator's pre-dispatch step is a
**grep of this file, not of the corpus**:

```
grep -n "tail declared for the next reservation\|the live tail is therefore" \
     notes/Pencil-labels.md | tail -20
```

which lists every section's declared tail in landing order. Both of shapes 4 and 5 would
have been caught by that one command. A scan cannot distinguish a family from a coincidence
of shape, nor a declaration from a consumption; the declaration can.

## Reserved namespace — direction BINSERT (2026-09-08, **CONSUMED: all eight labels; one STEP returned**)

**Reserved and consumed on 2026-09-08 for the single direction BINSERT**
(ordinal 82; `notes/Pencil-fanout.md` §"BINSERT") — the ninth strategy pass's
**rank 4**: *does option B for `hbareSplit`, the insertion calculus, still have
an endpoint at all?* One of a **concurrent round of three**; the two siblings
(BFOUR, BSERIES) both **extend §(K-bare-ext)** and held
**(BE-156)–(BE-163)** / *Steps BE155–BE162* and **(BE-164)–(BE-171)** /
*Steps BE163–BE170* respectively, so this direction was fenced out of that
family's tail and every check below is against `HEAD` (`RESEARCH-ARC.md` §2's
first concurrency hazard; the tree carried both siblings' untracked drivers
throughout).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BINSERT** | **§(K-ins) — a NEW section** | **(INS-1)–(INS-8)**, all eight consumed | **INS1–INS8**, of which **INS1–INS7** consumed | `w4/binsert.py` (three modes) |

**A NEW SECTION rather than §(K-bare-ext)'s tail — a coordinator call at the
landing, recorded here because it is a deliberate departure from this file's
own convention and not an oversight.** The convention (*Reserved namespaces*)
is that a direction which **extends** a live section reserves the unclaimed
tail of that section's family, and only a direction opening genuinely new
territory takes a new section — and every one of BINSERT's findings extends
**§(K-bare-ext)**, so the convention's preferred home was `(BE-172)`+ /
***Steps BE171*+** — *corrected 2026-09-08 at the BSERIES landing: this block
first read "Steps BE163+", and `BE163` is the **first step of BSERIES's own
reservation**, not a free tail, so a reader following the pointer would have
opened on top of a live range. The label half was right; the step half was one
block low.* The direction reported the tension rather than resolving it;
the coordinator's decision was **keep `§(K-ins)` / `INS-`**, on two grounds:
the pass's object is option B's *route*, which carries its own kill condition
and its own surviving endpoint (hence its own gap-map row, on the
`§(K-res)/(RS-5)` precedent), and the `(BE-)` tail was fenced by two live
siblings.

**One STEP is RETURNED UNUSED: *Step INS8*.** All eight labels are consumed,
but (INS-8) — the *no genericity to supply* claim — is stated **inside
*Step INS5***, beside the panel-collapse measurement it depends on, rather
than being given a step of its own. Labels and steps are separately reserved
objects under clause (L2), so the two counts need not match. **The next tail
is (INS-9) / *Step INS8*.**

**(L3) scope declaration, and it is a coordinator call rather than a registry
deviation.** §(K-ins) is a *new* section, so **every** `(BE-n)`, `(GR-n)`,
`(OC-n)`, `(RS-n)` and `(E4)` citation inside it is cross-section, and (L3)
asks for the owner on each. The section qualifies the load-bearing ones in
place and otherwise carries an explicit scoping paragraph of its own —
unqualified `(BE-n)`/`(E4)` mean §(K-bare-ext), `(GR-n)` §(K-grid), `(OC-n)`
§(K-out), `(RS-n)` §(K-res), `(L n)` this file's minting rule. That is how
§(K-bare-ext) itself reads its own `BE-` citations; the direction flagged the
departure from (L3)'s literal prescription and the coordinator accepted the
declared scope.

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): every token in the range, enumerated rather than sampled, **hits and
files reported separately**), across `*.md`, `*.tex`, `*.lean`, `*.py`,
`*.m2` **at `HEAD`** by `git grep -I -c -F`: `K-ins`, `(INS-1)`–`(INS-8)`,
the bare forms `INS-1`–`INS-8`, the raw step tokens `INS1`–`INS8`, `BINSERT`
and `binsert` — **27 tokens, every one 0 hits / 0 files**, reproducing the
coordinator's own prep enumeration exactly. This is the **first reservation
in the phase with no hit anywhere in the range**, the opening tokens
included: there was no predecessor tail declaration to collide with, because
the section is new.

`BINSERT` was checked for the substring hazard (L5) and is clean, and `INS-`
is multi-letter and topic-tagged per that clause — it names the **object**
(the insertion calculus), not a method or a verdict.

**(L6) landing-time bare-token grep, run on the returned draft and again on
the landed section.** The only bare `(X<digit>)` tokens present are `(E4)`
and `(L1)`/`(L2)`/`(L4)`/`(L5)`/`(L7)` — **all pre-existing tokens the
section cites, none minted here**; every mint is the topic-tagged
`(INS-n)`. `(BE-171)`, `(BE-172)` and `(BE-179)` appear in this block and in
the section's registry discussion **only** as references to the siblings'
reserved ranges and to the rejected renumbering option — they are **not**
mints.

## Reserved namespace — direction BSERIES (2026-09-08, **CONSUMED: all eight labels and all eight steps; NOTHING returned**)

**Reserved and consumed on 2026-09-08 for the single direction BSERIES**
(ordinal 83; `notes/Pencil-fanout.md` §"BSERIES") — block 10's **entry 2**:
*can the (BE-46)/(BE-52) per-shape witnesses behind the sharpened-at-one-end
route be retired class-level by running BWIN's machine at ONE peel?* One of a
**concurrent round of three**; the siblings are BFOUR (same section, the tail
immediately below this reservation) and BINSERT (§(K-ins), landed above).

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSERIES** | §(K-bare-ext) — **extends**, no new section | **(BE-164)–(BE-171)**, all eight consumed | **BE163–BE170**, all eight consumed | `w4/bseries.py` (eight modes) |

**It opens one block above the tail BARCH declared** (*"The next tail is
(BE-156) / Step BE155"*), **by coordinator allocation**, because the sibling
BFOUR holds the eight tokens from that tail. The registry does **not** conflict
with that allocation: BINSERT's block, landed the same day, records it
verbatim — *"the two siblings (BFOUR, BSERIES) both extend §(K-bare-ext) and
held (BE-156)–(BE-163) / Steps BE155–BE162 and (BE-164)–(BE-171) / Steps
BE163–BE170 respectively"*. **The next tail is (BE-172) / *Step BE171***.

**0-hit verification, re-run by the direction as its FIRST action and then AGAIN
after `HEAD` MOVED MID-RUN** (clause (L7): every token in the range enumerated
rather than sampled, **HITS and FILES reported separately**), across `*.md`,
`*.tex`, `*.lean`, `*.py`, `*.m2` **at `HEAD`** by `git grep -I -c -F`:

- **at `e63245c7` (dispatch time): all 26 tokens 0 hits / 0 files** —
  `(BE-164)`–`(BE-171)`, the bare forms `BE-164`–`BE-171`, the raw step tokens
  `BE163`–`BE170`, and `BSERIES`/`bseries` — reproducing the coordinator's own
  prep enumeration exactly;
- **at `67124a9c` (after the coordinator landed BINSERT mid-run):**
  `(BE-164)` **1/1**, `BE-164` **1/1**, `(BE-171)` **2/1**, `BE-171` **2/1**,
  `BE163` **2/1**, `BE170` **1/1**, `BSERIES` **1/1**, and
  `(BE-165)`–`(BE-170)`, their bare forms, `BE164`–`BE169` and `bseries` all
  **0/0**. **Every hit is in this file alone and every one is BINSERT's own
  declaration of this reservation.**

**Reservation clean and unconsumed** — and the hit pattern is exactly the one
**(L7)** exists to make legible: *a declaration is not a consumption, and it
lands on the range's opening and closing tokens*. This is the clause's first
**live** confirmation on a range it did not itself mint.

**A THIRD READ-SIDE CONCURRENCY HAZARD, recorded here because the (L7) check is
where it bit.** `RESEARCH-ARC.md` §2 lists three hazards for a concurrent
read-only round — diff against `HEAD` not the tree, prefix scratch files, do
not increment a shared counter — and **none of them covers `HEAD` itself
moving**. It moved here: the coordinator lands serially *inside* a live round,
so BINSERT's landing changed `HEAD` while this direction was measuring, which
makes a `HEAD`-anchored figure taken before the landing **also** stale. Every
figure in this landing was re-taken at `67124a9c`, the (L7) enumeration
included. *The §2 edit is the coordinator's at the round close.*

**(L6) landing-time bare-token grep, run on the returned draft and again on the
landed section.** The only bare `(X<digit>)` tokens present are `(b1)`, `(b2)`,
`(b3)`, `(E4)`, `(M1)`, `(M2)`, `(S1)`, `(S2)`, `(P)`, `(R)`, `(Z)`, `(CH-1)`
and `(CH-2)` — **all pre-existing tokens the section cites, none minted here**.
The direction's own new objects are deliberately **unlettered**: `W′`, `t′`,
cases `(a′)`/`(b′)`/`(c′)`, *habitat (I)*/*habitat (II)*, *one-end piece* and
*clean end*. The primed case tags are not label mints and are scoped to
*Steps BE163–BE170*; they were chosen over letters precisely because `(a)`/`(b)`
are already carrying two jobs each in §(K-bare-ext) ((BE-147)'s cases and
half (B)'s item-0 sub-items).

## Reserved namespace — direction BFOUR (2026-09-08, **CONSUMED: seven labels and seven steps; one of each RETURNED**)

**Reserved 2026-09-08 for the single direction BFOUR** (arc ordinal 81, run
concurrently with BSERIES and BINSERT; `notes/Pencil-fanout.md` §"BFOUR") —
**(BE-154)(iv): does a peel exist with `c_i(Π_x) = 2` and `e₁ + e₂ ≤ 3`, i.e.
is §(K-bare-ext) (E4) false?** It extends **§(K-bare-ext)** and opens **no** new
section, so the reservation is the unclaimed tail of that section's own `(BE-n)`
family and the owning section stays authoritative.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BFOUR** | §(K-bare-ext) — **extends**, no new section | **(BE-156)–(BE-163)**, of which **(BE-156)–(BE-162)** consumed | **BE155–BE162**, of which **BE155–BE161** consumed | `w4/bfour.py` (seven modes) |

**It opens at exactly the tail BARCH declared** (*"The next tail is (BE-156) /
Step BE155"*), and **not** at (BE-157). **One label and one step are RETURNED
UNUSED: (BE-163) and *Step BE162***, reserved against an eight-label section
that came in at seven, and **available**. Its step range therefore sits
*numerically below* the BSERIES continuation that landed one commit earlier:
`notes/Pencil-informal.md` is ordered by **landing**, not by step index, and
this block records that so a successor does not read it as a numbering error.

**THE LIVE TAIL IS (BE-172) / *Step BE171*** — BSERIES's declaration, unchanged
by this landing, since BSERIES holds `(BE-164)`–`(BE-171)` / *Steps
BE163–BE170* and returned nothing. **Two strays are available inside the
consumed region and a successor may take either**: **(BE-163)** and
***Step BE162*** (this direction's) alongside ***Step INS8*** (BINSERT's).

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`** by
`git grep -o -F` for hits and `git grep -l -F` for files:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files |
|---|---|---|
| `BE-156` | **6 / 1** | **6 / 1** |
| `BE-157` | **1 / 1** | **1 / 1** |
| `BE-158`–`BE-163` | 0 / 0 | 0 / 0 |

with the raw step tokens `BE155` at **6 / 1** and `BE156`–`BE162` at **0 / 0**,
and `bfour` **0 / 0**. All eight non-zero label/step hits are in **this file
alone**, inside BARCH's own reservation block, and every one is a
**declaration, not a consumption** — `(BE-156)`/`BE155` in its tail hand-over
and `(BE-157)` in its *"and not at (BE-157)"* clause. That is exactly (L7)'s
predicted **guaranteed hit at a range's opening tokens**, and the enumeration
reproduced the coordinator's prep token-for-token. **Reservation clean.**

**AND THE DIRECTION CODE ITSELF IS NOT 0-HIT — a NINTH declaration, caught by
re-measuring rather than by assuming.** `BFOUR` is **6 hits / 3 files** at
`HEAD`: `notes/Pencil-labels.md` ×4, `notes/Pencil-informal.md` ×1,
`notes/Pencil-fanout.md` ×1 — **all six written by the two siblings that landed
first in this same round** (BSERIES and BINSERT naming BFOUR as the direction
holding the `(BE-156)` tail), so every one is a **declaration, not a
consumption**, and the code was 0-hit when the round was reserved. **Recorded
because the first draft of this block asserted `BFOUR` 0 / 0 without measuring
it**, which is the (L7) failure mode one level up: the clause says enumerate
the *label* range, and a **serial** landing order means the *code* acquires
sibling references between reservation and landing. **Read as a clause:** a
landing-time (L5)/(L7) check re-measures the **direction code** too, and
expects hits equal to the number of siblings that landed before it.

**ONE LABEL MINTED OUTSIDE THE RANGE, deliberately and under (L1):
`(BE-E4′)`** — the repaired clause, (E4) restricted to `δ₁, δ₂ ≥ 1`
((BE-162)(i)). It was verified **0 hits / 0 files** at `HEAD` in both forms
(`(BE-E4′)`, `BE-E4′`), it is `BE-`-prefixed because clause (L1)'s remedy for a
`(X<digit>)`-shaped token is the owning section's tag, and the prime follows
the existing `(GR-4′)` / `(Λ0f′)` convention. **It is named this way precisely
so the `(E)` family stops growing bare tokens** — see the collision-table row
for `(E1)`–`(E5)` and the disposition note under clause (L6), both added at
this landing.

**(L6) landing-time bare-token grep, RUN over the whole repository** (the
sharpening this landing added to that clause). The direction minted **no** bare
`(X<digit>)` token of its own. The bare tokens the section *cites* — `(E4)`,
`(S1)`, `(S2)`, `(P)`/`(Z)`/`(R)`, `(b1)`/`(b2)`/`(b3)`, `(α)`/`(β)`, `(∗)`,
`(T1)`, `(F13)`, `(M1)`, `(E1)`/`(E2)`/`(E3)` in the E-rider — are all
pre-existing, and every load-bearing one is written **(L3)-qualified** at first
use (`§(K-bare-ext) (E4)` throughout). `BFOUR` was checked for the (L5)
substring hazard and is clean; `bfour` is likewise 0-hit as a raw substring.

## Reserved namespace — direction BSTEER (2026-09-08, **CONSUMED: seven labels and seven steps; one of each RETURNED**)

**Reserved 2026-09-08 for the single direction BSTEER** (arc ordinal 84, the
first dispatch of the arc with nothing else in flight since ordinal 75;
`notes/Pencil-fanout.md` §"BSTEER") — **(BE-162)(iii): at `δ₂ = 1`, can side
2's single screw line be steered inside `Π_x` while side 1 stays bad?**, the
task BFOUR's own hand-off named. It extends **§(K-bare-ext)** and opens **no**
new section, so the reservation is the unclaimed tail of that section's `(BE-n)`
family and the owning section stays authoritative.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BSTEER** | §(K-bare-ext) — **extends**, no new section | **(BE-172)–(BE-179)**, of which **(BE-172)–(BE-178)** consumed | **BE171–BE178**, of which **BE171–BE177** consumed | `w4/bsteer.py` (seven modes) |

**It opens at exactly the tail BFOUR and BSERIES both declared** (*"The next
tail is (BE-172) / Step BE171"*), and **not** at (BE-173). **One label and one
step are RETURNED UNUSED: (BE-179) and *Step BE178***, and **the two earlier
strays stay available and unused**: **(BE-163)** and ***Step BE162*** (BFOUR's)
alongside ***Step INS8*** (BINSERT's). **THE LIVE TAIL IS (BE-180) /
*Step BE179***, 0-hit verified at this landing. *(**CONSUMED 2026-09-08 by
direction BGPROP**, whose block is at the end of this file and declares the
next tail — this line is history, not a live reservation.)*

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`**, `git grep -o`
for hits and `git grep -l` for files:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files | step `BEn` hits / files |
|---|---|---|---|
| `BE-172` / `BE171` | **7 / 3** | **7 / 3** | **6 / 3** |
| `BE-173`–`BE-178` | 0 / 0 | 0 / 0 | 0 / 0 (`BE172`–`BE178`) |
| `BE-179` | **1 / 1** | **1 / 1** | — |

`BSTEER` and `bsteer` both **0 / 0** as raw substrings, (L5)'s check included.
Every non-zero hit is a **declaration, not a consumption**: `(BE-172)`/`BE171`
are the tail hand-over written *twice* — by BFOUR and by BSERIES, in
`Pencil-fanout.md`, `Pencil-informal.md` and this file — and the single
`(BE-179)` hit is BINSERT's own block noting that it names the token without
minting it. The enumeration **reproduced the coordinator's prep
token-for-token**, and this is the first reservation in the phase whose opening
tokens were declared by **two** predecessors rather than one, which is (L7)'s
own prediction with the multiplicity raised.

**ONE LABEL CONSUMED FROM OUTSIDE THE `(BE-n)` FAMILY, and it is BFOUR's, not a
mint: `(BE-E4′)`.** This direction *decides a question about* that clause and
cites it throughout; it mints nothing new. The `(E4)` collision recorded under
clause (L6) is therefore **unchanged in scope** by this landing, and every
citation of the bare `(E4)` here is **(L3)-qualified** as
`§(K-bare-ext) (E4)`.

**(L6) landing-time bare-token grep, RUN over the whole repository** — the
sharpening BFOUR added to that clause, now applied by the direction that added
it. **No bare `(X<digit>)` token is minted here.** The bare tokens the section
cites — `(E4)`, `(P)`/`(Z)`/`(R)`, `(M1)`, `(b1)`/`(b2)`/`(b3)`, `(α)`/`(β)`,
`(∗)`, `(S1)`/`(S2)`, and `(E1)`/`(E2)`/`(E3)` in the E-rider — are all
pre-existing, all in the collision table where they belong, and all qualified at
first use. **The one new symbol introduced, `Q`, is deliberately not a label**:
it is the Klein form, written as code (`pitch.Q`) and defined in the section's
*Standing notation*, so it cannot be read as a claim token.

## Reserved namespace — direction BGPROP (2026-09-08, **CONSUMED: eight labels and eight steps, none returned**)

**Reserved 2026-09-08 for the single direction BGPROP** (arc ordinal 85, the
second consecutive dispatch with nothing else in flight;
`notes/Pencil-fanout.md` §"BGPROP") — **the tenth strategy pass's rank 1,
`Γ`-properness**: does (BE-122)/(BE-123)'s proper → generic bridge TRANSPORT to
the `Γ`-locus, and can the incidence lemma (BE-149)(v) names as *what is
genuinely missing* be proved? It extends **§(K-bare-ext)** and opens **no** new
section, so the reservation is the unclaimed tail of that section's `(BE-n)`
family and the owning section stays authoritative.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BGPROP** | §(K-bare-ext) — **extends**, no new section | **(BE-180)–(BE-187)**, **all eight consumed** | **BE179–BE186**, **all eight consumed** | `w4/bgprop.py` (three modes + `validate`) |

**It opens at exactly the tail BSTEER declared** (*"THE LIVE TAIL IS (BE-180) /
Step BE179"*). **Nothing is returned**, and **the three earlier strays stay
available and unused**: **(BE-163)** / ***Step BE162*** (BFOUR's), **(BE-179)**
/ ***Step BE178*** (BSTEER's) and ***Step INS8*** (BINSERT's). **THE LIVE TAIL
IS NOW (BE-188) / *Step BE187***, 0-hit verified at this landing.
*(**CONSUMED 2026-09-08 by direction BRANKV**, whose block follows and
declares the next tail — this line is history, not a live reservation.)*

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`**:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files | step `BEn` hits / files |
|---|---|---|---|
| `BE-180` / `BE179` | **1 / 1** | **1 / 1** | **1 / 1** |
| `BE-181`–`BE-187` | 0 / 0 | 0 / 0 | 0 / 0 (`BE180`–`BE186`) |
| `BE-188` (the new tail) | 0 / 0 | — | — |

`BGPROP` and `bgprop` both **0 / 0** as raw substrings, (L5)'s check included.
The three non-zero cells are **one declaration, not a consumption**: all of
`(BE-180)`, `BE-180` and `BE179` resolve to the *same two lines* of BSTEER's
reservation block above, which hand the tail over. The enumeration
**reproduced the coordinator's prep token-for-token**, in both metrics — the
second consecutive reservation to do so, which is (L7) working as written.

**NO LABEL IS MINTED OUTSIDE THE RANGE.** Five symbols are introduced in the
section's *Standing notation* and **none of them is a label**: `Ω`, `Ω^⊥`,
`Γ_Ω`, `g_Ω`, `f`, `T`, `X_1` and `Δ_Ω` are all **objects**, written as
mathematics and defined in that block, so none can be read as a claim token.
`X_1` is the one worth naming explicitly: it is a *subscripted variable*, not
an `(X<digit>)`-shaped parenthesized token, and it never appears in
parentheses on its own.

**(L6) landing-time bare-token grep, RUN over the whole repository** — the
sharpening BFOUR added and BSTEER re-applied. **No bare `(X<digit>)` token is
minted here.** The grep over this landing's added prose returns **exactly one**
`(X<digit>)`-shaped token, `(E4)`, and it is a **citation** written
**(L3)-qualified** as `§(K-bare-ext) (E4)` in the E-rider — BFOUR's
grandfathered collision, unchanged in scope by this landing. The driver file's
own `(p1)`/`(p2)`/`(p3)`/`(R0)`/`(U0)`/`(W0)`/`(W12)` matches are **Python
function-call parentheses**, checked line by line, not labels; they are
reported here rather than silently filtered because (L6)'s whole point is that
a grep confined to prose sees neither a `*.lean` doc-comment nor a `*.py` one.

## Reserved namespace — direction BRANKV (2026-09-08, **CONSUMED: eight labels and eight steps, none returned**)

**Reserved 2026-09-08 for the single direction BRANKV** (arc ordinal 86, the
third consecutive dispatch with nothing else in flight;
`notes/Pencil-fanout.md` §"BRANKV") — **BGPROP's own named successor: is the
clause `Π_x ⊆ ρ̄_i ⟹ ρ_i = 6` true POINTWISE at `k = 2`?** It extends
**§(K-bare-ext)** and opens **no** new section.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BRANKV** | §(K-bare-ext) — **extends**, no new section | **(BE-188)–(BE-195)**, **all eight consumed** | **BE187–BE194**, **all eight consumed** | `w4/brankv.py` (three modes + `validate`) |

**It opens at exactly the tail BGPROP declared** (*"THE LIVE TAIL IS NOW
(BE-188) / Step BE187"*). **Nothing is returned**, and **the three earlier
strays stay available and unused**: **(BE-163)** / ***Step BE162*** (BFOUR's),
**(BE-179)** / ***Step BE178*** (BSTEER's) and ***Step INS8*** (BINSERT's).
**THE LIVE TAIL IS NOW (BE-196) / *Step BE195***, 0-hit verified at this
landing.
*(**CONSUMED 2026-09-08 by direction BLONGARC**, whose block follows and
declares the next tail — this line is history, not a live reservation.)*

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`**:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files | step `BEn` hits / files |
|---|---|---|---|
| `BE-188` / `BE187` | **1 / 1** | **2 / 1** | **1 / 1** |
| `BE-189`–`BE-195` | 0 / 0 | 0 / 0 | 0 / 0 (`BE188`–`BE194`) |
| `BE-196` (the new tail) | 0 / 0 | — | — |

`BRANKV` and `brankv` both **0 / 0** as raw substrings, (L5)'s check included.
Every non-zero cell is BGPROP's own tail declaration, **not a consumption**;
the bare `BE-188` reads **2 hits in 1 file** because that block names the token
twice (once in the tail sentence, once in its 0-hit table). The enumeration
**reproduced the coordinator's prep token-for-token in both metrics** — the
**third consecutive** reservation to do so.

**NO LABEL IS MINTED OUTSIDE THE RANGE.** Three symbols are introduced in the
section's *Standing notation* and **none is a label**: `arc_j`, `W_j` and
`rad(U)` are objects, written as mathematics and defined in that block.

**(L6) landing-time bare-token grep, RUN over the whole repository.** **No bare
`(X<digit>)` token is minted here.** The grep over this landing's added prose
returns **exactly one** `(X<digit>)`-shaped token, `(E4)`, written
**(L3)-qualified** as `§(K-bare-ext) (E4)` in the E-rider — BFOUR's
grandfathered collision, unchanged in scope.
**AND THE GREP CAUGHT SOMETHING IN THE DRIVER, which is the first time (L6)'s
whole-repository half has actually fired on a non-prose file.** The first draft
of `w4/brankv.py` carried the Python locals `E0`, `E1`, `E2` and `U2`, so
`grep -oE '\([A-Za-z]{1,3}[0-9]+\)'` over the file returned **`(E0)`,
`(E1)`, `(E2)`, `(U2)`** — call-parenthesis strings, not label mints, but
**`(E1)`/`(E2)` are the live §(K-grid) termination-ledger family** whose next
slot BARCH's `(E4)` took, and this file already names that collision three
times. Rather than filter them out as false positives, the locals were
**renamed** (`Eside`, `Es1`, `_Es2`, `Ucop`, `arc1`), after which the grep is
clean of the `(X<digit>)` shape entirely and the driver's figures are
unchanged. **The transferable point:** (L6)'s sharpening says a `*.lean`
doc-comment hit counts; a `*.py` local-variable name in a call is the same
hazard one step further out, and renaming a fresh local costs nothing while
`(E4)`'s ~74 references cost a coordinator round.

## Reserved namespace — direction BLONGARC (2026-09-08, **CONSUMED: eight labels and eight steps, none returned**)

**Reserved 2026-09-08 for the single direction BLONGARC** (arc ordinal 87, the
fourth consecutive dispatch with nothing else in flight;
`notes/Pencil-fanout.md` §"BLONGARC") — **BRANKV's own named successor: at arc
length `≥ 4`, is `rank(B|_U) ≤ 2` forced on the 4-dimensional
`U = ⟨ℓ_j⟩ + W_j` at a legal chart point?** It extends **§(K-bare-ext)** and
opens **no** new section.

| direction | owning § | labels reserved | steps reserved | driver |
|---|---|---|---|---|
| **BLONGARC** | §(K-bare-ext) — **extends**, no new section | **(BE-196)–(BE-203)**, **all eight consumed** | **BE195–BE202**, **all eight consumed** | `w4/blongarc.py` (four modes + `validate`) |

**It opens at exactly the tail BRANKV declared** (*"THE LIVE TAIL IS NOW
(BE-196) / Step BE195"*). **Nothing is returned**, and **the three earlier
strays stay available and unused**: **(BE-163)** / ***Step BE162*** (BFOUR's),
**(BE-179)** / ***Step BE178*** (BSTEER's) and ***Step INS8*** (BINSERT's).
**THE LIVE TAIL IS NOW (BE-204) / *Step BE203***, 0-hit verified at this
landing.

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`**:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files | step `BEn` hits / files |
|---|---|---|---|
| `BE-196` / `BE195` | **1 / 1** | **2 / 1** | **1 / 1** |
| `BE-197`–`BE-203` | 0 / 0 | 0 / 0 | 0 / 0 (`BE196`–`BE202`) |
| `BE-204` (the new tail) | 0 / 0 | — | — |

`BLONGARC` and `blongarc` both **0 / 0** as raw substrings, (L5)'s check
included. Every non-zero cell is BRANKV's own tail declaration, **not a
consumption**; the bare `BE-196` reads **2 hits in 1 file** because that block
names the token twice (once in the tail sentence, once in its 0-hit table).
The enumeration **reproduced the coordinator's prep token-for-token in both
metrics** — the **fourth consecutive** reservation to do so.

**NO LABEL IS MINTED OUTSIDE THE RANGE.** Three symbols are introduced in the
section's *Standing notation* and **none is a label**: `α_x`, `ℓ_{j'}` and `Ū`
are objects, written as mathematics and defined in that block. `α_x` and
`ℓ_{j'}` are *subscripted variables*, not `(X<digit>)`-shaped parenthesized
tokens, and neither ever appears in parentheses on its own.

**(L6) landing-time bare-token grep, RUN over the whole repository — AND IT
FIRED AGAIN, on the driver, for the SECOND consecutive landing.** **No bare
`(X<digit>)` token is minted in the prose.** The grep over this landing's
added prose returns **exactly one** `(X<digit>)`-shaped token, `(E4)`, written
**(L3)-qualified** as `§(K-bare-ext) (E4)` in the E-rider — BFOUR's
grandfathered collision, unchanged in scope. **The driver was the hit.** The
first draft of `w4/blongarc.py` carried the Python locals `P1`, `P2`, `U1` and
`v2`, so `grep -oE '\([A-Za-z][0-9]\)'` over the file returned **`(P1)`,
`(P2)`, `(U1)`, `(v2)`** — call-parenthesis strings, not label mints, but
`(P1)` and `(P2)` have **16** and **13** hits elsewhere in the tree
(`notes/Phase23-cleanup.md`, `notes/Phase28.md`, `notes/model-experiment-archive.md`,
`notes/Pencil-informal.md`, `notes/Pencil-fanout-archive.md`,
`notes/Phase23-design.md` among them), so they collide *in appearance* with
live label families exactly as BRANKV's `(E1)`/`(E2)` did. Following BRANKV's
precedent the locals were **renamed** (`Pca`, `Pcb`, `Uperp`, `vsec`), after
which the grep is clean of the `(X<digit>)` shape entirely and the driver's
figures are unchanged (`validate` re-run, all asserts green).
**AND THE SCOPE OF THE CHECK IS NOW STATED, because this landing had to
decide it.** The `(X<digit>)` shape is what (L6) names; **bare
single-letter** call parentheses — `(P)`, `(U)`, `(L)`, `(G)`, `(W)` — are
*not* in scope and must not be renamed. Two reasons, both measured: labels in
this corpus are always `(LETTER+DIGIT)` or `(TAG-N)`, never a lone letter
except for the grandfathered `(P)`/`(Z)`/`(R)` configurational family; and
`(P)` already appears in **ten or more** landed `w4` drivers (`annih.py`,
`battain.py`, `bearcase.py`, `bearfull.py`, `barch.py`, `bdecor.py`,
`bimage.py`, `bpeel.py`, …) and `(U)` in as many, `brankv.py` included, so
treating them as hits would demand a rename round across the whole harness
for zero collision risk. **The rule, stated once so the next landing does not
re-litigate it: (L6) greps `(X<digit>)`, renames a fresh local that matches,
and leaves single-letter call parentheses alone.**

## Reserved namespace — direction BEFOURP (2026-09-08, **CONSUMED: six labels and six steps, two labels and two steps RETURNED**)

| direction | section | labels | steps | driver |
|---|---|---|---|---|
| **BEFOURP** | §(K-bare-ext) — **extends**, no new section | **(BE-204)–(BE-209)** consumed; **(BE-210)/(BE-211) RETURNED** | **BE203–BE208** consumed; ***Steps BE209*/*BE210*** RETURNED | `w4/befourp.py` (three modes + `validate`) |

**It opens at exactly the tail BLONGARC declared** (*"THE LIVE TAIL IS NOW
(BE-204) / Step BE203"*). **Two labels and two steps are RETURNED** — the
section needed six, and a decomposition recon that pads to its reservation is
writing filler. **THE LIVE TAIL IS NOW (BE-210) / *Step BE209***, 0-hit
verified at this landing. **The four earlier strays stay available and
unused**: **(BE-163)** / ***Step BE162*** (BFOUR's), **(BE-179)** /
***Step BE178*** (BSTEER's), ***Step INS8*** (BINSERT's), and now
**(BE-210)–(BE-211)** / ***Steps BE209–BE210*** (this direction's).

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`**:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files | step `BEn` hits / files |
|---|---|---|---|
| `BE-204` / `BE203` | **1 / 1** | **2 / 1** | **1 / 1** |
| `BE-205`–`BE-211` | 0 / 0 | 0 / 0 | 0 / 0 (`BE204`–`BE210`) |

`BEFOURP` and `befourp` both **0 / 0** as raw substrings, (L5)'s check
included. Every non-zero cell is BLONGARC's own tail declaration, **not a
consumption**; the bare `BE-204` reads **2 hits in 1 file** for the same
reason BLONGARC's `BE-196` did (that block names the token twice). The
enumeration **reproduced the coordinator's prep token-for-token in both
metrics** — the **fifth consecutive** reservation to do so, and the first to
close *under* its range.

**TWO LABELS ARE MINTED OUTSIDE THE `(BE-n)` FAMILY, AND (L1) FIRED ON THE
FIRST DRAFT OF BOTH.** The section's two-piece decomposition needs names for
the pieces, and the first draft used the bare families **`(F_f)`/`(G_g)`** with
members `(F_4)`, `(F_5)`, `(F_6)`, `(G_1)`, `(G_2)`. **The (L1) grep struck
them:** `(G_1)` has **14** hits in **three landed drivers** —
`w4/bearfull.py`, `w4/bearcase.py`, `w4/brule.py`, all writing
`E(G_1)` / `dist_(G_1)` / `dist_{G_1}` for a *graph*, not a label — and
`(F_5)` has **6**. That is (L5)'s substring half firing on a *claim* token
rather than a direction code, and it is exactly the shape that made `PAT`
unusable. Per (L1)'s remedy the pieces are **section-tag prefixed**, matching
`(BE-E4′)`'s own precedent:

| token | owner | what it is | status |
|---|---|---|---|
| **`(BE-F_f)`** | §(K-bare-ext) (BE-205)(iii) | the *floor* piece family, `c_i(Π_x) = 2 ⟹ ρ_i ≥ f` | family; `(BE-F_5)`/`(BE-F_6)` **REFUTED**, `(BE-F_4)` **OPEN** — and **IS the floor `ρ_i ≥ 4`**, `q̂` adding nothing ((BE-212), BGTWOA) |
| **`(BE-G_g)`** | §(K-bare-ext) (BE-205)(iii) | the *other-side* piece family, `c_i(Π_x) = 2 ⟹ e_j ≥ g` | family; `(BE-G_1)` PROVED at `ρ_j = 1` (BSTEER); **`(BE-G_2)` and `(BE-G_2a)` REFUTED in the regime, so every `g ≥ 2` member is DEAD** ((BE-214)/(BE-215), BGTWOA) |

Both were verified **0-hit as raw substrings** (`BE-F_`, `BE-G_`,
`(BE-F_f)`, `(BE-G_g)` and every member token) before the rename landed, and
the sub-members `(BE-G_2a)`/`(BE-G_2b)` likewise. **The underscore is
load-bearing and deliberate**: it keeps the tokens off the `(X<digit>)` shape
(L6) greps, so they are not confusable with the `(E1)`/`(E4)`/`(S1)` families.

**ONE FURTHER LABEL CONSUMED FROM OUTSIDE THE FAMILY, and it is BFOUR's, not
a mint: `(BE-E4′)`.** This direction *decomposes* that clause and cites it
throughout. The `(E4)` collision recorded under clause (L6) is **unchanged in
scope**, and every citation of the bare `(E4)` is **(L3)-qualified** as
`§(K-bare-ext) (E4)` — including the one inside the driver's own
`e4prime` docstring, which is the first time that qualification has been
carried into Python rather than only into prose.

**(L6) landing-time bare-token grep, RUN over the whole repository — and it
did NOT fire this time, because (L1) caught the same tokens one clause
earlier.** `grep -oE '\([A-Z][0-9]\)'` over the added prose **and** over
`w4/befourp.py` returns **exactly one** token in each, `(E4)`, both
(L3)-qualified. The driver's locals were named lowercase from the first draft
(`rho1`, `del2`, `esd1`, `sp1`, `f1`/`f2`/`fh`) specifically to stay off the
shape — BRANKV's `E1`/`E2` and BLONGARC's `P1`/`P2`/`U1` renames applied
**pre-emptively** rather than at the landing grep, which is the first landing
in the phase where that check cost nothing. **BLONGARC's scope statement is
consumed unchanged**: `(X<digit>)` in, bare single-letter call parentheses out.

**NO OTHER SYMBOL IS A LABEL.** The section's *notation* additions — `q̂`
((BE-110)(i)'s projection `ω ↦ ω ∧ p_x`), `Σ_x`, `α_x`, `f` and `g` — are
objects and parameters, written as mathematics; `f` and `g` in particular are
**bare lowercase parameters of the two families**, never parenthesized alone.

## Reserved namespace — direction BGTWOA (2026-09-08, **CONSUMED IN FULL: eight labels and eight steps**)

| direction | section | labels | steps | driver |
|---|---|---|---|---|
| **BGTWOA** | §(K-bare-ext) — **extends**, no new section | **(BE-210)–(BE-217)** consumed | **BE209–BE216** consumed | `w4/bgtwoa.py` (three modes + `validate`) |

**It opens at exactly the tail BEFOURP declared** (*"THE LIVE TAIL IS NOW
(BE-210) / Step BE209"*) — i.e. **at the RETURNED pair**, not past it. That
matters: a scan of the *consumed* range alone would have opened at
`(BE-212)`/*Step BE211* and silently stranded BEFOURP's two returned tokens
forever, which is the off-by-N shape behind two of the five coordinator
reservation defects of the 2026-09-03 round. **The registry's own tail
declaration is what prevents it**, and this is the first landing where the
declaration and the consumed range *disagree* — so it is the first real test
of that sentence. **THE LIVE TAIL IS NOW (BE-218) / *Step BE217***, 0-hit
verified at this landing. **The three earlier strays stay available and
unused**: **(BE-163)** / ***Step BE162*** (BFOUR's), **(BE-179)** /
***Step BE178*** (BSTEER's), and ***Step INS8*** (BINSERT's) — BEFOURP's
returned pair is now **consumed**, so the stray list shortens by one for the
first time in the thread.

**0-hit verification, re-run by the direction as its FIRST action** (clause
(L7): **every** token in the range, enumerated rather than sampled, **hits and
files reported separately**), across the whole tree **at `HEAD`**:

| token | `(BE-n)` hits / files | bare `BE-n` hits / files | step `BEn` hits / files |
|---|---|---|---|
| `BE-210` / `BE209` | **4 / 2** | **4 / 2** | **4 / 2** |
| `BE-211` / `BE210` | **4 / 2** | **5 / 2** | **5 / 2** |
| `BE-212`–`BE-217` | 0 / 0 | 0 / 0 | 0 / 0 (`BE211`–`BE216`) |

`BGTWOA` and `bgtwoa` both **0 / 0** as raw substrings, (L5)'s check
included. **Every non-zero cell was OPENED, not counted**: all of them are
BEFOURP's reservation-and-return record (`notes/Pencil-fanout.md` ×2,
this file ×2) plus the tail declaration above — **no consumption anywhere**.
The enumeration **reproduced the coordinator's prep token-for-token in both
metrics**, the **sixth consecutive** reservation to do so, and the first where
the opening tokens were non-zero *by design* rather than by the predecessor's
tail sentence alone.

**(L6) landing-time bare-token grep, RUN over the whole repository, CLEAN.**
`grep -oE '\([A-Z][0-9]\)'` over the added prose returns **zero** tokens — the
first landing in the thread with a genuinely empty result, because the
direction cites `§(K-bare-ext) (E4)` **only** through its successor
`(BE-E4′)` and never needs the bare form. The driver's locals were named to
stay off the shape from the first draft (`side_near`/`side_far`,
`node_x`/`node_y`, `part_a`/`part_b`, `raw_side`, `inner`/`outer`,
`star_plane`) — BRANKV's `E1`/`E2` and BLONGARC's `P1`/`P2`/`U1` renames
applied **pre-emptively**, the second consecutive landing to pay that cost up
front rather than at the grep. **BEFOURP's/BLONGARC's scope statement is
consumed unchanged**: `(X<digit>)` in, bare single-letter call parentheses out.

**NO NEW LABEL FAMILY IS MINTED.** The direction *refutes* BEFOURP's
`(BE-G_2)`/`(BE-G_2a)` and demotes `(BE-F_4)`, so it consumes those tokens
rather than adding to the family; the two registry rows above them are updated
in place, per (L4) (no rename — the tokens now name **refuted** claims, which
is exactly the disposition `§(K-bare-ext) (E4)` was given). The section's *notation*
additions — `dim(ρ̄_j ∩ Σ_x)` and the profile length — are objects and
parameters, written as mathematics, never parenthesized alone.
