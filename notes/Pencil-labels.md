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

Six clauses. They are cheap; clause 1 is the one that actually prevents the
next collision, and (L6) is the landing-time backstop for the one case L1
structurally cannot see.

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

## Reserved namespace — direction BRNODE (2026-09-01, **IN FLIGHT**)

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
| §(K-Λ) | `Λ` ✓ | (Λ0), (Λ0a)–(Λ0i), (Λ0′), (Λ0f′), (Λ1), (Λ2), (Λ3), **(OUT)**; **driver blocks (M1)–(M4)** (`lambda1.m2`) and **(P1)–(P7)** (`lambda0.m2`); **since 2026-08-19 (direction LTWO)** (Λ4)–(Λ8), Steps Λ8–Λ12 (**`Λ`-prefixed step scheme**, per clause 4 — *Step Λ8* is NOT the existing *Step 8*), driver modes `--witness`/`--floor`/`--census`/`--validate` (`w4/ltwo.py`) | the Λ-compression's quadric; (OUT) = the outer-line criterion, *Step 5a*; (since LTWO) the branch calculus on `G°` alone, the companion-cycle lemma and the size floor realizing item (vii)'s two-hub-interior population at all four patterns | (Λ1) an identity over the function field; (K-Λ) refuted as an independent gap; **(Λ4)–(Λ8) proven-informally** (Steps Λ8–Λ12, direction LTWO) — item (vii) REALIZED at a proven size floor, `(K-wit)` residual recomputed not re-graded, Λ-completeness unchanged |
| §(K-dom) | `DM-` | **(D1)**–(D4); Steps D0–D7 | the dominance spike, differential of `H ↦ V_bc` | (D1)–(D3) proven; C1 refuted as a route |
| §(K-σ) | `σ` ✓ | (σ1)–(σ7); Steps σ0–σ6, σ4b; hunt pools H4/H5 | the polarity as a symmetry of the split; **route σ** | (σ7) proven; route σ a CANDIDATE (its field scope settled by §(K-clos)) |
| §(K-clos) | `AC-` ✓ | (AC-1)–**(AC-9)**; Steps Z0–Z8; driver blocks AC-C0/AC-E/AC-S/AC-U/AC-X/AC-Q/AC-R2/AC-F/AC-2c/AC-P (`closure.py`) | the over-`ℂ̄` question: the polarity's field scope, the σ-fixed grid locus, the `⋆`-eigen decoupling, the route-σ collapse, the char-0 descent | (AC-6) **refuted** as a class statement, open on the tight stratum; the rest proven-informally. **(AC-9)** (minted 2026-08-06, re-baselining slice S2): every σ-fixed body of degree `≥ 3` carries a coincident hinge line — **proven** by pigeonhole against *Step Z3*'s two-ruling-lines cap, measured 0/64 by the composite guard; it **qualifies (AC-3)** without weakening it |
| §(K-ann) | `ANH-` ✓ | (ANH-1)–(ANH-8); the two residual inputs **(ANH-R1)**, **(ANH-R2)**; Steps A1–A9; driver modes `--stress`/`--rate`/`--supp`/`--recipe`/`--census`/`--validate` (`annih.py`); **since 2026-08-06 (direction R)** (ANH-9)–(ANH-12), Steps A10–A13, and driver modes `--census`/`--bad`/`--comb`/`--validate` (`shrink.py`); **since 2026-08-06 (direction Q)** (ANH-13)–(ANH-16), Steps A14–A17, driver modes `--types`/`--reduce`/`--size`/`--frame`/`--witness`/`--validate` (`anhr1.py`) and M2 blocks (ANH-Q0)–(ANH-Q4) (`anhr1.m2`) | the annihilator as a self-stress of the contracted framework `H/P`: the reciprocity identity, the named move, the `k = 4` Tay circuit, the one-bracket recipe. **(ANH-8) is promoted to the *Shared dictionary* as (SD-6)** — that is the only copy | (ANH-1)–(ANH-6), (ANH-8) proven / proven-informally; (ANH-7) true-modulo-named-gap; **(ANH-R1) open** |
| §(K-out) | `OC-` ✓  ; **since 2026-08-19 (direction SIGZ, eighth fan-out)** (OC-35)–(OC-39), Steps O31–O36, driver modes `--reduce`/`--spans`/`--budget`/`--slack`/`--theta`/`--p21`/`--hunt` (`w4/sigz.py`), the Kirchhoff-flow form and the `slack`/`δ`/`ρ` ledger  ; **since 2026-08-19 (direction OSCHU, eighth fan-out)** (OC-29)–(OC-34), Steps O25–O30, driver modes `--restate`/`--gtarget`/`--rekey`/`--census1`/`--census2` (`w4/oschu.py`), pools POOL-OS / POOL-OQ / POOL-OG / POOL-OR / POOL-OC2  ; **since 2026-08-25 (direction OQRANK, single dispatch)** (OC-40)–(OC-44), Steps O37–O41, driver modes `--controls`/`--range A B`/`--census1`/`--census2`/`--validate` (`w4/oqrank.py`), pool POOL-OQ2 — the ⋆-eigen split with forced (1,2) profile, the per-block criterion and Veronese dictionary, the (OC-42) WALL, the 174/174 hunted census, and the openness theorem (OC-44); the SIGZ-returned (OC-40) re-claimed here | (OC-1)–**(OC-16)**; Steps O1–O12; the **pools** POOL-C / POOL-G / POOL-S / POOL-B and (since direction O, 2026-08-06) POOL-CW / POOL-A / POOL-W / POOL-SL; driver modes `--comb`/`--pool`/`--shapes`/`--build` (`outerline.py`) and `--wide`/`--adv`/`--wrench`/`--slide` (`outerwide.py`) + `outerwide.m2`; **since 2026-08-19 (direction OCON)** (OC-17)–(OC-22), Steps O13–O18, driver modes `--validate`/`--check`/`--control` (`w4/ocon.py`), pools POOL-OV / POOL-OC / POOL-OZ; **since 2026-08-19 (direction ZNEQ, seventh fan-out)** (OC-23)–(OC-28), Steps O19–O24, driver modes `--factor`/`--sweep`/`--reject`/`--transfer` (`w4/zneq.py`), pools POOL-ZF / POOL-ZQ / POOL-ZN / POOL-ZT / POOL-ZR | (OUT)'s hypothesis measured: the exact hinge-rate reading, the ambient-generic map, the never-automatic negative, the constructed silent point, the two pool distributions, the sampler defect, and the residual; (since OCON) the hard-stratum target-rank qualifier is free, and the (OC-8) residue reduces to a `Z ≠ ∅` + chart-irreducibility + one-chart-point reduction; (since ZNEQ) input (a) `Z ≠ ∅` itself factors into a necessary-for-`hK` half dominated by §(K-grid) (GR-10) and a target-rank half whose failure is a codimension-2 Schubert jump, with a self-refuted-and-corrected closed form and a 138/138 witness census | **(OC-3)** proven-informally and load-bearing; (OC-1) proven-informally; (OC-2)/(OC-5)/(OC-6)/(OC-7) measured; (OC-4) exhibited; **(OC-8) open**. **(OC-7) is a harness item**, `notes/scripts/README.md` *Harness debt* 4 — **CLEARED 2026-08-06** by the re-baselining round, whose slice S2 also minted **(OC-9)** here (the FIELD half of the coincident-hinge guard's adversarial test: the guard rejects 58/357 and its rejection set strictly contains the two-end diagnostic's 39). **(OC-17)–(OC-21) proven-informally** (Steps O13–O16, direction OCON); **(OC-22) an assessment**; **(OC-8) OPEN, reshaped** — the hard-stratum qualifier struck as free, two named inputs (`Z ≠ ∅`, chart irreducibility) added rather than removed. **(OC-23)–(OC-25) proven-informally, (OC-26) proven-informally (its own first closed form refuted by construction and corrected), (OC-27) measured (138/138 witnesses), (OC-28) proven-informally (a conditional domination on the open §(K-grid) gap (GR-10), the boundary exhibited at `P21`)** (Steps O19–O24, direction ZNEQ); **input (a) OPEN as a class-uniform statement, NOT an independent gap; (OC-8) OPEN, unchanged** |
| §(K-ind) | `IN-` | (I0)–(I4); Steps I0–I6 | numerical invariant along the generating moves | refuted as a route; (I3) a positive by-product |
| §(K-Δ) | `DL-` | **(M1)**, **(M2)**, **(M3)**; (N1), (N2) | the Δ-matroid literature hunt: (M1)–(M3) are the **three hypothesis tests**, (N1)/(N2) the two readings bought | NO HIT; discharged |
| §(K-bare-ext) | `BE-` ✓ | **(BE-1)–(BE-9)**, Steps BE1–BE8, driver modes `arith`/`danger`/`optc` (`kbare/breakhunt.py`) *(probe KBARE-FALSIFY, 2026-08-20)*; **since 2026-08-26 (direction BATTAIN)** **(BE-10)–(BE-14)**, Steps BE9–BE13, driver modes `model`/`cone`/`census`/`attain`/`indep`/`hunt`/`decide`/`localcone`/`probe` (`w4/battain.py`); (K-bare-ext) *(named here)* | the bare-half kernel off feasibility: the arbitrary-seed insertion lemma and its refutation; then the motive characterized off the Lean bodies, unconditional bare realizability, the hub-determinant form, the cone rank law `6(|V|−1) − def₂(G)`, and the direct-attainment statement | **(K-bare-ext) REFUTED as stated** (a *route* finding — `hbareSplit` UNTOUCHED and still pinned); (BE-10)/(BE-11)/(BE-12) **proven**; (BE-13) **proven-informally**, exact at 68/68; **(BE-14) OPEN**, measured 774/774, hard step isolated to `Y° ⊄ Z(G)`; **since 2026-08-26 (direction BTWOCUT)** **(BE-25)–(BE-29)**, Steps BE24–BE28, driver modes `wcheck`/`spqr`/`earfix`/`moduli`/`crosspair`/`hunt`/`probe`/`validate` (`w4/btwocut.py`) — the strengthened statement **PINNED** (S-mark closes, S-all does not, with the cost of each stated), the simultaneity worry proved **VACUOUS** by lower semicontinuity, a new elementary theorem (3-connected **minus one edge** still has `def₂ = def₃ = 0`) making the leaf base free, BINDUC's 56 ear misses **cleared as a constructor artifact**, the general-position half **dissolved on everything swept** (16/16, hunt empty at 13 484), and the induction's one genuinely-new obligation **named**: cross-pair welding; **since 2026-08-26 (direction BINDUC)** **(BE-20)–(BE-24)**, Steps BE19–BE23, driver modes `base`/`flatwit`/`gate`/`twocut`/`rank2`/`ear`/`hubplane`/`force`/`validate` (`w4/binduc.py`) — the FREE base (3-connected ⇒ `def₂ = 0`, exhaustive at 226 891), the exact 2-cut `max`-law **refuting BZAVOID's asserted `− 6`**, the rank-half composition criterion, the hub-plane construction (5 824 per-graph theorems) and the **generalized forcing mechanism** which strictly generalizes (BE-15)'s triangle rule and **fires empty as MEASURED** — **which is also the scope correction to (BE-15)(ii)**: its cap-free closure covers the TRIANGLE-forced mechanism, not the general one; **since 2026-08-26 (direction BZAVOID)** **(BE-15)–(BE-19)**, Steps BE14–BE18, driver modes `tri`/`crit`/`cap`/`pn`/`flat`/`sq`/`glue`/`validate` (`w4/bzavoid.py`) — the generalized forced-class cap and the **cap-free closure of the falsification arm at every graph**, the **planar-atom molecular identification** off the Lean bodies, the landed `G²` apparatus and the transversality count both **CLOSED**, and (BE-14) reduced to 2-connected graphs: **(BE-15)(ii)/(BE-16)(i)(ii)(iv)/(BE-17)(i)(ii)/(BE-18) proven, (BE-15)(i) proven-informally, (BE-16)(iii) proven on the distinct-adjacent-points locus, (BE-17)(iii) measured; (BE-14) still OPEN, `hbareSplit` untouched**; **since 2026-08-27/28 (directions BIMAGE, BEARCASE, BEARFULL, BSHARP — this clause repairs an index gap the first three left)** **(BE-30)–(BE-48)**, Steps BE29–BE47, drivers `w4/bimage.py`, `w4/bearcase.py`, `w4/bearfull.py`, `w4/bsharp.py` — the ear's image classified on the Klein quadric, (α) closed with the reach formula proved for `m ≥ 3`, the short-cycle law, and the (b1)-sharpening **dichotomy**; **since 2026-08-28 (direction BRULE)** **(BE-49)–(BE-53)**, Steps BE48–BE52, driver modes `dom`/`sep`/`domin`/`wit`/`hunt`/`validate` (`w4/brule.py`) — (b3)'s honest domain, the **separation theorem** making (b3) free wherever a BSHARP mechanism fires, the (R)/(Z) dominance correcting (BE-37)(ii)'s inference, and the one-witness-per-shape discharge; **since 2026-08-29 (direction BWIN)** **(BE-54)–(BE-58)**, Steps BE53–BE57, driver modes `dec`/`sweep`/`exc`/`cls`/`wide`/`validate` (`w4/bwin.py`) — the modular-law reformulation, the end-choice lemma and rank-one budget, the excess law, **the window identity PROVED as a CLASS THEOREM**, and job 3's window-is-not-the-barbells census; the owning section's six continuation verdict blocks are authoritative for all twenty-nine labels |
| §(K-mech) | `MX-` ✓ | (MX-1)–(MX-9); driver modes `--flex`/`--wide`/`--inc`/`--sigma`/`--sweep` (`mech.py`) | the mechanisms of the residual (W2)/(W4) anomalies: the realizable-load space `Ω`, α-confinement, pole-cluster loads, the welded flex, the 6v11e rescue, the σ rider | (MX-1)/(MX-2) proven; (MX-3)–(MX-7) proven-informally; (MX-8) settled-NO in the probed family; (MX-9) measured |
| §(K-grid) | `GR-` ✓  ; **since 2026-08-19 (direction GTMPL, eighth fan-out)** (GR-79)–(GR-84), Steps G98–G103, driver modes `--charge`/`--frame`/`--tpl`/`--min`/`--wit`/`--e1`/`--lam`/`--val` (`w4/gtmpl.py`), the `n_hub = 16` **witness shape** and its 30-member family  ; **since 2026-08-19 (direction GFLOW, eighth fan-out)** (GR-85)–(GR-90), Steps G104–G109, driver modes `--model`/`--chain`/`--exact`/`--desc`/`--big`/`--adv`/`--validate` (`w4/gflow.py`), the clauses **(GR-R1)** and **(GR-C2)**  ; **since 2026-08-19 (direction GCOLL, eighth fan-out)** (GR-91)–(GR-96), Steps G110–G115, driver modes `--slack`/`--dem`/`--tf`/`--suff`/`--big8`/`--bigp`/`--wit`/`--dfg`/`--adv` (`w4/gcoll.py`), the Petersen witness family | (GR-1)–(GR-6); Steps G0–G7; driver blocks GR-D1–GR-D5 (`grid.py`); **since 2026-08-06 (direction G)** (GR-7)–(GR-11) + the primed successor **(GR-4′)** (recorded under (GR-4) as its repaired form, per L4 no-renaming), Steps G8–G13, driver modes `--formula`/`--treetriple`/`--wide`/`--validate` (`gridwit.py`); **since 2026-08-07 (direction E)** (GR-12)–(GR-15), Steps G14–G18, driver modes `--restate`/`--hard`/`--sep`/`--exemplar`/`--validate` (`packmm.py`); **since 2026-08-07 (direction TCOL)** (GR-16)–(GR-20), Steps G19–G23, driver modes `--branch`/`--runs`/`--pack`/`--hier`/`--wide`/`--validate` (`w4/gridcol.py`; `m2/gridcol.m2` not needed); **since 2026-08-07 (direction CFLANK)** (GR-21)–(GR-26), Steps G24–G28, driver modes `--law`/`--adv`/`--cubic`/`--lam`/`--lam6`/`--dens`/`--tight`/`--validate` (`w4/cflank.py`; `m2/cflank.m2` not needed, `§(K-prof)`/`PF-` unopened); **since 2026-08-13 (direction GCAP)** (GR-27)–(GR-28), Steps G29–G33, driver modes `--probe`/`--law`/`--cap`/`--flip`/`--adv`/`--validate` (`w4/gcap.py`; `m2/gcap.m2` not needed, `§(K-gcap)`/`GC-` unopened); **since 2026-08-13 (direction GUNIF)** (GR-29)–(GR-31), Steps G34–G37, driver modes `--menu`/`--ledger`/`--wit`/`--repair`/`--validate` (`w4/gunif.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened, `§(K-unif)`/`GU-` still not minted); **since 2026-08-13 (direction GEXIST)** (GR-32)–(GR-35), Steps G38–G42, driver modes `--exh`/`--charge`/`--repair`/`--adv`/`--validate` (`w4/gexist.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a third time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-13 (direction GORIENT)** (GR-36)–(GR-39), Steps G43–G47, driver modes `--hall`/`--kill`/`--hot`/`--adv`/`--validate` (`w4/gorient.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a fourth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-15 (direction GDEV)** (GR-40)–(GR-42), Steps G48–G52, driver modes `--charge`/`--bound`/`--adv`/`--hunt`/`--validate` (`w4/gdev.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a fifth time, `§(K-unif)`/`GU-` still not minted) *(clause BACKFILLED at the GADM landing — the GDEV landing recorded its claim only in the narrative entry below)*; **since 2026-08-17 (direction GADM)** (GR-43), Steps G53–G57, driver modes `--nk`/`--free`/`--balance`/`--adv`/`--validate` (`w4/gadm.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a sixth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-18 (direction GPSA)** (GR-44)–(GR-45), Steps G58–G62, driver modes `--sdr`/`--balance`/`--odd`/`--adv`/`--validate` (`w4/gpsa.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a seventh time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-18 (direction GDESC)** (GR-46)–(GR-48), Steps G63–G67, driver modes `--stuck`/`--cases`/`--opt`/`--adv`/`--validate` (`w4/gdesc.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened an eighth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-19 (direction GBAL)** (GR-49)–(GR-54), Steps G68–G73, driver modes `--zform`/`--oracle`/`--two`/`--split`/`--thm`/`--adv`/`--validate` (`w4/gbal.py`; the argument stayed inside §(K-grid)'s own family again, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a ninth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction YLOC, seventh fan-out)** (GR-61)–(GR-66), Steps G80–G85, driver modes `--loc`/`--fibre`/`--par`/`--coll`/`--fit`/`--cert`/`--adv`/`--validate` (`w4/yloc.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a tenth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction BALB, seventh fan-out)** (GR-67)–(GR-72), Steps G86–G91, driver modes `--anchor`/`--flip`/`--ceil`/`--exh`/`--big`/`--adv`/`--validate` (`w4/balb.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, an eleventh time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction AGLU, seventh fan-out)** (GR-73)–(GR-78), Steps G92–G97, driver modes `--pool`/`--pin`/`--kill8`/`--lam8`/`--adv`/`--val` (`w4/aglu.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a twelfth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened) | the tight-stratum residual of (AC-6): eigen-blocks as conic direction networks / generalized-spline systems, the counting obstruction families ((GR-3); unified as **(GR-8)** sub-multigraph cycle spaces), chart-image membership, the 907-shape census, the interpolation factorization (GR-7), the tree-triple certificate theorem (GR-9), the merged residual (GR-10), the ε-adic fallback (GR-11), the branch-level reduction to the hub multigraph (GR-16), the circuit run law (GR-17), the 6-spanning-tree packing statement (GR-18), the collapse-order hierarchy (GR-19), the excess law (GR-21), the five sparsity caps (GR-22), the flip injection (GR-23), the private-branch repair theorem (GR-24), the cut criterion (GR-25), the 40 742-shape exhaustive hunt (GR-26), the block-additive exact computation of the (GR-8) maximum (GR-27), the closed defect formula and `g ≤ 1` cap (GR-28), the exhaustive dart-menu budget ledger (GR-29), the exact-boundary refutation of the all-`k` cap (GR-30), the per-shape survival + sweep-local repair-distance measurement (GR-31), the capacity theorem (GR-32), the weakness/orientation lemma (GR-33), the union-bound refutation + rung-minority rule (GR-34), the submodularity/uncrossing lemma (GR-35), the structural interior-adjacency charge (GR-36), the (c,m) selection model and its cut-space parity obstruction (GR-37), the exact slack identity / attachment lemma / intersection kill (GR-38), the capacity-tight structure theorem with its saturation kills (GR-39), the corner charge (GR-40), the parity floor (GR-41), the pentagon-necklace refutation family (GR-42), the odd-cycle-packing shift floor (GR-43), the exact parity-layer selection formula with its automatic Hall/SDR discharge (GR-44), the balance-move calculus (GR-45), its one-move transitivity (GR-46), the (X, φ, T) normal form (GR-47), the stuck-case escape catalogue (GR-48), the z-form bijection (GR-49), the orientation criterion (GR-50), the weight criterion (GR-51), the parity theorem (GR-52), the splitting lemma (GR-53), the balance theorem (GR-54), the z-form translation of the chunk invariants (GR-61), the degree-predicate refutation (GR-62), the parity-step audit (GR-63), the collision bound (GR-64), the fit identity (GR-65), the GBAL-certificate measurement (GR-66), the M-anchored z-form and parity law (GR-67), the closed-form legal-move price (GR-68), the imbalance ceiling with its exact boundary (GR-69), the reduction to one availability clause with its exhaustive stratum verification and T1 refutation (GR-70), the beyond-stratum extension with cap-free certificates (GR-71), the slack-0 degree lemma and its J-charge extension to arbitrary branch sets (GR-73), the `n_hub = 8` AA-glue pinning to a single template (GR-74), the `n_hub = 8` intersection-kill theorem (GR-75), the general-`n` W-charge forcing `n_hub ≥ 10` (GR-76), the `n_hub = 8` binding-non-laminarity census (GR-77), and the exhaustive `n_hub = 8` fully-good-colouring census (GR-78) | reduction proven; (GR-2) a proven refutation of the former (AC-6) close-route sentence; **(GR-4) refuted-as-stated, repaired as (GR-4′), off the critical path; (GR-9) proven; (GR-12)/(GR-13)/(GR-14) proven-informally — the (GR-10) min-max REFUTED as posed, (GR-10) itself open (exhaustively certified where swept); (GR-16)–(GR-19) proven — the branch reduction, circuit run law, 6-tree packing and collapse hierarchy — collapse order 4 measured at all 18 habitat separators; (GR-21)–(GR-25) proven — the excess law, five sparsity caps, flip injection, private-branch repair, cut criterion — TCOL's two named flank sites both CLOSED AS A ROUTE, (GR-26) exhaustive over 40 742 shapes with no hit; **(GR-27) proven; (GR-28)(i)–(iii) proven, (GR-28)(iv) REFUTED at `k ≥ 3` with an exact boundary — a THEOREM at `n_hub ≤ 6` (GR-29's ledger), FALSE from `n_hub = 8` on (GR-30's four witnesses, `g` up to 3) — the certificate-3 target still proven per swept shape at every `D = 0` shape checked; per-shape (GR-15) HOLDS at all four new witnesses and *Step G32*'s ≤ 2-flip repair law is sweep-local, breaking at `n_hub = 16` (GR-31)**; **(GR-32)–(GR-33) and (GR-35) proven — the capacity theorem (whole graph exactly critical, every proper chunk one unit slack), the weakness lemma (binding needs ≥ 2 aligned per-hub weaknesses; the all-even case is a pure orientation problem) and the uncrossing lemma (defect submodular) reduce the uniform target to a minority-dart orientation problem; (GR-34) REFUTES the uncorrelated union-bound mechanism by a constructed witness (`CL10`) while a correlated rung-minority rule closes the whole ladder family — GEXIST is an honest MISS, no g-flank found**; **(GR-36)–(GR-39) proven — the structural charge (the corrected obstruction family is the binding-capable chunks, strictly larger than capacity-tight), the (c,m) selection model (matching-based colourings, cut-space parity obstruction), the intersection kill (settled VACUOUSLY STRONG at `n_hub ≤ 6` — binding is laminar, no crossing same-block pairs), and the hot-hub structure theorem + kills (0 fully-hot hubs, now EXHAUSTIVE over all 4920 shapes) — GORIENT is an honest MISS, re-anchoring the target on a bounded-deviation selection principle (W3 the sticking instance, needing `d = 3` against `d ≤ 2` elsewhere), no g-flank found**; **(GR-40)–(GR-42) proven (direction GDEV) — the corner charge (tight at W3M, where (GR-36) prices 0), the parity floor (deviations bounded below by the coset invariant `φ*`), and the pentagon necklaces: the bounded-deviation selection form is REFUTED AS POSED (`d ≥ m/2` unbounded; every member rank-certified fully-good — a form-refutation, never a flank); the layer split measured, `d_fg = d_adm` at 133/133**; **(GR-43) proven (direction GADM) — the odd-cycle-packing shift floor: `d_par = d_adm = d_fg = m` EXACTLY at NK(2)/6/8/10 (rank-certified at the optimum, up to `n_hub = 50`), so the shift-metric layer is UNBOUNDED and the growth law's bounded-correction reading is REFUTED while the (a′) `d_fg = d_adm` law SURVIVES its first large-`d` test; ledger entry 5 (per-shape admissibility) settled as a separate OPEN statement ((GR-37)(iii)'s balance clause statement-beyond-proof); the W3 stick corrected to a 1-shift + 1-balance split — an honest MISS on (a′)-as-a-theorem, no g-flank found**; **(GR-44)–(GR-45) proven (direction GPSA) — the Hall/SDR step AUTOMATIC and `d_par(M) = w_M` EXACT (entry 5's parity half PROVEN, (GR-37)(iii) repaired there; the balance clause stays statement-beyond-proof), plus the cut-move calculus with its exact flip formula — entry 5's balance half true-modulo-named-gap (the descent lemma's stuck case), exhaustively true at 97 censused shapes, entry 5 NOT a HIT, no g-flank found**; **(GR-46)–(GR-48) proven (direction GDESC) — the move family is ONE-MOVE TRANSITIVE, so the descent lemma over the FULL family is EQUIVALENT to entry 5's balance half (the stuck case no smaller residual; a full-family demotion witness would be E1 clause (v)); the (X, φ, T) normal form restates balance as matching flexibility; the escape catalogue's PROVEN {T1, T2} kill is REALIZED at n = 30 — the bounded {T1, T2} descent route DEMOTED BY WITNESS while {T1, T2, K3} stays unbeaten, entry 5 still OPEN and NOT a HIT with its residual named input (X), (b′)'s unmeasured half measured, no g-flank found**; residual = (GR-15), OPEN unchanged, no flank found, the route re-anchored on the growth-law form — (a′) primary with its sticking case named (fixed-μ exchange insufficient); GADM's shift-metric routing of the thirteenth was OVERRIDDEN by the accepted 2026-08-18 recon verdict (GPSA, ledger entry 5 — LANDED 2026-08-18; GDESC, the descent lemma's stuck case — LANDED 2026-08-18); (GR-49)–(GR-54) proven (direction GBAL, one of five in the sixth fan-out) — the z-form absorbs the (c, m)/coset/SDR/matching apparatus into one bit per branch, balance becomes a degree-constrained orientation decided EXACTLY in polynomial time, the two-sided Hall condition collapses to a local weight inequality, a parity contradiction shows one monochromatic-pair hub per side is harmless, and a finite exhaustion over the maximal constraint structures shows one always suffices — chaining to **the balance theorem**: **entry 5 is PROVEN in BOTH halves, a HIT** (the parity half re-derived without Petersen, `d_par(M) = w_M` untouched), **E3 ARMED but does NOT fire** (entry 1's (a′) stays open), the (GR-45)–(GR-48) apparatus subsumed not contradicted, no g-flank found — the certificate-3 uniformity ROUTE stays dead as posed**; **(GR-61)–(GR-66) proven-informally (direction YLOC, one of five in the seventh fan-out)** — the pinned GBAL-localization route DEMOTED BY WITNESS (GR-62): full goodness is not a function of the (GR-50) degree data, so no (GR-51)-shaped criterion applies to the chunk system; the coordinator's predicted break point REFUTED as stated (GR-63) — (GR-52) localizes for free, the chain actually breaking two links earlier, at (GR-50)→(GR-51); the positive content is a colouring-free collision bound on `d_fg` (GR-64) and a coordinate-free fit identity unifying `dist(m, M)` and `z_mono(S)` (GR-65); GBAL's own certificate measured against (Y), missing both constraints (GR-66) — input (Y) stays OPEN, not hit, **E3 (ARMED by GBAL) does NOT fire**, no g-flank found; **(GR-67)–(GR-72) proven (direction BALB, one of five in the seventh fan-out)** — the M-anchored z-form gives the PARITY LAW (every per-matching layer gap EVEN) and is the perfect-matching instance of the landed (GR-65)(i) fit identity, independently re-derived and corroborating it (GR-67); every legal move is priced in closed form, matching branches and whole 2-factor cycles FREE, PROVING (b′)'s price half outright (GR-68); the imbalance ceiling `\|δ\| ≤ 2 min(k, ⌊n_hub/4⌋)` is a THEOREM at `n_hub ≤ 6` and FALSE from `n_hub = 8` at an explicit Wagner-graph witness (GR-69); (b′) reduces to one availability clause, verified EXHAUSTIVELY on the whole stratum in its landed T1-only instance, which is REFUTED from `n_hub = 8` with stuck witnesses each repaired at price 0 by a named mixed-pair successor (GR-70); (b′) extended to 536 exact shapes at `n_hub = 8/10/12` with cap-free per-matching certificates at `n = 30` (GR-71) — **(b′) stays OPEN, NOT a HIT**, residual Clause A′'s doubly-blocked case; no g-flank found; **(GR-73)–(GR-78) proven/measured (direction AGLU, one of five in the seventh fan-out)** — ledger attack (c) is **SETTLED NEGATIVE at `n_hub = 8`**: the AA-glue configuration is pinned to a single 10-branch template (GR-74) and proven NOT realizable there, independently certified by an EXHAUSTIVE, uncapped scan of the complete stratum that reproduces (GR-38)'s own `n_hub ≤ 6` headline exactly, so the (GR-38) intersection kill is a **THEOREM at `n_hub = 8`, non-vacuously** (GR-75); a general-`n` charge pushes the open case to **`n_hub ≥ 10`**, a three-template question (GR-76); the dispatch's predicted consequence is **REFUTED** — outright binding laminarity is FALSE at `n_hub = 8` (3 774 crossing same-block binding pairs, EXHAUSTIVE, against 0 at `n_hub ≤ 6`), so only the **maximal** family's uncrossing survives (GR-77); the (GR-15) counting-side target holds EXHAUSTIVELY over the whole `n_hub = 8` stratum with no cap, 86.9 % of colourings fully good, no g-flank (GR-78) — a HIT on the not-realizable branch; no gap-map status moves, (GR-15) OPEN modulo (GR-4′), class uniformity untouched  ; **since 2026-08-25 (direction GFLIP, single dispatch)** (GR-97)–(GR-99), Steps G116–G119, driver modes `--form`/`--lemma`/`--thm`/`--wit`/`--validate` (`w4/gflip.py`) — the demand form of the (GR-51) criterion, the cubic counting lemma, and the selection theorem (at most `b` A-branches blocked); **(GR-R1) PROVEN**, so (GR-89)(ii)'s `n`-free `≤ 12` is a THEOREM; (GR-100)/(GR-101)/Step G120 returned to the tail  ; **since 2026-08-25 (direction GCHEAP, single dispatch)** (GR-100)–(GR-104), Steps G120–G124, driver modes `--cap`/`--sel`/`--bnd`/`--validate` (`w4/gcheap.py`) — the lone-dart identity + blocked-end capacity, the selection corollary (every-step (GR-C2) PROVEN for `n_hub < 6|δ|`, so (b′) at the constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum), the stall tax, the `n_hub = 12` boundary witness (per-configuration (GR-C2) REFUTED, boundary exact both ways), and the price-form residual (GR-104); the GFLIP-returned (GR-100)/(GR-101)/Step G120 re-claimed here  ; **since 2026-08-25 (direction GPRICE, single dispatch)** (GR-105)–(GR-109), Steps G125–G129, driver modes `--cell`/`--seed`/`--hunt`/`--mech`/`--validate` (`w4/gprice.py`) — the colour-swap identity `f(p) = f(p̄)`, the reversal-set normal form at `O ⊆ M` (`dist = n − |R|` exact, `f` computable in `2^n`), the reachability theorem (affine pattern-subspaces, the linkage obstruction), the minted **balance law (GR-108)** — (GR-104)(i) a THEOREM at `2k = 2`, every `n`, modulo it alone — and the status statement (GR-109)  ; **since 2026-08-25 (direction GBLAW, single dispatch)** (GR-110)–(GR-114), Steps G130–G134, driver modes `--form`/`--conn`/`--recomb`/`--strand`/`--validate` (`w4/gblaw.py`) — the arc-transversal normal form, the recombination theorem (maximum-family connectivity, the universal-linkage refutation shape), the escape lemma (**(GR-108) ⟸ existential escape**), the measured escape verdict (universal escape REFUTED at the `n = 16` strand witness; existential escape 0 failures at 1 099 pairs), and the status statement (GR-114)  ; **since 2026-08-26 (direction GXESC, single dispatch)** (GR-115)–(GR-119), Steps G135–G139, driver modes `--ledger`/`--closure`/`--hunt`/`--verify`/`--strand`/`--validate` (`w4/gxesc.py`) — the reversal-label ledger (M-closed ⟹ balance-valid at every `2k`), the **refutation of (GR-108) and existential escape by four verified witnesses from `n = 16`**, the gap-2 law (⟺ (GR-104)(i) at the cell, proven except at the all-(2,2) case), the measured record, and the status statement (GR-119) |
| §(K-res) *(in `notes/Pencil-informal-grid.md`, end of file)* | `RS-` ✓ (2026-08-28, direction RESGRID) | (RS-1)–(RS-6), *Steps RS1–RS10*; (RS-7)–(RS-12) returned; driver modes `--audit`/`--dimz`/`--rank`/`--theta`/`--validate` (`w4/resgrid.py`) | the residual-habitat transport audit: (RS-1) the habitat-free rank identity, (RS-2) the slack law, (RS-3) the forced core witness + rigidity-covers-excess, (RS-4) the transported discharge, (RS-5) the (K-res) grid residual ((GR-15)'s criterion, quantifier widened; per-shape proven at `W19`/`S29`/`NT21c3`), (RS-6) the deficient-fringe refutation (θ(2,3,7)) | (RS-1)–(RS-4), (RS-6) proven-informally; (RS-5) open as the uniform statement, proven per-shape at the three named shapes; the (K-res) wave a user call |
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
| §widened kernels (routes 1/3) | `WK-` | (E-loc); **(K-res)** | the routes-1/3 kernel widening; (K-res) is the widened kernel carried as a byte-identical sibling of `hK` |

## Registry — `notes/Pencil-strategy.md`, `Phase39.md`, `Phase39-design.md`

| owner | labels in use | what the family is |
|---|---|---|
| strategy §4 | **C1**, **C2**, **C3** | the three candidate stronger inductive invariants (C1 = dominance of the `V_bc` map, run and struck) |
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
