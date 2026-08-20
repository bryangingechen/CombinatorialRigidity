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
list (`notes/Phase39.md` *Current state*, the "keep going on my own
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

**Disposition: RENAMED**, per the 2026-08-20 user adjudication (`Phase39.md`
*Current state*): the rename option this record left open for the user was
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

## Reserved namespace — probe KBARE-FALSIFY (2026-08-20, incoming)

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
| §(K-out) | `OC-` ✓  ; **since 2026-08-19 (direction SIGZ, eighth fan-out)** (OC-35)–(OC-39), Steps O31–O36, driver modes `--reduce`/`--spans`/`--budget`/`--slack`/`--theta`/`--p21`/`--hunt` (`w4/sigz.py`), the Kirchhoff-flow form and the `slack`/`δ`/`ρ` ledger  ; **since 2026-08-19 (direction OSCHU, eighth fan-out)** (OC-29)–(OC-34), Steps O25–O30, driver modes `--restate`/`--gtarget`/`--rekey`/`--census1`/`--census2` (`w4/oschu.py`), pools POOL-OS / POOL-OQ / POOL-OG / POOL-OR / POOL-OC2 | (OC-1)–**(OC-16)**; Steps O1–O12; the **pools** POOL-C / POOL-G / POOL-S / POOL-B and (since direction O, 2026-08-06) POOL-CW / POOL-A / POOL-W / POOL-SL; driver modes `--comb`/`--pool`/`--shapes`/`--build` (`outerline.py`) and `--wide`/`--adv`/`--wrench`/`--slide` (`outerwide.py`) + `outerwide.m2`; **since 2026-08-19 (direction OCON)** (OC-17)–(OC-22), Steps O13–O18, driver modes `--validate`/`--check`/`--control` (`w4/ocon.py`), pools POOL-OV / POOL-OC / POOL-OZ; **since 2026-08-19 (direction ZNEQ, seventh fan-out)** (OC-23)–(OC-28), Steps O19–O24, driver modes `--factor`/`--sweep`/`--reject`/`--transfer` (`w4/zneq.py`), pools POOL-ZF / POOL-ZQ / POOL-ZN / POOL-ZT / POOL-ZR | (OUT)'s hypothesis measured: the exact hinge-rate reading, the ambient-generic map, the never-automatic negative, the constructed silent point, the two pool distributions, the sampler defect, and the residual; (since OCON) the hard-stratum target-rank qualifier is free, and the (OC-8) residue reduces to a `Z ≠ ∅` + chart-irreducibility + one-chart-point reduction; (since ZNEQ) input (a) `Z ≠ ∅` itself factors into a necessary-for-`hK` half dominated by §(K-grid) (GR-10) and a target-rank half whose failure is a codimension-2 Schubert jump, with a self-refuted-and-corrected closed form and a 138/138 witness census | **(OC-3)** proven-informally and load-bearing; (OC-1) proven-informally; (OC-2)/(OC-5)/(OC-6)/(OC-7) measured; (OC-4) exhibited; **(OC-8) open**. **(OC-7) is a harness item**, `notes/scripts/README.md` *Harness debt* 4 — **CLEARED 2026-08-06** by the re-baselining round, whose slice S2 also minted **(OC-9)** here (the FIELD half of the coincident-hinge guard's adversarial test: the guard rejects 58/357 and its rejection set strictly contains the two-end diagnostic's 39). **(OC-17)–(OC-21) proven-informally** (Steps O13–O16, direction OCON); **(OC-22) an assessment**; **(OC-8) OPEN, reshaped** — the hard-stratum qualifier struck as free, two named inputs (`Z ≠ ∅`, chart irreducibility) added rather than removed. **(OC-23)–(OC-25) proven-informally, (OC-26) proven-informally (its own first closed form refuted by construction and corrected), (OC-27) measured (138/138 witnesses), (OC-28) proven-informally (a conditional domination on the open §(K-grid) gap (GR-10), the boundary exhibited at `P21`)** (Steps O19–O24, direction ZNEQ); **input (a) OPEN as a class-uniform statement, NOT an independent gap; (OC-8) OPEN, unchanged** |
| §(K-ind) | `IN-` | (I0)–(I4); Steps I0–I6 | numerical invariant along the generating moves | refuted as a route; (I3) a positive by-product |
| §(K-Δ) | `DL-` | **(M1)**, **(M2)**, **(M3)**; (N1), (N2) | the Δ-matroid literature hunt: (M1)–(M3) are the **three hypothesis tests**, (N1)/(N2) the two readings bought | NO HIT; discharged |
| §(K-bare-ext) | `BE-` | (K-bare-ext) | the (K-bare) stub | open, nothing being developed |
| §(K-mech) | `MX-` ✓ | (MX-1)–(MX-9); driver modes `--flex`/`--wide`/`--inc`/`--sigma`/`--sweep` (`mech.py`) | the mechanisms of the residual (W2)/(W4) anomalies: the realizable-load space `Ω`, α-confinement, pole-cluster loads, the welded flex, the 6v11e rescue, the σ rider | (MX-1)/(MX-2) proven; (MX-3)–(MX-7) proven-informally; (MX-8) settled-NO in the probed family; (MX-9) measured |
| §(K-grid) | `GR-` ✓  ; **since 2026-08-19 (direction GTMPL, eighth fan-out)** (GR-79)–(GR-84), Steps G98–G103, driver modes `--charge`/`--frame`/`--tpl`/`--min`/`--wit`/`--e1`/`--lam`/`--val` (`w4/gtmpl.py`), the `n_hub = 16` **witness shape** and its 30-member family  ; **since 2026-08-19 (direction GFLOW, eighth fan-out)** (GR-85)–(GR-90), Steps G104–G109, driver modes `--model`/`--chain`/`--exact`/`--desc`/`--big`/`--adv`/`--validate` (`w4/gflow.py`), the clauses **(GR-R1)** and **(GR-C2)**  ; **since 2026-08-19 (direction GCOLL, eighth fan-out)** (GR-91)–(GR-96), Steps G110–G115, driver modes `--slack`/`--dem`/`--tf`/`--suff`/`--big8`/`--bigp`/`--wit`/`--dfg`/`--adv` (`w4/gcoll.py`), the Petersen witness family | (GR-1)–(GR-6); Steps G0–G7; driver blocks GR-D1–GR-D5 (`grid.py`); **since 2026-08-06 (direction G)** (GR-7)–(GR-11) + the primed successor **(GR-4′)** (recorded under (GR-4) as its repaired form, per L4 no-renaming), Steps G8–G13, driver modes `--formula`/`--treetriple`/`--wide`/`--validate` (`gridwit.py`); **since 2026-08-07 (direction E)** (GR-12)–(GR-15), Steps G14–G18, driver modes `--restate`/`--hard`/`--sep`/`--exemplar`/`--validate` (`packmm.py`); **since 2026-08-07 (direction TCOL)** (GR-16)–(GR-20), Steps G19–G23, driver modes `--branch`/`--runs`/`--pack`/`--hier`/`--wide`/`--validate` (`w4/gridcol.py`; `m2/gridcol.m2` not needed); **since 2026-08-07 (direction CFLANK)** (GR-21)–(GR-26), Steps G24–G28, driver modes `--law`/`--adv`/`--cubic`/`--lam`/`--lam6`/`--dens`/`--tight`/`--validate` (`w4/cflank.py`; `m2/cflank.m2` not needed, `§(K-prof)`/`PF-` unopened); **since 2026-08-13 (direction GCAP)** (GR-27)–(GR-28), Steps G29–G33, driver modes `--probe`/`--law`/`--cap`/`--flip`/`--adv`/`--validate` (`w4/gcap.py`; `m2/gcap.m2` not needed, `§(K-gcap)`/`GC-` unopened); **since 2026-08-13 (direction GUNIF)** (GR-29)–(GR-31), Steps G34–G37, driver modes `--menu`/`--ledger`/`--wit`/`--repair`/`--validate` (`w4/gunif.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened, `§(K-unif)`/`GU-` still not minted); **since 2026-08-13 (direction GEXIST)** (GR-32)–(GR-35), Steps G38–G42, driver modes `--exh`/`--charge`/`--repair`/`--adv`/`--validate` (`w4/gexist.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a third time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-13 (direction GORIENT)** (GR-36)–(GR-39), Steps G43–G47, driver modes `--hall`/`--kill`/`--hot`/`--adv`/`--validate` (`w4/gorient.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a fourth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-15 (direction GDEV)** (GR-40)–(GR-42), Steps G48–G52, driver modes `--charge`/`--bound`/`--adv`/`--hunt`/`--validate` (`w4/gdev.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a fifth time, `§(K-unif)`/`GU-` still not minted) *(clause BACKFILLED at the GADM landing — the GDEV landing recorded its claim only in the narrative entry below)*; **since 2026-08-17 (direction GADM)** (GR-43), Steps G53–G57, driver modes `--nk`/`--free`/`--balance`/`--adv`/`--validate` (`w4/gadm.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a sixth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-18 (direction GPSA)** (GR-44)–(GR-45), Steps G58–G62, driver modes `--sdr`/`--balance`/`--odd`/`--adv`/`--validate` (`w4/gpsa.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened a seventh time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-18 (direction GDESC)** (GR-46)–(GR-48), Steps G63–G67, driver modes `--stuck`/`--cases`/`--opt`/`--adv`/`--validate` (`w4/gdesc.py`; no M2 leaf expected or opened, `§(K-gcap)`/`GC-` still unopened an eighth time, `§(K-unif)`/`GU-` still not minted); **since 2026-08-19 (direction GBAL)** (GR-49)–(GR-54), Steps G68–G73, driver modes `--zform`/`--oracle`/`--two`/`--split`/`--thm`/`--adv`/`--validate` (`w4/gbal.py`; the argument stayed inside §(K-grid)'s own family again, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a ninth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction YLOC, seventh fan-out)** (GR-61)–(GR-66), Steps G80–G85, driver modes `--loc`/`--fibre`/`--par`/`--coll`/`--fit`/`--cert`/`--adv`/`--validate` (`w4/yloc.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a tenth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction BALB, seventh fan-out)** (GR-67)–(GR-72), Steps G86–G91, driver modes `--anchor`/`--flip`/`--ceil`/`--exh`/`--big`/`--adv`/`--validate` (`w4/balb.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, an eleventh time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened); **since 2026-08-19 (direction AGLU, seventh fan-out)** (GR-73)–(GR-78), Steps G92–G97, driver modes `--pool`/`--pin`/`--kill8`/`--lam8`/`--adv`/`--val` (`w4/aglu.py`; the argument stayed inside §(K-grid)'s own family a further time, so `§(K-gcap)`/`GC-` were still never opened and return to the pool unopened, reserved-but-unopened, a twelfth time; `§(K-unif)`/`GU-` still not minted; no M2 leaf expected or opened) | the tight-stratum residual of (AC-6): eigen-blocks as conic direction networks / generalized-spline systems, the counting obstruction families ((GR-3); unified as **(GR-8)** sub-multigraph cycle spaces), chart-image membership, the 907-shape census, the interpolation factorization (GR-7), the tree-triple certificate theorem (GR-9), the merged residual (GR-10), the ε-adic fallback (GR-11), the branch-level reduction to the hub multigraph (GR-16), the circuit run law (GR-17), the 6-spanning-tree packing statement (GR-18), the collapse-order hierarchy (GR-19), the excess law (GR-21), the five sparsity caps (GR-22), the flip injection (GR-23), the private-branch repair theorem (GR-24), the cut criterion (GR-25), the 40 742-shape exhaustive hunt (GR-26), the block-additive exact computation of the (GR-8) maximum (GR-27), the closed defect formula and `g ≤ 1` cap (GR-28), the exhaustive dart-menu budget ledger (GR-29), the exact-boundary refutation of the all-`k` cap (GR-30), the per-shape survival + sweep-local repair-distance measurement (GR-31), the capacity theorem (GR-32), the weakness/orientation lemma (GR-33), the union-bound refutation + rung-minority rule (GR-34), the submodularity/uncrossing lemma (GR-35), the structural interior-adjacency charge (GR-36), the (c,m) selection model and its cut-space parity obstruction (GR-37), the exact slack identity / attachment lemma / intersection kill (GR-38), the capacity-tight structure theorem with its saturation kills (GR-39), the corner charge (GR-40), the parity floor (GR-41), the pentagon-necklace refutation family (GR-42), the odd-cycle-packing shift floor (GR-43), the exact parity-layer selection formula with its automatic Hall/SDR discharge (GR-44), the balance-move calculus (GR-45), its one-move transitivity (GR-46), the (X, φ, T) normal form (GR-47), the stuck-case escape catalogue (GR-48), the z-form bijection (GR-49), the orientation criterion (GR-50), the weight criterion (GR-51), the parity theorem (GR-52), the splitting lemma (GR-53), the balance theorem (GR-54), the z-form translation of the chunk invariants (GR-61), the degree-predicate refutation (GR-62), the parity-step audit (GR-63), the collision bound (GR-64), the fit identity (GR-65), the GBAL-certificate measurement (GR-66), the M-anchored z-form and parity law (GR-67), the closed-form legal-move price (GR-68), the imbalance ceiling with its exact boundary (GR-69), the reduction to one availability clause with its exhaustive stratum verification and T1 refutation (GR-70), the beyond-stratum extension with cap-free certificates (GR-71), the slack-0 degree lemma and its J-charge extension to arbitrary branch sets (GR-73), the `n_hub = 8` AA-glue pinning to a single template (GR-74), the `n_hub = 8` intersection-kill theorem (GR-75), the general-`n` W-charge forcing `n_hub ≥ 10` (GR-76), the `n_hub = 8` binding-non-laminarity census (GR-77), and the exhaustive `n_hub = 8` fully-good-colouring census (GR-78) | reduction proven; (GR-2) a proven refutation of the former (AC-6) close-route sentence; **(GR-4) refuted-as-stated, repaired as (GR-4′), off the critical path; (GR-9) proven; (GR-12)/(GR-13)/(GR-14) proven-informally — the (GR-10) min-max REFUTED as posed, (GR-10) itself open (exhaustively certified where swept); (GR-16)–(GR-19) proven — the branch reduction, circuit run law, 6-tree packing and collapse hierarchy — collapse order 4 measured at all 18 habitat separators; (GR-21)–(GR-25) proven — the excess law, five sparsity caps, flip injection, private-branch repair, cut criterion — TCOL's two named flank sites both CLOSED AS A ROUTE, (GR-26) exhaustive over 40 742 shapes with no hit; **(GR-27) proven; (GR-28)(i)–(iii) proven, (GR-28)(iv) REFUTED at `k ≥ 3` with an exact boundary — a THEOREM at `n_hub ≤ 6` (GR-29's ledger), FALSE from `n_hub = 8` on (GR-30's four witnesses, `g` up to 3) — the certificate-3 target still proven per swept shape at every `D = 0` shape checked; per-shape (GR-15) HOLDS at all four new witnesses and *Step G32*'s ≤ 2-flip repair law is sweep-local, breaking at `n_hub = 16` (GR-31)**; **(GR-32)–(GR-33) and (GR-35) proven — the capacity theorem (whole graph exactly critical, every proper chunk one unit slack), the weakness lemma (binding needs ≥ 2 aligned per-hub weaknesses; the all-even case is a pure orientation problem) and the uncrossing lemma (defect submodular) reduce the uniform target to a minority-dart orientation problem; (GR-34) REFUTES the uncorrelated union-bound mechanism by a constructed witness (`CL10`) while a correlated rung-minority rule closes the whole ladder family — GEXIST is an honest MISS, no g-flank found**; **(GR-36)–(GR-39) proven — the structural charge (the corrected obstruction family is the binding-capable chunks, strictly larger than capacity-tight), the (c,m) selection model (matching-based colourings, cut-space parity obstruction), the intersection kill (settled VACUOUSLY STRONG at `n_hub ≤ 6` — binding is laminar, no crossing same-block pairs), and the hot-hub structure theorem + kills (0 fully-hot hubs, now EXHAUSTIVE over all 4920 shapes) — GORIENT is an honest MISS, re-anchoring the target on a bounded-deviation selection principle (W3 the sticking instance, needing `d = 3` against `d ≤ 2` elsewhere), no g-flank found**; **(GR-40)–(GR-42) proven (direction GDEV) — the corner charge (tight at W3M, where (GR-36) prices 0), the parity floor (deviations bounded below by the coset invariant `φ*`), and the pentagon necklaces: the bounded-deviation selection form is REFUTED AS POSED (`d ≥ m/2` unbounded; every member rank-certified fully-good — a form-refutation, never a flank); the layer split measured, `d_fg = d_adm` at 133/133**; **(GR-43) proven (direction GADM) — the odd-cycle-packing shift floor: `d_par = d_adm = d_fg = m` EXACTLY at NK(2)/6/8/10 (rank-certified at the optimum, up to `n_hub = 50`), so the shift-metric layer is UNBOUNDED and the growth law's bounded-correction reading is REFUTED while the (a′) `d_fg = d_adm` law SURVIVES its first large-`d` test; ledger entry 5 (per-shape admissibility) settled as a separate OPEN statement ((GR-37)(iii)'s balance clause statement-beyond-proof); the W3 stick corrected to a 1-shift + 1-balance split — an honest MISS on (a′)-as-a-theorem, no g-flank found**; **(GR-44)–(GR-45) proven (direction GPSA) — the Hall/SDR step AUTOMATIC and `d_par(M) = w_M` EXACT (entry 5's parity half PROVEN, (GR-37)(iii) repaired there; the balance clause stays statement-beyond-proof), plus the cut-move calculus with its exact flip formula — entry 5's balance half true-modulo-named-gap (the descent lemma's stuck case), exhaustively true at 97 censused shapes, entry 5 NOT a HIT, no g-flank found**; **(GR-46)–(GR-48) proven (direction GDESC) — the move family is ONE-MOVE TRANSITIVE, so the descent lemma over the FULL family is EQUIVALENT to entry 5's balance half (the stuck case no smaller residual; a full-family demotion witness would be E1 clause (v)); the (X, φ, T) normal form restates balance as matching flexibility; the escape catalogue's PROVEN {T1, T2} kill is REALIZED at n = 30 — the bounded {T1, T2} descent route DEMOTED BY WITNESS while {T1, T2, K3} stays unbeaten, entry 5 still OPEN and NOT a HIT with its residual named input (X), (b′)'s unmeasured half measured, no g-flank found**; residual = (GR-15), OPEN unchanged, no flank found, the route re-anchored on the growth-law form — (a′) primary with its sticking case named (fixed-μ exchange insufficient); GADM's shift-metric routing of the thirteenth was OVERRIDDEN by the accepted 2026-08-18 recon verdict (GPSA, ledger entry 5 — LANDED 2026-08-18; GDESC, the descent lemma's stuck case — LANDED 2026-08-18); (GR-49)–(GR-54) proven (direction GBAL, one of five in the sixth fan-out) — the z-form absorbs the (c, m)/coset/SDR/matching apparatus into one bit per branch, balance becomes a degree-constrained orientation decided EXACTLY in polynomial time, the two-sided Hall condition collapses to a local weight inequality, a parity contradiction shows one monochromatic-pair hub per side is harmless, and a finite exhaustion over the maximal constraint structures shows one always suffices — chaining to **the balance theorem**: **entry 5 is PROVEN in BOTH halves, a HIT** (the parity half re-derived without Petersen, `d_par(M) = w_M` untouched), **E3 ARMED but does NOT fire** (entry 1's (a′) stays open), the (GR-45)–(GR-48) apparatus subsumed not contradicted, no g-flank found — the certificate-3 uniformity ROUTE stays dead as posed**; **(GR-61)–(GR-66) proven-informally (direction YLOC, one of five in the seventh fan-out)** — the pinned GBAL-localization route DEMOTED BY WITNESS (GR-62): full goodness is not a function of the (GR-50) degree data, so no (GR-51)-shaped criterion applies to the chunk system; the coordinator's predicted break point REFUTED as stated (GR-63) — (GR-52) localizes for free, the chain actually breaking two links earlier, at (GR-50)→(GR-51); the positive content is a colouring-free collision bound on `d_fg` (GR-64) and a coordinate-free fit identity unifying `dist(m, M)` and `z_mono(S)` (GR-65); GBAL's own certificate measured against (Y), missing both constraints (GR-66) — input (Y) stays OPEN, not hit, **E3 (ARMED by GBAL) does NOT fire**, no g-flank found; **(GR-67)–(GR-72) proven (direction BALB, one of five in the seventh fan-out)** — the M-anchored z-form gives the PARITY LAW (every per-matching layer gap EVEN) and is the perfect-matching instance of the landed (GR-65)(i) fit identity, independently re-derived and corroborating it (GR-67); every legal move is priced in closed form, matching branches and whole 2-factor cycles FREE, PROVING (b′)'s price half outright (GR-68); the imbalance ceiling `\|δ\| ≤ 2 min(k, ⌊n_hub/4⌋)` is a THEOREM at `n_hub ≤ 6` and FALSE from `n_hub = 8` at an explicit Wagner-graph witness (GR-69); (b′) reduces to one availability clause, verified EXHAUSTIVELY on the whole stratum in its landed T1-only instance, which is REFUTED from `n_hub = 8` with stuck witnesses each repaired at price 0 by a named mixed-pair successor (GR-70); (b′) extended to 536 exact shapes at `n_hub = 8/10/12` with cap-free per-matching certificates at `n = 30` (GR-71) — **(b′) stays OPEN, NOT a HIT**, residual Clause A′'s doubly-blocked case; no g-flank found; **(GR-73)–(GR-78) proven/measured (direction AGLU, one of five in the seventh fan-out)** — ledger attack (c) is **SETTLED NEGATIVE at `n_hub = 8`**: the AA-glue configuration is pinned to a single 10-branch template (GR-74) and proven NOT realizable there, independently certified by an EXHAUSTIVE, uncapped scan of the complete stratum that reproduces (GR-38)'s own `n_hub ≤ 6` headline exactly, so the (GR-38) intersection kill is a **THEOREM at `n_hub = 8`, non-vacuously** (GR-75); a general-`n` charge pushes the open case to **`n_hub ≥ 10`**, a three-template question (GR-76); the dispatch's predicted consequence is **REFUTED** — outright binding laminarity is FALSE at `n_hub = 8` (3 774 crossing same-block binding pairs, EXHAUSTIVE, against 0 at `n_hub ≤ 6`), so only the **maximal** family's uncrossing survives (GR-77); the (GR-15) counting-side target holds EXHAUSTIVELY over the whole `n_hub = 8` stratum with no cap, 86.9 % of colourings fully good, no g-flank (GR-78) — a HIT on the not-realizable branch; no gap-map status moves, (GR-15) OPEN modulo (GR-4′), class uniformity untouched |
| §(K-frame) | `FR-` ✓ | (FR-1)–(FR-7); the residual input **(FR-R1)**; Steps FR0–FR6; driver modes `--rulings`/`--pattern`/`--transport`/`--outer`/`--validate` (`framedom.py`) and M2 blocks (FR-M0)–(FR-M3) (`framedom.m2`); **since 2026-08-07 (direction PEX)** (FR-8)–(FR-14), Steps FR7–FR11, driver modes `--frame`/`--recipe`/`--strat`/`--kill`/`--validate`/`--recon` (`w4/patexist.py`; `m2/patexist.m2` not needed); **since 2026-08-19 (direction FRES)** (FR-15)–(FR-17), Steps FR12–FR15, no driver ((FR-18) reserved and unused) | the shared chart-to-frame dominance residue of §(K-out) (OC-16) / §(K-ann) (ANH-14): the minimal non-containment lemma, the ruling decomposition and determinant law at grid points, the `G′`-regridding transport, the 1904-site pattern battery, the θ(3,4,5) constructed witnesses, (since PEX) the bare-cycle stratum's finiteness + exhaustive enumeration, and (since FRES) the chart-map-vs-chart-variety correction that closes the residue with no rider | (FR-1)/(FR-2)/(FR-3) proven / proven-informally; (FR-4) superseded by **(FR-17)**, proven-informally with **no named gap**; (FR-5) measured (each certificate a per-site proof); (FR-6) exact per point, retro-certified by (FR-16); **(FR-R1) PROVEN** (Steps FR7–FR11, direction PEX); **(FR-15)–(FR-17) proven-informally** (Steps FR12–FR15, direction FRES) — no rider remains |
| §(K-chart) | `CH-` ✓ | (CH-1)–(CH-8); Steps CH1–CH8; driver modes `--empty`/`--guard`/`--fibre`/`--all` (`w4/cirr.py`) | *(new, 2026-08-19, direction CIRR)* the pencil chart of `G′` proven irreducible, ℚ-rational, a tower of affine-linear fibres: the constant-fibre-dimension restriction identified as `IsNondegPencilRealization` conjunct 3 ((CH-6)), the closure argument that makes the restriction cost nothing ((CH-4)), the nonemptiness clause and its girth ≥ 4 correction to §(K-frame) *Step FR13* ((CH-5)), and the consumer audit of §(K-out) (OC-19) / §(K-slide) (S1)(e) / §(K-dom) (D4) / §(K-ann) (ANH-9)(ii) ((CH-7)); (CH-8) is a pointer to the landed, strictly stronger `not_pencilNondegFeasible_of_triangle_two_hubs` | (CH-1)–(CH-7) proven-informally, no named gap; (CH-3)/(CH-6) proven; **a HIT** — all four consumers clean; no gap-map status moves |

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
