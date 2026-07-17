# Phase 34 — PROSPECT G3: the generic lift (work log)

**Status:** in progress (opened 2026-07-17, recon-first).

Planning input: `notes/Prospect.md` — the Tier-2 **G3** entry and its open
recon question. Queue position user-adjudicated 2026-07-10 (`notes/Prospect.md`
*Hand-off* item 4); the queue order re-confirmed with the user at this
opening (2026-07-17). Primary source: Jackson–Jordán, *The generic rank of
body-bar-and-hinge frameworks*, Eur. J. Combin. **31** (2010), 574–588 —
already the project's `jacksonJordan2009` bib entry / `formalization.yaml`
source (the def = corank bridge came from it in Phase 19).

## Current state

Phase just opened; nothing is built and no blueprint chapter is open. The
next concrete step is the **opening recon dispatch** (question stated
verbatim under *Hand-off / next phase*). Everything below the checklist is
transcribed from `notes/Prospect.md`'s survey record (source-grounded
2026-07-10), not re-derived this commit.

## What the phase targets (from the Prospect G3 entry)

Upgrade the project's **existence-form** realization statements to the
**generic** ("almost all realizations") form, via the Jackson–Jordán 2010
*coordinate* route (their Thms 5.2, 6.4, 7.2, 8.1/8.2 — survey read of the
`.refs` copy), which deliberately avoids Whiteley 1988's
variety-irreducibility machinery (Proposition 6 in Whiteley 1988 — the lift
both `body-bar.tex` and `body-hinge.tex` explicitly defer with "not pursued
here" remarks, standing since Phases 15/16). The affected statement surface:

- **Tay's body-bar theorem** (Phase 15, `thm:tay-witness`,
  `Graph.BodyBarFramework.tay_witness`) — existence-of-realization form.
- **Body-hinge Tay–Whiteley** (Phase 16, `thm:body-hinge-tay`,
  `Graph.BodyHingeFramework.body_hinge_tay`) — same form, via the
  `(δ−1)·G` reduction.
- **The molecular statements** (Phases 17–26 surface) — JJ 2010 p.13 notes
  that combining their generic-rank results with the (now-proved) molecular
  conjecture sharpens Cor 5.7 to *all generic* realizations of `G²`.

Per the adjudicated queue rationale, the genericity layer is built once,
over the final carrier — the Phase-33 `[Field K] [Infinite K]` chain for the
core, with the molecule application staying ℝ (Prospect K4). Whether that
carrier statement survives contact with JJ 2010's genericity device is
exactly the recon question — it is **not** settled here.

Likely seam if the phase runs long (codes-until-open, not pre-divided):
the body-bar/body-hinge layer vs. the molecular layer
(`notes/Prospect.md` *Hand-off*).

## Work-item checklist

- [ ] **R0 — the opening recon** (the product-route substitution question;
  stated exactly under *Hand-off / next phase*). Read-only; verdict shapes
  everything downstream.
- [ ] Adjudicate scope + route on R0's verdict; open the blueprint chapter
  (forward mode) only then.
- [ ] The build itself — sliced after R0; do not pre-plan slices here.

## Blockers / open questions

- **The R0 question** (below) — no build work is sanctioned until it
  returns.
- Downstream of R0, for the adjudication (questions, not claims): what
  genericity *notion* the formalization uses (JJ 2010 run their layer on
  algebraic independence over ℚ, inside ℝ — the device Phase 30 removed
  from this project; how "generic" is even stated over the Phase-33
  `[Field K] [Infinite K]` carrier is part of the route question), and
  which of the three statement layers (body-bar / body-hinge / molecular)
  the phase commits to.

## Hand-off / next phase

Next concrete step: **dispatch the opening recon (R0)** on the G3 open
recon question, verbatim from `notes/Prospect.md` *Open recon questions*:

> **G3:** can the Phase-30 product route replace JJ 2010's
> algebraic-independence-over-ℚ genericity layer, or does the "almost
> all" form genuinely need alg-indep back? (Bears on whether RELAX's
> simplification survives the strengthening.)

Read-only recon against the `.refs` JJ 2010 copy and the Phase-30 product
machinery (`exists_eval_ne_zero` product shots; `notes/Phase30.md`); the
verdict comes back to this note and drives the scope adjudication.

## Decisions made during this phase

- **Blueprint chapter-opening deferred until the R0 verdict lands**
  (2026-07-17, at open). A chapter written before the recon would
  transcribe JJ 2010's genericity layer as settled math against the
  project's carrier — the Phase-32 chapter-open trap (its zero-extension
  rank form was refuted by the pre-build recon; `notes/Phase32.md` *Recon
  verdicts*) and `CLAUDE.md`'s transcribed-proof caveat. Until the chapter
  exists, this note's checklist is the phase's to-do list.
