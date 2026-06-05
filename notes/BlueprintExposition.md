# Blueprint exposition ledger — hard nodes deserving a clearer-than-KT account

**Purpose.** One of the project's deliverables is a *clearer explanation of
Katoh–Tanigawa's proof than KT themselves give* for the genuinely difficult /
tricky arguments. The blueprint stays terse-by-default (carleson style, 1–3
sentence proofs — `blueprint/CLAUDE.md` *Proof verbosity*), but **crux nodes
earn full, followable exposition**. This file is the cross-phase *ledger* of
which nodes have earned that treatment and whether the exposition has landed.

It is a **capture-now / write-later** mechanism (agreed with the project owner,
2026-06-04):

- **Capture (cheap, while fresh).** When a node initially scoped as one commit
  turns out to be much harder and gets rerouted / reworked / decomposed, add a
  one-line entry here naming the *stable* mathematical insight the reroute
  surfaced — the case structure KT glossed, why a strengthening is forced,
  where the real difficulty sits. "Thought-one-commit → rerouted" is the
  primary trigger and is recoverable from git history for retroactive entries.
- **Write (at phase-close, once the argument is `sorry`-free).** The expanded
  blueprint prose lands in the phase-close end-to-end blueprint pass, *not*
  during the churny recon — the clean argument (and any simplification toward
  KT's own style) is only known once the result is final. That pass is
  broadened from "collapse formalization asides" to *also* "add the KT-glossed
  exposition for that phase's ledgered nodes."

**Out of scope** (these stay terse / excluded, per the existing rules):
Lean-*modelling* narration ("basis-free", "Layer 4b reshaped …") and
mathlib-standard background. The carve-out is for *mathematical difficulty*,
not Lean verbosity.

**Codification deferred.** The standing carve-out rule for `blueprint/CLAUDE.md`
*Proof verbosity* is intentionally **not** written yet — we derive the
principle by doing this a few times first (the format / criterion may sharpen,
and post-`sorry`-free simplification may change what the clean account is).
Revisit codification once 22a plus a retroactive node or two are done.

## Format

One entry per node, grouped by destination blueprint chapter:

> `label / Lean name` — [status] trigger; **stable insight to expose** — pointer

where `status ∈ {pending, done (<commit>)}`.

## Ledger

### `algebraic-induction.tex` — molecular algebraic induction (Phases 21 / 21b / 22a)

- **`lem:case-I-realization` (N6 composer)** — [pending] thought 1 commit →
  reconned into N6-G1/G2/G3 (2026-06-04). **Stable insight:** KT §6.2 Case I is
  a *trifurcation* (Lemmas 6.2 non-simple, 6.3 `G/E′`-simple, 6.5 degree-2
  vertex removal), not a uniform contraction recursion; and the realization
  motive must be *strengthened to general position* on the inductive legs (the
  composer's per-leg adapter consumes `HasGenericFullRankRealization`, while the
  induction threads only the bare motive). Pointer:
  `notes/Phase22-realization-design.md` §1.5–1.6; `notes/Phase22a.md`.
- **conditioned motive `Pc := (G.Simple → GP) ∧ bare` (`theorem_55_generic`;
  folds into `lem:case-I-realization` prose)** — [pending] G2a (`f35be5d`).
  **Stable insight:** the generic motive has to be *conditioned on simplicity*
  — KT's "nonparallel, if `G` is simple" (printed p.669); unconditional general
  position is *false* at the parallel-`K₂` base. Pointer:
  `notes/Phase22-realization-design.md` §1.6.
- **genericity device output is not GP (`lem:case-I-realization` /
  `lem:genericity-device` interface)** — [pending] N6-G1 spike (2026-06-04).
  **Stable insight:** the genericity device's output realization is *not* itself
  in general position (it lands at an arbitrary Gram-determinant non-root, not a
  moment-curve point) — so general position must come from the *seed*, it cannot
  be recovered from the device. Pointer: `DESIGN.md` *Constructibility recon …*;
  `notes/Phase22a.md`.
- **contraction simplicity `rigidContract_simple` / `map_simple` (G2b; folds into
  `lem:case-I-realization` prose)** — [pending] G2b built clean (2026-06-04).
  **Stable insight:** vertex-relabelling (`map`) is the *one* graph operation
  that breaks `Simple` — it can manufacture both loops (collapse an edge's
  endpoints) and parallel edges (collapse two edges onto one pair), so unlike
  `↾`/`＼`/`-`/induce it has no unconditional `Simple` instance. This is *why* KT
  Case I trifurcates: `G / E′` simple is a genuine *case hypothesis* (Lemma 6.3),
  and its failure is routed to Lemma 6.5's vertex-*removal* (which does preserve
  simplicity). The positive criterion `map_simple` (no-self-collapse +
  no-pair-collapse) is the faithful statement of that case input. Pointer:
  `notes/Phase22-realization-design.md` §1.6; `notes/Phase22a.md`.

### Retroactive (Phases 1–21b) — to be seeded from git history

- TODO (unscheduled): scan for historical "thought-one-commit → rerouted" nodes
  across earlier phases (candidates surface from `notes/PhaseN.md` reroute
  records + `git log`). Run as a cleanup-style round; the candidate list can be
  produced on demand. Phase 17's Lemma 2.1 and the Phase 5 blocker argument are
  likely early candidates.
