# blueprint/AUTHORING.md — prose & editorial conventions (read on demand)

The prose-writing and editorial half of the blueprint authoring conventions,
split out of `blueprint/CLAUDE.md` so that always-loaded manual stays focused
on every-touch forward-mode mechanics (the red/green node encoding, static
checks, builds, file layout). **Read this when writing or revising a blueprint
chapter** — adding nodes, prose proofs, citations, or deciding what merits an
entry. It is *not* auto-loaded (it is a plain reference like `RENDERING.md` /
`SETUP-AND-PITFALLS.md`); `blueprint/CLAUDE.md` *Authoring conventions* points
here.

For the node-annotation mechanics (`\lean{}` / `\leanok` / `\uses{}` order,
the sorry-blocked red-node convention) and the carleson-style baseline this all
follows, see `blueprint/CLAUDE.md` *Authoring conventions*.

## Authoring conventions (prose & editorial)

### Label prefixes

Use semantic prefixes consistently:
- `def:` for definitions
- `lem:` for lemmas
- `thm:` for theorems
- `cor:` for corollaries
- `prop:` for propositions
- `sec:` for sections

This makes `\Cref{}` output read naturally
("Definition 1.2", "Lemma 3.4") thanks to `cleveref`.

### Cross-references

Use `\cref{...}` / `\Cref{...}` (cleveref), never bare `\ref`. Both
`print.tex` and `web.tex` load cleveref with `capitalize`, so
`\Cref{lem:foo}` produces "Lemma 1.2" with the right capitalization.

### Citations

The blueprint loads a BibTeX bibliography from `src/bibliography.bib`
in both entry points (`print.tex`, `web.tex`) with the `amsalpha`
style. Cite published work with `\cite{key}`, combining multiple
citations with comma separation: `\cite{tayWhiteley1985,jordan2016}`.

Key convention: `firstAuthorYear` for single-author works
(`laman1970`), camelCased authors for multi-author works
(`tayWhiteley1985`, `graverServatiusServatius1993`). Match what's
already in `bibliography.bib`.

Top-level `CLAUDE.md → Referencing prior work` has the accuracy bar.
For the blueprint specifically:

- **Before adding a new bib entry**, verify title, authors,
  journal/series, volume, year, and page range against a primary
  source — DOI landing page, publisher metadata, or NASA ADS for
  older journals. Don't copy from second-hand citations without
  cross-checking.
- **Match attribution to who proved it.** When the modern
  presentation matters, name both: *"classical strategy of
  Tay--Whiteley 1985, in the modern presentation of Jord\'an 2016
  §2.2"* (`chapter/intro.tex` is the canonical example).
- **Verify any §N pointers** — §N must exist in the cited work and
  contain what you claim. Drop the section pointer rather than
  guess.

`leanblueprint pdf` (CI) and `inv bp` (local) drive `latexmk`, which
runs `bibtex` and produces `print/print.bbl`. `inv bp` also copies
that file to `src/web.bbl` so the subsequent `inv web` plastex run
renders the bibliography page and resolves in-prose `\cite{}`s. Both
formats use the same `amsalpha` style, so labels like `[TW85]`,
`[Jor16]` are stable across formats.

### What to include vs. skip

**Be selective.** The blueprint is a reader's doc for a human
audience, not a 1:1 mirror of the Lean. A typical Lean file has
many small declarations that don't merit a blueprint entry. The
default presumption is *exclude*; only include declarations that
clear one of the bars below.

- **Include**:
  - Definitions of project-level concepts (`IsSparse`, `IsLaman`,
    `IsTight`, `IsTightOn`, etc.).
  - Theorems that a reader would name out loud
    (e.g. "Laman's theorem", "tight-subset union closure").
  - Lemmas with non-trivial mathematical content used at a phase
    boundary or feeding a main theorem.
- **Skip**:
  - Pure tautologies that follow immediately from a definition
    (e.g. `edgesIn_subset_edgeSet` is just `A ∩ B ⊆ A`).
  - Constructors / accessors whose only job is to absorb
    `Sym2`-membership or And-projection boilerplate
    (e.g. `mk_mem_edgesIn`, `IsLaman.isSparse`,
    `IsLaman.edgeSet_ncard`). The fact they prove is already legible
    from the type signature.
  - Mirror lemmas under `CombinatorialRigidity/Mathlib/` — these are
    upstream-eligible facts about `Sym2`, `Set.ncard`, etc., not
    project results. They belong upstream, not in the blueprint.
  - Small bridge / glue lemmas whose names or statements are likely
    to change as the API stabilizes. These are also the highest-
    churn artefacts, and blueprinting them means re-editing the
    blueprint on every Lean refactor.
- **Group**: closely related corner cases under one `\begin{lemma}`
  with multiple comma-separated names in `\lean{...}` (see
  `lem:edgesIn-corners` in `sparsity.tex`).
- **Phase-N-prep lemmas that live in Phase-M files** still belong
  in the chapter for **file M**, not phase N. The blueprint reader
  cares about the formal landscape (which file holds what), not
  about which agent-session added a given lemma.

Heuristic that captures most of the above: *if the lemma's name or
statement is likely to change as the API stabilizes, that's a sign
it's churn-prone internal infrastructure — skip it.* See
`blueprint/DESIGN.md` for the rationale.

#### Narrative-bridge corollaries (the `@[deprecated]` shim pattern)

A hybrid between *Include* and *Skip*: a corollary worth naming as a
consequence for the project's central object (e.g. a Laman-specialised
form of a sparse-level theorem) but whose Lean version is a one-line
composition with **no downstream caller**. Prose-only invites silent
drift; a normal lemma proliferates API that competes with the general
form. The pattern: keep it a full `\begin{corollary}` with `\lean{}` +
`\leanok`, and formalize the Lean shim under `@[deprecated <general-form>
(since := "narrative-bridge")]` with the intent in its doc-comment — the
build still checks the prose (a rename breaks the shim body), the warning
discourages callsites, the dep-graph greens. (Why the non-date `since`
sentinel: `CombinatorialRigidity/CLAUDE.md` *Engineering conventions*.)
Canonical example: `cor:isLaman-exists-rowIndependent` ↔
`SimpleGraph.IsLaman.exists_rowIndependent_placement`
(`MatroidIdentification.lean`).

**Only when the Lean has zero expected callers.** Most specialized
lemmas (`IsLaman.iso`, `IsGenericallyRigid.card_mul_le_two`, …) are real
API with callers — formalize them eagerly, no `@[deprecated]`. If you
want `@[deprecated]` on a lemma that *has* callers, either refactor them
onto the general form or drop the marker (it's genuine API).

### Proof verbosity

Match the carleson style: one to three sentences of English gesturing
at the argument; a reader wanting the full proof clicks to the Lean.
(Models in `sparsity.tex`: "Immediate from the definition." up to the
~10-line `thm:isTightOn-union-inter`.)

**First make Lean as painless as the math; only then add prose asides.**
When a step is harder to formalize than to state, fix the *Lean* first
(better strategy, an upstreamable helper, sharper automation); only if
that fails add a brief aside naming the residual gap. "The Lean is just
verbose" is a smell — friction we accept in the blueprint the next phase
pays for.

**Be honest about formalization cost, both ways.**
- *Omit* (Lean noise invisible to the math): `omega`/`grind`/`simp`
  closes, typeclass elaboration, mathlib glue.
- *Note* (a one-line math step that grew real Lean infrastructure): a
  hand-rolled `Equiv` for a "canonical" move, a named helper standing in
  for a one-step correspondence, a case-split the math wouldn't take —
  one clause, so the prose is a faithful map, not a polished fiction.
- *Don't over-note* (the basis-free anti-pattern): prose narrating *how
  the formalization models* an object ("basis-free, deferring
  coordinatization", "abstract graded piece rather than a basis") is
  changelog, not math. One clause max, and only when the modelling choice
  is load-bearing for a later node; else cut it (it belongs in the Lean
  doc-comment). Phase 18's §2.2–2.4 accreted four such asides — don't
  reintroduce them.

**Cut comparisons with the project's own informal argument** (the PI, 2026-10-03,
at round 3 of the post-Phase-40 cleanup round). A proof never compares itself
with the project's own prior informal argument — a workbook, a design note, an
earlier draft — which the reader has not read and should not need to. A reason
the proof is shaped as it is stays, stated on its own, not as a comparison. So
does an argument that gives more insight but was not formalized: "In cases
where the informal argument might give more insight but we decided not to
formalize it due to technical reasons, it could be worth mentioning as well"
(the PI) — as a short remark or formalization note, naming that reason. A
stronger fact the proof does not need is cut unless a reader would expect it;
then one sentence says the proof needs only the weaker form.

**The carve-out: crux nodes earn full, detailed exposition.**
Terse-by-default is the rule above; the exception is the project's
deliverable of a *fully detailed, self-contained exposition* of
Katoh–Tanigawa's hardest arguments — spelling out the steps the paper
reasonably compresses, so each crux is followable without the authors'
context (a complement to KT's research exposition, not a verdict on it). A
genuinely hard node earns a full, followable prose proof — and which nodes
have earned it (and whether the prose has landed) is tracked in the
cross-phase ledger `../notes/BlueprintExposition.md`.
**Capture-now / write-later:** during a phase, add a one-line ledger entry
whenever a node reroutes/decomposes and surfaces a stable mathematical
insight (the case structure KT states compactly, why a strengthening is forced);
**write** the expanded exposition at phase-close (the broadened blueprint
re-read — top-level `CLAUDE.md` *When this commit closes a phase*), once the
argument is `sorry`-free. The carve-out is for *mathematical* difficulty
about **KT's math**, not our formalization setup — a reroute caused by a
project-side mistake does not earn an entry (the ledger's own header has
the sharpened inclusion criterion + the `(a)/(b)/(c)` flavors).

### Audience & vocabulary

The molecular-conjecture chapters (Phases 17–26) target a specific
reader: **a mathematician working in rigidity theory who knows
Katoh–Tanigawa 2011 but has not carefully studied its proof.** The
audience test for any word or phrase in prose is: *would a rigidity
theorist who has read KT know this term?* If the answer is no — because
it names a Lean identifier, a phase number, a sub-phase code, or a
dependency-graph status rather than a mathematical object — it does not
belong in reader-facing prose. (Adopted at the post-Phase-23 cleanup
round after a survey found process vocabulary throughout the molecular
chapters, including inside headline theorem statements; see
`../notes/Phase23-cleanup.md`.)

**Six principles** govern the prose — when writing new text and when
revising existing text alike; each carries one mechanical test.

**A. Vocabulary & register.** Match the flat, even prose of a published
paper, with Katoh–Tanigawa 2011 as the exemplar (read a few pages under
`.refs/` before revising a chapter). No significance-pointing ("the
heart of", "crucially", "remarkably"), rationed em-dash asides, and no
mechanism metaphors ("feeds", "drives", "fires", "threads", "carries") —
use plain mathematical verbs. Hypothesis names never appear in prose;
declaration names only parenthetically at step boundaries, as addresses.
*Test:* a working mathematician could have written the paragraph, every
sentence still mathematics with its parentheticals deleted.
*Voice and sentences* (the PI, 2026-10-03, at round 3 of the post-Phase-40
cleanup). "Flat" means no hype, not impersonal. Write as KT do: "we" and
"let us" are fine ("we shall construct", "let us first sketch the proof").
An abstract subject standing in for the author ("the proof reaches", "the
step assumes", "call this") is a tell. One idea per sentence: split a
sentence with more than one subordinate clause or more than one
parenthetical `\cref`, and give every "this" or "it" a referent in the
sentence before. Do not answer a question the reader has not asked: a
negative remark ("X is not needed", "the hypothesis enters only here")
stays only where a reader would expect X.
*Algorithmic-chapter carve-out* (the DFS / pebble-game / executable
chapters — Phase 28 calibration): a step that terminates, visits, marks,
returns, accepts, or searches is plain computational English and **stays**
— only mechanism *metaphors* dressing up a mathematical relation are
rewritten. A Lean tactic (`native_decide`/`decide`) is named as a
parenthetical address, never a prose subject that "fires". A
domain-standard move name (the pebble-game / chip-firing "fire") stays
only when it names the algorithm's actual orientation step; the pebble
game's steps are "insert an arc"/"reverse a path", so every "fires" there
was decorative and rewritten.

**B. Statements.** A statement is the mathematical claim at KT's
strength, modeled on KT's shape — *"Let [setup]. (Suppose […].) Then
[claim]."* — one to four sentences, extendable only by a notation gloss
("where $D = \binom{d+1}{2}$") or a further-mathematical "i.e."/"in
particular" restatement; a definition introduces its object and ends.
Everything else moves out: term expansions, vacuity/essentiality
discussion, methodological asides, role/positioning clauses, and
comparisons to a remark or connective prose; construction and proof
material to the proof; Lean identifiers to the Formalization note; a
definition's consequences, existence constructions, and model
comparisons to surrounding prose. Attribution stays — a title bracket or
one plain sentence, never a role clause. *Tests:* (i) *deletion* — cut
every sentence that is not hypothesis, claim, or gloss; if the
obligation is unchanged it belonged outside; (ii) *standalone* — read as
if no other node existed (the failure tell: a trailing "This is …").

**C. Proofs.** A proof is a mathematical narrative in KT's vocabulary,
with `\cref`s as parenthetical anchors, never grammatical subjects; an
existing narrative block (a case dichotomy, a chain dispatch, a
construction account) becomes the backbone, not a parallel essay beside
a dep-graph-traversal proof. Break a proof over ~8 source lines into
paragraphs by argument movement. A specialization proves itself in one
sentence ("Specialize \cref{…} to $n = 3$"); two Lean proofs that
duplicate each other are a statement-surface item to collapse in Lean,
never a license to duplicate prose. *Test:* every step with a sentence
`\cref`s a node or names its Lean declaration inline, so the prose
indexes every load-bearing declaration (helpers stay unpinned). The test
is for proofs, where the index is what links the prose to the Lean. An
overview or a preamble cites only what the reader needs to find, not
every sentence's source.

**D. Formalization notes & pins.** Lean-encoding detail goes in a
*Formalization note* — the `fmlnote` environment (`\begin{fmlnote} …
\end{fmlnote}`, shares the theorem counter so it renders "Formalization note
N.M" and is `\cref`-able; defined in `preamble/common.tex`, `\crefname` in
`web.tex`/`print.tex`) — placed outside every other environment (after
the proof, or after a definition), never in the statement block — at
most one per node, only where the Lean diverges, in mathematical
English, not Lean syntax (no `\mathtt{}` formulas, no audit codes,
understandable to a reader who cannot read Lean); a bare "Formalized as
X" note is deleted, as the pin already links. Pin what the reader should
open, not the full API: one decl per node ideally, two or three with a
role-labeled one-clause-per-decl map at most; four or more means the
node bundles results — split them or leave helpers unpinned. A recurring
encoding artifact is explained once, in one labeled remark listing its
carrying nodes and `\cref`'d elsewhere — the canonical case being the
fresh-edge-label supply (an ambient label-type artifact with no analogue
in KT, satisfied by any large-enough label type; `\cref` its
satisfiability lemma and witness). *Test:* delete the note; if the pin
links already gave it all, it stays deleted.

**E. Fidelity & anchoring.** Never re-group the source's case structure
or labels: each case KT states separately gets its own node, `\cref`,
and `\uses` edges, and titles are a KT anchor plus a short mathematical
description with no internal codes. Cite the induction principle the
proof actually runs on (not a $k = 0$-only reduction where the all-$k$
skeleton drives it), and give every KT-numbered result or equation the
"KT" prefix ("KT Theorem 4.9", "KT eq. (6.1)") in titles, statements,
and proofs. *Test (both directions of every reference):* reading
forward, a definition or statement shows every conjunct and
constituent datum that later prose names, adjusts, or discusses;
reading backward, every term of art, named object, or hypothesis a
sentence leans on resolves to a definition, gloss, or `\cref` already
visible to the reader — a term used before (or without) its
introduction fails even if a correct definition exists elsewhere in
the corpus. (Failure tells: an unanchored "This is …"; an italicized
term whose first occurrence is not its introduction.)
*Node order* (the PI, 2026-10-03). A node may move within its chapter to cure
a forward reference the backward test catches — the fix is reordering, not
re-grouping: case structure, titles, and `\uses` edges carry over unchanged.
*Terminology* (the PI, 2026-10-03). Be skeptical of nonstandard terms.
Prefer the source's term or the textbook's. Keep a project coinage only
when no standard term exists, and then define it where the reader cannot
miss it: a definition node, or the chapter's notation paragraph, not a
parenthetical or a lead-in. A Lean-side device with no mathematical
content (an endpoint selector, say) stays out of statements.

**F. Chapter flow.** A chapter opens with a half-page mathematical
roadmap — what is proved, in what order, what the reader needs — with no
phase numbers, dep-graph/forward-mode status, or standalone *Status.*
paragraph. Each subsection opens with a short orienting paragraph and
load-bearing definitions get a lead-in sentence, so the chapter reads as
an article with embedded statements, not a list of environments; the
dep-graph color convention is explained once in `chapter/intro.tex` and
never re-explained in a preamble. *Test:* the preamble names what is
proved and in what order without a single phase number or dep-graph
term. *Once* (the PI, 2026-10-03). The orienting paragraph sketches the
argument once, at overview depth. A lead-in before a node says only what
the opening did not, such as why the node is stated in this generality;
it never restates the node. No overview before a theorem repeats its
proof's paragraphs.

**Revising an existing chapter (the R-task sweep order).** Statements
first (B): run the deletion and standalone tests on every environment
and move what fails. Then the anchor sweep (E, reading backward): for
every term of art, named construction, or symbol that a proof, note,
or connective sentence uses, confirm the reader has already met its
introduction — check that each `\emph{}`-introduced term's first
occurrence is its definition, and `\cref` terms imported from other
chapters at first use. Then proofs (C), then notes and pins (D), then
the vocabulary and register greps (A), and the preamble and connective
prose last (F), once the content around them is stable. The forward
fidelity checks of E — case structure, KT prefixes, citing the
induction principle actually used — ride with the statement and proof
passes.

*Process footer — all existing gates hold:* restated statements match
the pinned Lean's strength (honesty + definition-faithfulness gates,
`blueprint/CLAUDE.md`); `\uses` edges are preserved unless a node
split/merge reshapes them; `verify.sh` + `lint.sh` stay green per
commit.

These six principles (A–F) replace the seventeen numbered *Target style*
rules that preceded them (calibration v1–v4, in git history); a "rule N"
reference in an older note or commit resolves there.

**Terminology dictionary** (settled at the post-Phase-23 cleanup round;
extend it rather than inventing a parallel list):

| project term | replacement in reader-facing prose |
|---|---|
| brick | rank-addition lemma / rank bound (KT §6.1 language) |
| motive | induction statement / realization predicate (define once if kept at all) |
| producer | realization lemma / existence lemma |
| stratum, strata | drop (or "stage") |
| carry / adjudicated carry | rewritten away (a deferred hypothesis, named mathematically) |
| the `hub` bound | the motion-space lower bound + `\cref` to its lemma |
| arm / fire / route / spine / wire | plain mathematical prose |
| threads / feeds / carries (as a verb) | mechanism metaphor (principle A); the ban applies inside Formalization notes as well as prose |
| honest form / honesty (of a statement) | epistemic process vocabulary — name the math ("the rank form", "the form KT actually uses"); the *honesty gate* keeps its name in the manuals, never in chapter prose |
| genuine (hinge, realization) | nondegenerate — nondegeneracy is definitional in KT's body-hinge framework, and "genuine" appears nowhere in KT |
| re-aim, and other Lean-verb coinages (`reaim`, `splice`, …) | describe the operation mathematically; the Lean helper name parenthetically at most (principle A) |
| parallel | edges: only the multigraph sense (two edges on one vertex pair). KT's panel term is "nonparallel" (KT §5.1) — gloss at first use. Extensors: "linearly independent", never "parallel" |
| green / red / leaf-most / live to-do list | only in `intro.tex`'s one dep-graph note |
| Lean hypothesis names (e.g. `h622`, `hsplit`, `hsplitGP`, `hcontract`, `hcSimple`, `hgen`, `hcut`, `hD`, `h65`, `M4`) | never in prose (principle A) |

Lean file/section names (e.g. `Bricks.lean`) are invisible to blueprint
readers and are unaffected by this table.

## The retrospective appendix (Phase 29 exception)

*(Moved from `blueprint/CLAUDE.md` on 2026-10-05; it matters only when editing
`chapter/retrospective.tex`.)*

`chapter/retrospective.tex` ("Notes on the formalization") is a **deliberate,
conscious exception** to two standing conventions at once: the top-level
`CLAUDE.md` rule that process/route-history is deleted from live documents
(left to git + `notes/FRICTION.md` `[process]` entries + `DESIGN.md`), and
`AUTHORING.md` principle A's ban on Lean identifiers as prose subjects. Its
subject *is* the formalization's own wrong turns
(`../notes/FormalizationRetrospective.md` carries the taxonomy-ordered outline
and the raw-material inventory; work log `../notes/Phase29.md`), so both
exceptions are load-bearing rather than accidental drift, and are confined to
this one file.

**Structural placement.** One appendix chapter, wired in via `\appendix`
(a plain `article`/`amsart` command — plastex's `Packages/article.py`
implements it correctly, resetting the section counter and switching
`\thesection` to `A`, `B`, …; no fallback was needed) in `chapter/main.tex`
after the last math chapter, so it never sits in the proof's reading path.
One `\subsection` per failure-mode class (the outline's (ii)–(vi)), episodes
within a class as `\subsubsection`s.

**Register carve-out.** Otherwise the appendix follows the same flat,
published-paper register as the rest of the blueprint (`AUTHORING.md`
principle A: no significance-pointing, no verdict language, no mechanism
metaphors) — the difference is scope, not tone: Lean declarations, types,
and short code excerpts are first-class objects here, appearing directly in
prose and in displayed code blocks, rather than only as parenthetical
addresses. Two mechanics this requires:

- **Displayed Lean excerpts use `\begin{alltt}...\end{alltt}`** (LaTeX's
  standard `alltt` package, loaded in `preamble/common.tex` for both
  builds; plastex has its own Python implementation + an HTML5 template,
  no fallback needed). **Gotcha:** `alltt` gives `$`, `#`, `%`, `_`, etc.
  *catcode 12* (literal, like real verbatim) — only `\`, `{`, `}` keep
  their normal meaning — so a Lean snippet's Unicode (`ℕ`, `∃`, `∧`, `→`,
  …) cannot be typed as raw Unicode (this project's existing convention
  anyway: no chapter uses raw Unicode math symbols, always LaTeX macros)
  nor switched to math with bare `$...$`. Use `\(...\)` for each symbol
  instead (a control sequence, so it survives `alltt`'s catcode change);
  `$...$` remains the convention everywhere *outside* an `alltt` block.
  Keep source lines short enough not to overflow the print build's text
  width — `alltt` does not wrap; break at a Lean connective with an
  indented continuation if a line runs long, the same as ordinary
  code-formatting judgment.
- **A Lean identifier with a Unicode subscript (`C₁`, `h₂`, …) needs
  `\(\sb{1}\)`, not `\(_1\)`.** `\(...\)` rescues *control-sequence*
  symbols (`\to`, `\wedge`, `\neq`, …) because a control sequence's name
  is read under letter catcodes, which `alltt` does not touch — but `_`
  itself is one of the characters `alltt` recatcodes to 12 (literal), and
  catcodes are fixed at tokenization time, before `\(`/`\)` ever run,
  so `_` stays a plain "other" character even inside `\(...\)`. Writing
  `C\(_1\)` therefore typesets a literal underscore-and-digit, not a
  subscript (caught by rendering the print PDF at 300dpi and inspecting
  the page — `pdftotext` alone won't show the difference, since it
  extracts the character stream, not the glyph position). The primitive
  subscript/superscript control sequences `\sb{...}`/`\sp{...}` (plain
  TeX names for `_`/`^`) are, like `\to`, read by name and so survive
  the catcode change: `C\(\sb{1}\)` renders a true subscript.
- **`div.alltt` needed an explicit CSS rule** (`extra_styles.css`): the
  theme styles `pre`/`pre.verbatim` for whitespace and monospace, but has
  no rule for plastex's `<div class="alltt">`, so without one a browser
  collapses the code block's newlines and indentation like ordinary text.
- **A long `\texttt{...}` Lean identifier in running prose (not an `alltt`
  block) can overflow the print build's right margin** (Phase 29 W3-1,
  caught by the 300dpi print-PDF inspection, not by `pdftotext` or the web
  build — a browser wraps plain text more forgivingly than xelatex's
  paragraph breaker): a `\texttt{}` group with no interword glue (an
  identifier's `\_`-escaped underscores don't count) has no legal TeX
  line-break point, so one long identifier — or several packed onto one
  line, as this appendix's register invites — can produce an unbroken run
  wider than the text width. Fix: insert `\allowbreak{}` after selected
  `\_`s inside the identifier
  (`exists\_\allowbreak{}shared\_\allowbreak{}redundancy...`), a
  zero-penalty break point with no visible hyphen (unlike `\-`). Apply
  only to an identifier that actually overflows at build time, not as a
  blanket rule on every long `\texttt{}`.
- **Commit links** via
  `\href{https://github.com/bryangingechen/CombinatorialRigidity/commit/<sha>}{\texttt{<short-sha>}}`,
  full-length SHA in the URL (GitHub also accepts an abbreviated prefix,
  but the full form never risks an ambiguous/rotting short prefix), short
  8-character form in the visible link text. Post-lift commits only (the
  2026-05-13 move to a standalone repository rewrote earlier history).

**Vocabulary gate exemption.** `lint.sh`'s checks 5a (banned words:
brick/motive/producer(s)/stratum/strata/green-modulo) and 5b (phase
self-description) both exempt `chapter/retrospective.tex` outright, the
same style as `intro.tex`'s existing 5b-only exemption — see the checks'
own header comments in `lint.sh` for the mechanics. This is not a loophole:
the whole point of the register carve-out above is that this vocabulary is
the appendix's mathematical content, not process leakage into the rest of
the blueprint's reader-facing prose (which the gate still polices
normally).
