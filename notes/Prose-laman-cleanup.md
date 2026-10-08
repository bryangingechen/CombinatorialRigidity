# PROSE round 1/5 — `prose-laman`, Laman's theorem and the rigidity matroid (work log)

**Status:** in progress (opened 2026-10-07). Round 1 of **PROSE**'s five rounds; their plan, the
PI's decisions and the one planned stop are in `notes/Prose.md`, and `.claude/autopilot/queue.toml`
is the authority for which rounds are done. The round rewrites the prose of the twelve chapters
`sparsity.tex` → `executable.tex` to `40-exposition`'s register. Every `\label`, pin, `\leanok`,
`\uses` edge and statement strength stays as it is. What else the round notices goes to the ledger
`notes/Prose-findings.md`. 21 one-commit tasks, of which task 1 is this open.
**Next concrete task:** task 2, the dependency-audit script `scripts/blueprint-deps.py`
(`notes/Prose.md` §5), at Opus, with acceptance tests (a)–(c) (*Lemma checklist*). After task 3,
the sample, the round stops for the PI (Stop 1). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

Planned: **Stop 1** (`NEEDS_PI`), after task 3, the sample (`notes/Prose.md` §6). The coordinator
writes it here, newest entry first, with what task 3's line asks it to include; the PI answers in
an entry that starts `**PI, <date>:**`. Any unplanned `NEEDS_PI` entry goes here too. No entries
yet.

## Current state

**Round 1 is open** (task 1, this commit, docs only; the Lean tree and the blueprint TeX are
`6f4f7afa`'s, which are `64bb9754`'s). Nothing is mid-stream. The next concrete task is task 2,
the audit script.

**Verified at the open** (2026-10-07):
- Whole-project `lake build` green at `6f4f7afa`: 2996 jobs, all cached (the coordinator's run).
  This commit touches no Lean, so it was not re-run.
- `#print axioms` on all **19** `formalization.yaml` main results gives `[propext,
  Classical.choice, Quot.sound]`. The harness is `40-docs`' `scratch/40-docs/Axioms.lean` with one
  name updated, `pencil_conjecture` → `pencil_realization_theorem` (renamed at `64bb9754`), copied
  to `scratch/prose-laman/Axioms.lean` (gitignored). Its 19 names (in order) and 14 imports (as a
  set) were diffed against the yaml's `declaration:` and `file:` fields: identical. Run with `lake
  lean`, its output equals `40-docs`' close byte for byte apart from the harness's path and that
  renamed name. The one warning is the harness's own over-long line, as before.
- **The round's gate values.** Every slice must reproduce them:
  - `blueprint/lint.sh` green. `blueprint/verify.sh` green: `checkdecls` silent, and **9**
    `WARNING:` lines, all plasTeX package and renderer notices.
  - `blueprint/print/print.log`: **0** `LaTeX Warning` lines; **176** overfull boxes, counted at
    the open and close but not gated. (`latexmk` found the PDF up to date: no `.tex` is newer than
    the log, so it is HEAD's.)
  - The built graph: **657** nodes and **1 292** edges, fingerprint **`673e3178d1b3145e`**; pin
    hash **`b53eb8b1cf78cb06`** (`blueprint/lean_decls`: 1 030 pins, 1 020 distinct names). All
    of these were identical on a second `verify.sh` run. The commands are under *Scope*, gate 3.
- **`notes/Prose.md` §7, re-measured at HEAD** (§7 was taken at `64bb9754`, the same blueprint
  tree):
  - Rounds 1–4 cover 32 TeX files, 17 664 lines by `wc -l` (§7: 17 663) and 505 nodes. Round 1
    has 12 files, 5 011 lines, 153 nodes and 181 pins. Out of scope, as in §7: `pencil.tex`
    (1 186), `main-component.tex` (5 518), `retrospective.tex` (789) and `main.tex`. The whole
    blueprint has 657 statement environments, the graph's 657 nodes.
  - Nodes with four or more pins: as in §7, 19 in scope and 9 in `pencil.tex` and
    `main-component.tex`. Round 1's are `lem:edgesIn-corners` (4) and `pebble-game.tex`'s
    `def:pebble-counts` (5), `lem:pebble-game-invariants` (5) and `def:tryReachPebble` (4).
  - The register screen: §7's regex was not recorded, so this log records the round's (*Scope*,
    *The round's screens*). It is broader, and ranks the same seven chapters highest:
    `panel-layer` 63, `case-i` 31, `molecular-induction` 29, `case-iii` 24, `generic-lift` 18,
    `molecule-modelling` and `intro` 12 each. Round 1's chapters score 0–6.
- In the graph, 152 of round 1's 153 nodes are green and filled. `def:blockingWitness`
  (`pebble-game.tex`) is blue: it has no `\lean` and no `\leanok`.

## Scope and standing rules

From `notes/Prose.md` §2, restated only as far as a builder needs them.

- **Surface.** The twelve chapters, in `blueprint/src/chapter/main.tex` order: `sparsity`,
  `laman`, `henneberg`, `frameworks`, `henneberg-rigidity`, `trivial-motions`, `laman-theorem`,
  `rigidity-matroid`, `count-matroid`, `dfs`, `pebble-game`, `executable`. No other chapter's TeX.
  A docs edit that keeps a pointer into a rewritten chapter true is in scope (the chapter-model
  pointers to `sparsity.tex`; `notes/BlueprintExposition.md`'s Group-A pointers).
- **The hygiene rule.** The round does not change a headline statement or the strength of a
  blueprint statement. A finding that would need such a change becomes a ledger `S` entry and a
  line under *Candidates for the PI*. It is not acted on, and it is not a stop.
- **Prose only (rounds 1–4), and no Lean edits (all five rounds).** `CombinatorialRigidity/`,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` stay untouched; the close checks that
  their `git diff --stat` since the open is empty. Every node keeps its `\label`, its `\lean{…}` pins, its
  `\leanok` and its `\uses` edges. A statement block is edited for register and anchoring only. A
  node may move within its chapter to cure a forward reference (`blueprint/AUTHORING.md` principle
  E, *Node order*); a cross-chapter forward reference gets a `\cref` and a sentence instead. A graph
  or node-shape finding becomes a ledger `E` or `N` entry for round 5.
- **The register.** `blueprint/AUTHORING.md` principles A–F with their 2026-10-03 clauses;
  `40-exposition`'s exemplar `notes/Phase40-exposition-exemplar.md`; and, from task 4, this
  round's pinned sample `notes/Prose-exemplar.md`. Principle A's algorithmic carve-out applies in
  `dfs.tex`, `pebble-game.tex` and `executable.tex`.
- **Crux nodes.** No round-1 node has a *done* entry in `notes/BlueprintExposition.md`: Phase 28
  screened phases 1–16 out (*Retroactive coverage*, Group A). That verdict rests on full proofs of
  `thm:isTightOn-union-inter`, `thm:isTightOn-union-with-bonus`,
  `lem:isSparse-typeII-reverse-blocker`, `lem:isSparse-exists-nonadj-among-three-neighbors`,
  `thm:isSparse-exists-typeI-or-typeII-reverse` (with its preamble's map to Jordán's lemma numbers)
  and `lem:isSparse-of-rowIndependent-two`. Keep them full, and keep the ledger's pointers true.
- **Evidence.**
  - Citations meet `CLAUDE.md` *Referencing prior work*. `.refs/` has Jordán 2016, Lee–Streinu
    2008, Lee–Streinu–Theran, Whiteley 1996 and Tay–Whiteley 1985. It does not have Henneberg
    1911, Laman 1970, Lovász–Yemini 1982, Asimow–Roth 1978 or Jacobs–Hendrickson 1997: check
    those against the DOI landing page, or weaken the claim to "classical" or "see X" (`REFS.md`).
    The commit that relies on a passage names it.
  - Claims about the Lean come from declarations' statements and bodies, never from docstrings,
    and, from task 2 on, from the audit script's report for what a pin reaches.
- **Findings.** Each goes to `notes/Prose-findings.md` as one entry in its category (format and IDs
  in its header), and here as one line naming its ID: `S` and `M` under *Candidates for the PI*;
  `E`, `N`, `T` and `U` under *Moved to a later round* (round 5); `L` there too (a later Lean
  round). The ledger entry is the line's mirror (`CLEANUP.md` *Per-round work log*).
- **Gates for every slice**, each in the foreground with an explicit `timeout`:
  1. `blueprint/lint.sh` green.
  2. `blueprint/verify.sh` green: `checkdecls` silent, 9 `WARNING:` lines.
  3. **The invariance check**, run from the repository root after `verify.sh`. It must print
     `1292 edges 673e3178d1b3145e` and `b53eb8b1cf78cb06`:
     ```sh
     python3 -c "import re,hashlib;g=open('blueprint/web/dep_graph_document.html').read();g=g[g.find('digraph'):];g=g[g.find('{')+1:g.find('}')];s=sorted(filter(None,(re.sub(r'\s+',' ',x).strip() for x in g.split(';'))));print(sum(' -> ' in x for x in s),'edges',hashlib.sha256('\n'.join(s).encode()).hexdigest()[:16])"
     sort blueprint/lean_decls | shasum -a 256 | cut -c1-16
     ```
  4. `blueprint/print/print.log` has 0 `LaTeX Warning` lines.
  5. `python3 notes/check-phase-note.py` green; it gates this log by its title.

  Every commit also updates this log: its checklist line, *Current state* and *Hand-off*.
- **The round's screens** (not gates; the open's figures are in *Per-chapter diagnosis*, and the
  close re-runs them). Per chapter, with TeX comments stripped: principle-A register hits; then
  Lean-device hits inside statement blocks, and in the whole chapter. "Route" and "carries" are
  sometimes literal, and the device screen misses a subtype written as `G[\{w \ne v\}]`.
  ```sh
  python3 - blueprint/src/chapter/{sparsity,laman,henneberg,frameworks,henneberg-rigidity,trivial-motions,laman-theorem,rigidity-matroid,count-matroid,dfs,pebble-game,executable}.tex <<'PY'
  import re,sys
  E=r'(definition|lemma|theorem|corollary|proposition)'
  A=re.compile(r'\b(feeds?|drives?|fires?|firing|threads?|carr(?:y|ies|ied)|wired?|wiring|routes?|spine|heart of|crucial(?:ly)?|remarkabl[ey]|brick|motive|producer|strat(?:um|a)|honest|genuine|re-?aim|splice|leaf-most)\b',re.I)
  D=re.compile(r'\\texttt\{|\\mathtt\{|\\mathrm\{(?:none|some|Option|Sym2|Fin|List|SimpleGraph|fromEdgeSet|maxBlock|decide|span)\}|\\mathrm\{[^}]*(?:[a-z][A-Z]|\.|\\_)[^}]*\}')
  P=lambda s: re.sub(r'\\(lean|uses|label)\{[^}]*\}','',s)
  for f in sys.argv[1:]:
      t=re.sub(r'(?<!\\)%.*','',open(f).read()); B=re.findall(r'\\begin\{'+E+r'\}(.*?)\\end\{\1\}',t,re.S)
      print(f.split('/')[-1][:-4], len(A.findall(t)), sum(len(D.findall(P(b))) for _,b in B), len(D.findall(P(t))))
  PY
  ```

## Per-chapter diagnosis

Seen at the open; line numbers are the open's, and the labels are the stable reference. Each
slice re-derives its own findings and records them in its commit and the ledger.

| Chapter | Lines | Nodes | Pins | Register | Lean devices (statements / all) | Task |
|---|---|---|---|---|---|---|
| `sparsity` | 537 | 23 | 27 | 0 | 0 / 1 | 5.1, 5.2 |
| `laman` | 114 | 6 | 6 | 0 | 0 / 0 | 5.2 |
| `henneberg` | 372 | 12 | 12 | 1 | 32 / 86 | 3, 5.3 |
| `frameworks` | 415 | 19 | 19 | 1 | 7 / 20 | 5.4 |
| `henneberg-rigidity` | 247 | 5 | 5 | 0 | 11 / 72 | 5.5 |
| `trivial-motions` | 280 | 13 | 13 | 0 | 21 / 44 | 5.6 |
| `laman-theorem` | 477 | 13 | 13 | 0 | 11 / 39 | 5.7, 5.8 |
| `rigidity-matroid` | 696 | 18 | 18 | 1 | 17 / 95 | 5.9, 5.10 |
| `count-matroid` | 306 | 8 | 8 | 0 | 16 / 45 | 5.11 |
| `dfs` | 179 | 5 | 9 | 2 | 14 / 21 | 5.12 |
| `pebble-game` | 960 | 23 | 43 | 6 | 55 / 95 | 5.13–5.15 |
| `executable` | 428 | 8 | 8 | 4 | 43 / 130 | 5.16 |
| **total** | 5 011 | 153 | 181 | 15 | 227 / 648 | |

Phases 1–5 wrote the earliest of these chapters in backfill mode, and phases 6–11 kept their
style: the register is mostly flat, and the problem is Lean devices in statements and proofs.

- **`sparsity`** is the chapter model (`blueprint/CLAUDE.md`, `blueprint/DESIGN.md`;
  `AUTHORING.md` lines 104 and 142, whose quoted "Immediate from the definition." is
  `frameworks.tex`'s, not this chapter's). The register is already close; there is no roadmap,
  only two section openings, the second sending the reader to `sec:intro` for the Laman case. The
  last subsection's "bridge-augmented candidate `G[\{w \ne v\}] \cup \{\{x, y\}\}`" is a subtype
  standing for `G − v + xy`, and its proof works through "the inclusion of `G'`'s vertices".
  "Tight-blocker" and "per-pair" are coinages; Jordán's term is a *suitable* splitting. Line 59
  names `SimpleGraph.incidenceSet` in prose. `lem:edgesIn-corners` (4 pins) is principle D's
  corner-case grouping.
- **`laman`** is short and clean. Its opening and *The base case* send the reader to `sec:intro`
  for the Henneberg induction, which is in `laman-theorem.tex`. A statement writes the complete
  graph as `⊤`. *Degree bounds*' "(so we cannot reverse a Type~I move at a vertex of degree~1)"
  is muddled.
- **`henneberg`** has the most Lean-shaped statements of the round. Its opening fixes "the fresh
  vertex is `none : Option V`", and statements read `typeI G a b`, `Sym2.map some` and
  `(typeI G a b).IsLaman ⟺ G.IsLaman`. Henneberg's Type I and II moves are Jordán's 0- and
  1-extensions (Jordán 2016 p. 38, which glosses the first as "a Henneberg move of type I";
  Lemmas 1.2.2–1.2.3, and p. 44). The opening's "Henneberg's theorem characterises Laman graphs"
  needs a source check, since Henneberg 1911 predates Laman 1970. The reverse decomposition is
  stated with `G[\{w \ne v\}]` and rests on `rigidity-matroid.tex`'s sparse form, a later
  chapter.
- **`frameworks`**: statements name `Framework V d` and `RigidityMap G p`, and proofs cite mathlib
  lemma names. "Generically rigid" is defined as "some placement is infinitesimally rigid", and
  the injective form is a device the Henneberg induction needs; each wants a sentence where it is
  defined. *To check:* for `|V| ≤ d`, the bound `dim ker ≤ d(d+1)/2` is weaker than Asimow–Roth's
  infinitesimal rigidity. Read from `IsInfinitesimallyRigid`'s body, two unjoined vertices in
  `ℝ³` satisfy it (`6 ≤ 6`); at `d = 2` the two agree. If so: a formalization note, and an `S`
  entry.
- **`henneberg-rigidity`**: the idea, where to place the new vertex, is in the opening's bullets.
  Statements carry `Option V`, `none`, `some` and `typeI`.
  `thm:typeII-isGenericallyRigidInj-two-of-nonCollinear` uses `p_a, p_b, p_c` before it introduces
  `a, b, c`. The chapter cites nothing: Jordán's Lemmas 1.2.2–1.2.3 (p. 38) state the rank
  preservation, citing Whiteley 1996 Lemmas 11.1.1 and 11.1.7; check and attribute. "Strengthened
  decomposition" is stale.
- **`trivial-motions`** uses the Lean names as notation in its statements (`translationMotion t`,
  `infinitesimalRotation A p`, `trivialMotions p`, `elemSkewMap i j`), and its proofs cite mathlib
  names. The index-set formalization note may fail principle D's deletion test.
- **`laman-theorem`**: the ⇐ proof names `typeI_iso_of_two_neighbors`. The subsubsection *The
  rigidity rows as a family in the algebraic dual* is a Lean presentation, and the ⇒ proofs cite
  about ten mathlib names. "A classical Maxwell-type counting argument; see Jordán Lemma 1.3.1" is
  the attribution shape root `CLAUDE.md` warns about: check Jordán 1.3.1 and credit Maxwell's
  count. "Is not needed for the iff itself" is garbled (it is not needed for Laman's theorem).
- **`rigidity-matroid`**: the new vertex is `none : Option V` in the Type I lemmas and `\star`,
  with `V \sqcup \{\star\}`, in `lem:typeII-rowIndependent-lift`; one notation should hold
  chapter-wide. `lem:typeI-rowIndependent-lift`'s proof speaks of "one or two lines", both through
  `p'_a` or `p'_b` in direction `p'_b − p'_a`: they are one line. The opening's *Terminology*
  repeats `sparsity.tex`'s critical-set gloss, and `count-matroid.tex` gives it a third time. The
  subsection *Linear-matroid framing* puts `Matroid.ofFun`, `Function.extend` and `Subtype.val`
  in statements and proofs.
- **`count-matroid`**: statements use `fromEdgeSet I`, `\mathrm{Sym}_2 V` and `maxBlock X`. The
  *Terminology* paragraph answers a question not asked (Jordán's M-circuits). To check against
  `.refs/`: "introduced by Whiteley", "Whiteley's appendix", "Theorem 5(4)", and that outside
  `ℓ < 2k` "the bases need not have equal cardinality". `IndepMatroid.ofFinite` is named in prose.
- **`dfs`** (carve-out) is close already. `List V`, `some (w, p)`, `none`,
  `Relation.ReflTransGen` and `DirectedWalk.dropUntilBundle` appear in statements and proofs.
- **`pebble-game`** (carve-out) is the largest chapter and the most Lean-shaped. Statements carry
  `.inr D`, `.inl w`, `w.uv_1`, `runPebbleGameWith empty k ℓ …`, `WorkhorseWitness` and
  `PebbleGameResult`. Coinages: "computable core", "convenience form", "verdict-bearing". Bundled
  nodes: `def:pebble-counts` (5 pins), `lem:pebble-game-invariants` (5), `def:tryReachPebble` (4);
  and `def:blockingWitness` has no pin and no `\leanok`. `thm:pebble-game-soundness` assumes
  `ℓ < 2k`, which its pin `runPebbleGameWith_sound` does not take (read in the Lean; the proof
  says so in a parenthetical): an `S` entry, statement weaker than pin. Check the Lee–Streinu
  pointers (§§3–6, Theorem 8, Lemmas 10–15, Corollaries 11–12), Jacobs–Hendrickson 1997, and
  Lee–Streinu–Theran (the bib entry is CCCG 2005; `.refs/` holds a 2008 file).
- **`executable`** (carve-out) is about the Lean artefact itself (`#eval`, `decide`,
  `native_decide`, the `Decidable` instances, the CLI), so names stay as addresses. What goes:
  Lean as the subject of sentences, changelog ("was already factored", "no longer needed"), and
  Lean syntax in statement blocks (`(D.outNbhd v).sort (·≤·)`, `ofLex ∘ …`). Unverified claims:
  "sub-second wall time on a developer laptop", "polynomial time", and where `K₄` is rejected.

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
task at Opus, a fresh agent per task, except the close, which may run at Sonnet (§2).

- [x] **1. O — the open** (this commit; docs only): this log, the ledger skeleton, the baselines,
  the axioms check and the status surfaces.
- [ ] **2. A — the dependency-audit script** (`notes/Prose.md` §5). `scripts/blueprint-deps.py`,
  with a Lean metaprogram it runs through `lake lean`, never `lake env lean`; both committed.
  - *Inputs:* every `\label`, `\lean{…}`, `\leanok` and statement- and proof-level `\uses` in
    `blueprint/src/chapter/**.tex`; the main results of `formalization.yaml`.
  - *Lean side:* for each pinned declaration, the constants in its type and in its value, followed
    through unpinned project declarations (every `CombinatorialRigidity` module, the `Mathlib/`
    mirrors, private and auxiliary `match_`/`proof_` declarations included), stopping at pinned
    declarations and at constants from outside the project.
  - *Reports:* (1) per node, the nodes its pins reach through the type and through the value,
    against its `\uses`: missing edges, and unbacked edges (for a check, not defects); (2) pins
    outside the closure of every main result; (3) pins per node, four or more flagged; (4)
    `--dump`: the built graph's sorted edges, parsed as gate 3 parses them, and the label→pins map.
  - *Into the ledger:* the first report into `E` and `N`; into *Lean baselines*,
    `scripts/cleanup-smell-sweep.py`'s counts over the whole tree and the top 20 of `CLEANUP.md`
    §C's ranking.
  - *Acceptance tests*, in the script's own commit. **(a)** In a scratch copy of the TeX, remove
    `lem:deficiency-zero-connected` from the proof `\uses` of `thm:pencil-x0-theorem-s`
    (`40-exposition`'s `m6`, added by `40-simplify`): the script must report that edge missing.
    **(b)** `Graph.x0Attains_of_finrank_liftingSpace_eq_three`, the pin of `cor:pencil-flat-x0`,
    has no Lean caller: the script must place it outside every main result's closure. **(c)** The
    script's run time goes in this line.
  - *If still BLOCKED after one escalation:* salvage its route findings here, record it as not
    done, and go on to task 3; the slices read instead. Round 5's open retries it once.
- [ ] **3. S — the sample: `henneberg.tex`'s *Preservation of the Laman property*** (159–273, 115
  lines): `thm:typeI-isLaman`, `thm:typeII-isLaman`, `thm:typeI-reverse-isLaman`,
  `thm:typeI-isLaman-iff`, the lead-in, and the paragraph before the reverse direction. **Stop 1
  follows.**
  - *Diagnosis.* The statements are the Lean's: the extension is `typeI G a b`, a graph on `Option
    V`, and the equivalence reads `(typeI G a b).IsLaman ⟺ G.IsLaman`. The proofs count with
    `none`, `some` and `s ∩ some[V]`. The paragraph before the reverse direction explains it
    through `G[\{w \ne v\}]` and a theorem of a later chapter, where it should say in words what
    the reverse decomposition needs and where that is proved.
  - *Choices it makes, for the PI.* (i) How a Lean device in a statement is restated: the
    extension as a graph on `V` plus a new vertex, with the `Option` encoding left to a
    formalization note at `def:typeI` (task 5.3's). (ii) Henneberg's Type I and II against
    Jordán's 0- and 1-extension: keep one and gloss the other once, where the reader cannot miss
    it (task 5.3 writes it into the definitions). (iii) The depth of the sparsity case analysis,
    which stays the pinned Lean's argument.
  - *Must not change:* any `\label`, `\lean`, `\leanok` or `\uses` line; the statements' strength;
    the proofs' argument; the node order; anything outside the subsection. A fix needed elsewhere
    goes as one line into the task that owns it.
  - *Evidence bar:* the statements and bodies of `SimpleGraph.Henneberg.typeI_isLaman`,
    `typeII_isLaman`, `typeI_reverse_isLaman` and `typeI_isLaman_iff`. A citation for the
    preservation facts only once checked (Jordán 2016 §2.1, pp. 43–44; Tay–Whiteley 1985), and no
    new `\cite` key unless verified as `AUTHORING.md` *Citations* asks.
  - *Depth:* expect the subsection to change by 20–40 lines; much more is duplication.
  - *Record:* the sha, a two-line note of the choices, and the new line range. The coordinator's
    Stop-1 entry (`notes/Prose.md` §6) then holds the sample's commit and rendered text, these
    choices, how the algorithmic carve-out will read in tasks 5.12–5.16 (the sample cannot show
    it), any `AUTHORING.md` amendment it proposes, and the slice lists of rounds 1–4 with their
    granularity judgment.
- [ ] **4. E — pin the exemplar** (docs only; the commit after the PI's Stop-1 entry). Transcribe
  the PI's answer verbatim into *Decisions*; copy the approved sample, revised first if the PI
  asks, to `notes/Prose-exemplar.md`, frozen as `notes/Phase40-exposition-exemplar.md` is; land
  any `AUTHORING.md` amendment the PI makes; settle the slice list as the PI rules.
- [ ] **5. The slices**, one commit each, in `main.tex` order, each chapter's openings in its last
  slice (principle F). The diagnosis of each is its chapter's, above.
  - [ ] **5.1 `sparsity.tex`, first half**: §1's three subsections and §2's *Definitions*, *Basic
    properties* and *Low-degree* (11–142, 155–301); 15 nodes, 279 lines.
  - [ ] **5.2 `sparsity.tex`, second half and openings, and all of `laman.tex`**: sparsity's
    isomorphism transport, tight-subset lattice and per-pair blocker (302–537) with both section
    openings (1–10, 143–154), and `laman.tex` (114 lines); 14 nodes, 372 lines. It writes
    `sparsity.tex`'s roadmap and keeps the chapter-model pointers true (*Per-chapter diagnosis*).
  - [ ] **5.3 `henneberg.tex` apart from the sample**: definitions, edge-set counts, the reverse
    decomposition, the worked example and the opening (1–158, 274–372); 8 nodes, 257 lines. It
    carries the sample's notation and terminology into the definitions and the opening's
    convention paragraph.
  - [ ] **5.4 `frameworks.tex`**: 19 nodes, 415 lines.
  - [ ] **5.5 `henneberg-rigidity.tex`**: 5 nodes, 247 lines.
  - [ ] **5.6 `trivial-motions.tex`**: 13 nodes, 280 lines.
  - [ ] **5.7 `laman-theorem.tex`, first part**: the `d = 2` count, the ⇐ direction, and the ⇒
    direction from its preamble through the rank bounds (28–306); 9 nodes, 279 lines.
  - [ ] **5.8 `laman-theorem.tex`, second part and opening**: sparsity from row-independence, the
    assembly and Laman's theorem (307–477), and the opening (1–27); 4 nodes, 198 lines.
  - [ ] **5.9 `rigidity-matroid.tex`, first part**: the sparse reverse decomposition and the
    Henneberg lifts (37–386); 8 nodes, 350 lines.
  - [ ] **5.10 `rigidity-matroid.tex`, second part and opening**: the hard direction, the matroid
    and the linear framing (387–696), and the opening (1–36); 10 nodes, 346 lines.
  - [ ] **5.11 `count-matroid.tex`**: 8 nodes, 306 lines.
  - [ ] **5.12 `dfs.tex`** (carve-out): 5 nodes, 179 lines.
  - [ ] **5.13 `pebble-game.tex`, state, invariants and the basic algorithm** (carve-out; 61–410):
    10 nodes, 350 lines.
  - [ ] **5.14 `pebble-game.tex`, soundness and completeness** (411–783): 9 nodes, 373 lines.
  - [ ] **5.15 `pebble-game.tex`, correctness, verdict, corollary and opening** (784–960, 1–60):
    4 nodes, 237 lines.
  - [ ] **5.16 `executable.tex`** (carve-out): 8 nodes, 428 lines.
- [ ] **6. X — close the round** (`CLEANUP.md` *Workflow* 5; docs only).
  - *Gates:* whole-project `lake build` green; the no-Lean-edit check (`git diff --stat <open>.. --
    CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` empty). The axioms
    check runs next at round 5's close, not here (§2).
  - *The blueprint:* `lint.sh` and `verify.sh` green, the invariance values the open's, the
    warning counts unchanged, overfull boxes counted; the screens re-run beside the open's table.
  - *Findings:* every ledger entry the round found has its line here, and vice versa.
  - *The exposition ledger:* check `notes/BlueprintExposition.md`'s Group-A pointers against the
    new text, and add a round note.
  - *Status surfaces:* the ROADMAP row reads ✓ Complete; ROADMAP's PROSE bullet and
    `notes/Prose.md`'s **Status** name round 2's open.
  - *The queue:* `prose-laman`'s row in `.claude/autopilot/queue.toml` gets `done = true`, and
    nothing else there changes.

## Candidates for the PI

`S` and `M` findings, one line each naming the ledger ID (`notes/Prose-findings.md` holds the
finding). Recorded, never acted on in this round; round 5's report ranks them for the PI.

- None yet.

## Moved to a later round

`E`, `N`, `T` and `U` findings for round 5, `prose-graph`, and `L` findings for a later Lean round,
one line each naming the ledger ID and the task that found it.

- None yet.

## Blockers / open questions

- None blocking. The planned stop is Stop 1, after task 3 (*Autopilot: for the PI*). It asks the
  PI whether the sample's register, depth and choices (i)–(iii) are the round's, whether any
  `AUTHORING.md` amendment is wanted, and whether the slice lists hold.

## Hand-off / next phase

**Next concrete task: task 2, the dependency-audit script `scripts/blueprint-deps.py`, at Opus.**
Its spec and acceptance tests (a)–(c) are under *Lemma checklist*; `notes/Prose.md` §5 is the
plan. It writes the script's first report into the ledger's `E` and `N` sections and the Lean
baselines into its opening section. Then task 3, the sample, and Stop 1; no slice is written
before the PI's entry. Then task 4 pins the exemplar, tasks 5.1–5.16 follow in order, and task 6
closes the round.

## Decisions made during this round

- **2026-10-07, the open: the sample is `notes/Prose.md` §3's default**, `henneberg.tex`'s
  *Preservation of the Laman property*. It is typical of phases 1–6 (four nodes, Lean devices in
  every statement, case-analysis proofs) and poses this round's two new questions: how a Lean
  device in a statement is restated, and Henneberg's names against Jordán's. It cannot show the
  algorithmic carve-out, which the Stop-1 entry describes instead. Considered: `sparsity.tex`
  (already near the register), `frameworks.tex`'s definitions (few devices).
- **The slicing.** Slices of 150–430 lines (`40-exposition`'s range) cut at subsection
  boundaries; a chapter of at most 430 lines is one slice, and the openings go last. `sparsity`,
  `laman-theorem` and `rigidity-matroid` split in two, `pebble-game` in three. `laman.tex` (114)
  rides with `sparsity.tex`'s last slice, as the `(2, 3)` case of that chapter. That gives 16
  slices averaging 306 lines, above `40-exposition`'s 270: these chapters are less dense.
- **The screens** are recorded under *Scope*, since `notes/Prose.md` §7's regex was not.
