# PROSE round 1/5 — `prose-laman`, Laman's theorem and the rigidity matroid (work log)

**Status:** in progress (opened 2026-10-07). Round 1 of **PROSE**'s five rounds; their plan, the
PI's decisions and the one planned stop are in `notes/Prose.md`, and `.claude/autopilot/queue.toml`
is the authority for which rounds are done. The round rewrites the prose of the twelve chapters
`sparsity.tex` → `executable.tex` to `40-exposition`'s register. Every `\label`, pin, `\leanok`,
`\uses` edge and statement strength stays as it is. What else the round notices goes to the ledger
`notes/Prose-findings.md`. 21 one-commit tasks; tasks 1–4 and 5.1–5.14 are done: the open, the
dependency-audit script `scripts/blueprint-deps.py`, the sample, its pinning as the exemplar
`notes/Prose-exemplar.md` after the PI approved it at Stop 1 (2026-10-07, *Autopilot: for the
PI*), and the first fourteen slices, `sparsity.tex` through `pebble-game.tex`'s soundness and
completeness. **Next concrete task:** task 5.15, the rest of `pebble-game.tex` and its opening.
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

Newest entry first. The PI answers in an entry that starts `**PI, <date>:**`. Stop 1 is the
round's one planned stop; any unplanned `NEEDS_PI` entry goes here too.

### 2026-10-07 — `NEEDS_PI`: Stop 1, the sample section (planned stop, `notes/Prose.md` §6)

**The question, in short** (answered below; its full text, with the coordinator's checks of the
sample, is this log at `05100074`). Task 3 (`67525c41`) rewrote `henneberg.tex`'s *Preservation of
the Laman property*: its four theorems state the moves as constructions in words ("Let $G'$ be
obtained from $G$ by the Type~I move at $a$ and $b$."), and the proofs follow the Lean's case
split. The PI was asked about: **1**, the sample's register, depth and evidence bar, to be pinned
for rounds 1–4; **2**, its three choices: (i) a Lean device in a statement restated as the
construction in words, with new vertex $v$; (ii) Henneberg's Type~I/II kept, Jordán's
0-/1-extension named once; (iii) the Lean's case split kept; **3**, four calls the builder flagged:
(a) edges written $ab$; (b) $G - v$ and $G - v + ab$ where the reverse decomposition and two later
chapters write $G'$ for the smaller graph; (c) "These facts are classical", which names no
originator; (d) `thm:typeI-isLaman-iff`, which only combines the two theorems before it; **4**, the
principle-B amendment for `AUTHORING.md`; **5**, how the algorithmic carve-out reads in tasks
5.12–5.16; **6**, the slice lists of rounds 1–4. Options: A, approve as is; B, approve with
revisions; C, revise and show again; D, regroup the slices.

**PI, 2026-10-07:** (transcribed verbatim from the attended session that reviewed the sample)
- On 1 and 2: "1-2 these look good."
- On 3: "edge notation, the graph G' names is not a big deal as long as it's understandable; I'm
  more concerned about the classical attribution: could we omit it or find something to back that
  up? The iff node also seems natural."
- On 4: "The amendment looks good."
- On 5: "I think this is reasonable; more than following rules strictly though, the overriding goal
  is to make sure the result is understandable. Perhaps the coordinator should pay careful
  attention to the first few Sonnet dispatches to ensure that the guidelines are working."
- On 6: "Looks good to me."

*The attended session's notes* (not the PI's words). **3c:** Jordán credits no one for Lemmas
2.1.4(a) and 2.1.5; both "follow easily" from his count (pp. 44–45). Nixon–Ross (`.refs/`, arXiv
1203.6623v2, Theorem 2.5) credit the characterization they are the easy half of to Henneberg and
Laman, neither of which is in `.refs/`. So option B: at the PI's request this entry's commit drops
"These facts are classical." from the sample (now 159–259); for task 5.3, the opening (line 4)
credits Henneberg alone. **5:** every slice runs at Opus (`notes/Prose.md` §2), so "the first few
Sonnet dispatches" is read as the first few slices; *Hand-off* carries the check.

## Current state

**The fourteenth slice has landed** (task 5.14, this commit): `pebble-game.tex`'s *Soundness* and
*Completeness*, now 540–893. Tasks 5.1–5.13 rewrote `sparsity.tex` through `pebble-game.tex`'s
first part. Nothing is mid-stream; task 5.15 is next.
- **Gates at this commit**, all the open's values: `lint.sh` green; `verify.sh` green, with
  `checkdecls` silent and 9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e`
  and `b53eb8b1cf78cb06`; `print.log` 0 `LaTeX Warning` lines (129 overfull boxes, none in
  540–893; 131 at `db7ff7d6`). The screens on 540–893 read 0 and 2 / 10, every device hit
  `\mathrm{span}`, Lee–Streinu's own notation (0 and 12 / 27 on the same text at the parent).
- **For the slices:** `python3 scripts/blueprint-deps.py --label <label>` prints what a node's pins
  reach, each with its chain of constants, against its `\uses`; `--chapter <name>` does a chapter.
  The first run after a Lean or pin change takes about two minutes, and later runs read the cache.

**The round's gate values**, which every slice must reproduce (verified at the open, 2026-10-07,
with the whole-project `lake build` and the axioms of the 19 main results; detail in the log at
`bca00d3f`):
- `blueprint/lint.sh` green. `blueprint/verify.sh` green: `checkdecls` silent, and **9**
  `WARNING:` lines, all plasTeX package and renderer notices.
- `blueprint/print/print.log`: **0** `LaTeX Warning` lines; overfull boxes counted, not gated (176
  at the open).
- The built graph: **657** nodes and **1 292** edges, fingerprint **`673e3178d1b3145e`**; pin hash
  **`b53eb8b1cf78cb06`** (`blueprint/lean_decls`: 1 030 pins, 1 020 distinct names). The commands
  are under *Scope*, gate 3.

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
- **The register.** `blueprint/AUTHORING.md` principles A–F with their 2026-10-03 clauses, the
  2026-10-07 *Constructions* clause of B, and the PI's sentence before them ("the overriding goal
  is to make sure the result is understandable"); `40-exposition`'s exemplar
  `notes/Phase40-exposition-exemplar.md`; and this round's pinned sample `notes/Prose-exemplar.md`.
  Principle A's algorithmic carve-out applies in `dfs.tex`, `pebble-game.tex` and `executable.tex`
  (*Decisions*: the carve-out in tasks 5.12–5.16).
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

- **Done chapters.** The open's bullets for `sparsity` through `dfs` were consumed by tasks
  5.1–5.12; they are in this log at `e5dd8256`, and each task's findings are in its commit and the
  ledger.
- **`pebble-game`** (carve-out) is the largest chapter and the most Lean-shaped. Tasks 5.13 and
  5.14 rewrote 61–893. Left for 5.15 (895–1071 and 1–60): `.inr D`, `.inl w`, `w.V'`,
  `runPebbleGameWith empty k ℓ …`, `WorkhorseWitness`, `PebbleGameResult` and its constructors,
  `runPebbleGameExec` and `countMatroid` in statements; a Lean name in a proof; and the coinages
  "computable core" (also in a subsection title), "convenience form", "verdict-bearing" and
  "matroidal regime". Bundled nodes (`F-009`, round 5): `def:pebble-counts` (5 pins),
  `lem:pebble-game-invariants` (5), `def:tryReachPebble` (4); `def:blockingWitness` has no pin and
  no `\leanok`. Check the Lee–Streinu pointers (Theorem 8, Lemma 15, Corollary 11, §§5–6),
  Jacobs–Hendrickson 1997, and Lee–Streinu–Theran (the bib entry is CCCG 2005; `.refs/` holds a
  2008 file).
- **`executable`** (carve-out) is about the Lean artefact itself (`#eval`, `decide`,
  `native_decide`, the `Decidable` instances, the CLI), so names stay as addresses. What goes:
  Lean as the subject of sentences, changelog ("was already factored", "no longer needed"), and
  Lean syntax in statement blocks (`(D.outNbhd v).sort (·≤·)`, `ofLex ∘ …`). Unverified claims:
  "sub-second wall time on a developer laptop", "polynomial time", and where `K₄` is rejected.

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
task at Opus, a fresh agent per task, except the close, which may run at Sonnet (§2).

- [x] **1. O — the open** (`bca00d3f`; docs only): this log, the ledger, the baselines, the axioms
  check and the status surfaces.
- [x] **2. A — the dependency-audit script** (`68bc7ad7`): `scripts/blueprint-deps.py` with its
  Lean half `scripts/BlueprintDeps.lean`; its first report is the ledger's `F-001`–`F-012`.
- [x] **3. S — the sample** (`67525c41`; `henneberg.tex`'s *Preservation of the Laman property*):
  approved at Stop 1, which dropped "These facts are classical." (`e9e3f37d`). Found `F-013`.
- [x] **4. E — pin the exemplar** (`09106a34`): `notes/Prose-exemplar.md` and principle B's
  *Constructions* clause.
- [ ] **5. The slices**, one commit each, in `main.tex` order, each chapter's openings in its last
  slice (principle F). The diagnosis of each is its chapter's, above.
  - [x] **5.1 `sparsity.tex`, first half** (`4657a7fc`; 15 nodes). Found `F-014`.
  - [x] **5.2 `sparsity.tex`, rest and openings, `laman.tex`** (`0a2230a0`). `F-015`–`F-018`.
  - [x] **5.3 `henneberg.tex` apart from the sample** (`690ac764`; 8 nodes). Found `F-019`.
  - [x] **5.4 `frameworks.tex`** (`6fcabe9c`; 19 nodes). Found `F-020`.
  - [x] **5.5 `henneberg-rigidity.tex`** (`a9bde8de`; 5 nodes). Found `F-021`, `F-022`.
  - [x] **5.6 `trivial-motions.tex`** (`0ac690f4`; 13 nodes). Found `F-023`, `F-024`.
  - [x] **5.7 `laman-theorem.tex`, first part** (`2e09aae1`; then 30–329). `F-025`, `F-026`.
  - [x] **5.8 `laman-theorem.tex`, rest and opening** (`318020da`; 331–513, 1–28). `F-027`.
  - [x] **5.9 `rigidity-matroid.tex`, first part** (`537db294`; then 41–502). Found `F-028`.
  - [x] **5.10 `rigidity-matroid.tex`, rest and opening** (`d0178306`). `F-029`, `F-030`.
  - [x] **5.11 `count-matroid.tex`** (`d6a53778`; then 1–298). Found `F-031`, `F-032`.
  - [x] **5.12 `dfs.tex`** (`e5dd8256`; then 1–204). Found `F-033`.
  - [x] **5.13 `pebble-game.tex`, first part** (`db7ff7d6`; then 61–539). `F-034`, `F-035`.
  - [x] **5.14 `pebble-game.tex`, soundness and completeness** (this commit; now 540–893, 8
    nodes): statements and proofs in words, independence defined, the rejection argument set
    beside Lee–Streinu's. Filed `F-036`–`F-040`.
  - [ ] **5.15 `pebble-game.tex`, correctness, verdict, corollary and opening** (now 895–1071,
    1–60): 4 nodes, 237 lines.
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

- `F-015` (S, task 5.2): `thm:isTightOn-insert-vertex-with-edges` assumes $V$ finite; its pin
  does not.
- `F-020` (S, task 5.4): `IsInfinitesimallyRigid` is weaker than Jordán's rank form when
  $2 \le |V| \le d - 1$; $d = 2$ and the two $d = 3$ headline corollaries are unaffected.
- `F-025` (M, task 5.7): the blueprint, `intro.tex` and Lean docstrings credit Lovász–Yemini with
  "row-independent iff $(2,3)$-sparse", which Jordán credits to Laman (Theorem 2.2.1).
- `F-026` (S, task 5.7): `lem:span-range-rigidityRow` assumes $V$ finite; its pin assumes only
  finitely many edges.
- `F-027` (S, task 5.8): `lem:isSparse-of-rowIndependent-two` assumes $V$ finite; its pin does
  not.
- `F-028` (S, task 5.9): five lift and transport nodes of `rigidity-matroid.tex` assume their
  vertex sets finite; their pins do not.
- `F-031` (S, task 5.11): `lem:exists-isTightOn-of-insert-not-sparse` assumes $V$ finite; its pin
  does not.
- `F-034` (S, task 5.13): `lem:pebble-game-invariants` assumes $V$ finite and $\ell < 2k$, and
  puts (1)–(2) under $\ell \le k|V'|$; its pins assume none of these.
- `F-036` (S, task 5.14): `thm:pebble-game-soundness` assumes $\ell < 2k$; its pin does not. Its
  old wording also left out "each edge once", which the pin requires; the rewrite says it.
- `F-037` (S, task 5.14): `lem:workhorseWitness-certifies` assumes $G$ finite; its pin assumes only
  that $G$ has finitely many edges.
- `F-038` (S, task 5.13, filed by 5.14): `def:blockingWitness` now also asks $\ell \le k|V'|$
  (`db7ff7d6`), settling its two old sentences on the reject verdict's reading.

## Moved to a later round

`E`, `N`, `T` and `U` findings for round 5, `prose-graph`, and `L` findings for a later Lean round,
one line each naming the ledger ID and the task that found it.

- `F-001` (E, task 2): round 1's chapters, 83 missing `\uses` edges at 37 nodes.
- `F-002` (E, task 2): round 2's chapters, 99 missing edges at 58 nodes.
- `F-003` (E, task 2): round 3's files, 164 missing edges at 47 nodes.
- `F-004` (E, task 2): round 4's chapters, 76 missing edges at 42 nodes.
- `F-005` (E, task 2): `pencil.tex` and `main-component.tex`, 114 missing edges at 58 nodes.
- `F-006` (E, task 2): 397 unbacked `\uses` across the blueprint, for a check.
- `F-007` (E, task 2): three `\uses` of the remark `rem:kt-lemma-41`, none drawn.
- `F-008` (E, task 2): the graph's four unfilled nodes.
- `F-009` (N, task 2): 28 nodes with four or more pins.
- `F-010` (N, task 2): six pinned helpers that draw missing in-edges.
- `F-011` (N, task 2): seven missing edges that would close a cycle.
- `F-012` (N, task 2): 202 pins outside every main result's closure (liveness).
- `F-013` (L, task 3): `typeII_isLaman`'s binder `a ≠ b`, implied by its edge hypothesis.
- `F-014` (N, task 5.1): the sparse reverse decomposition's low-degree lemma has no node; the
  degree-≤ 3 node and its Laman form are outside every main result's closure.
- `F-016` (N, task 5.2): the degree-three case of the sparse reverse decomposition has no nodes;
  Jordán's Lemma 2.1.3 is argued only in the Lean.
- `F-017` (L, task 5.2): two `hF_finite` binders that follow from `hF_sub`.
- `F-018` (L, task 5.2): `typeII_reverse_blocker`'s docstrings say "distinct"; its statement does
  not.
- `F-019` (N, task 5.3): the sparse reverse decomposition's node is in `rigidity-matroid.tex`,
  after its first user in `henneberg.tex`, though it uses only `sparsity.tex`.
- `F-021` (L, task 5.5): `typeII_isGenericallyRigidInj_two_of_nonCollinear`'s binder `a ≠ b`,
  implied by its non-collinearity hypothesis.
- `F-022` (L, task 5.5): two docstrings in `HennebergRigidity.lean` that contradict their
  declarations.
- `F-023` (L, task 5.6): `TrivialMotions.lean`'s docstrings name a declaration and a $d = 2$ case
  that the file does not have.
- `F-024` (L, task 5.6): `trivialMotionFamily_linearIndependent`'s `[Finite V]` is unused, though
  its `nolint` comment calls the linter wrong.
- `F-029` (N, task 5.10): `rigidity-matroid.tex`'s matroid nodes use `count-matroid.tex`'s, which
  comes after it.
- `F-030` (L, task 5.10): docstrings in `MatroidIdentification.lean` and
  `LinearRigidityMatroid.lean` that contradict their declarations.
- `F-032` (L, task 5.11): `countMatroid`'s docstring gives $(3,6)$ as a failure of augmentation;
  $(3,6)$-sparse graphs have no edges.
- `F-033` (L, task 5.12): the search marks only the current walk, so it is exponential in the
  worst case; docstrings call the reachability region's cost quadratic.
- `F-035` (L, task 5.13): docstrings in `PebbleGame/Basic.lean` and `Algorithm.lean` that
  describe later or earlier states of the code; one contradicts its file.
- `F-039` (L, task 5.14): `hloops` in three pebble-game theorems follows from their `himg`.
- `F-040` (L, task 5.14): docstrings in `PebbleGame/Correctness.lean` and `Algorithm.lean` that
  name blueprint labels and declarations that do not exist.

## Blockers / open questions

- None. Stop 1 was answered on 2026-10-07 (*Autopilot: for the PI*).

## Hand-off / next phase

**Next: task 5.15**, the fifteenth slice: the rest of `pebble-game.tex` (carve-out; now 895–1071,
*Correctness of the computable core*, *User-facing verdict* and *Matroidal-independence
corollary*) and its opening (1–60). It has 4 nodes: `thm:pebble-game-correct`,
`def:pebbleGameResult`, `thm:pebbleGameResult-isAccept-iff` and
`cor:pebble-game-countMatroid-indep`. The diagnosis is under *Per-chapter diagnosis*, the gates
under *Scope*. What 5.15 must know:
- **The names** (*Decisions*, tasks 5.13 and 5.14): the pebble search; processing $uv$ at $D$,
  which accepts $uv$ and returns $D'$ or rejects it and returns a failure witness $(D, V', (u, v))$;
  the pebble game on a list from $D_0$, and on $G$, which accepts $G$ with $D$ or rejects it with
  $V'$; *independent in $D$*. An edge list is "the pairs $(u_1, v_1), \ldots, (u_m, v_m)$ list the
  edges of $G$, each once, as $(u, v)$ or as $(v, u)$" (the pins' `hloops`, `hpairwise`, `himg`).
  "For every choice of the lists $N^+_D(a)$" replaces "the computable core".
- **Already written, so cite it rather than repeat it** (principle F, *Once*). *Soundness*'s
  opening sketches the accept direction (Lee–Streinu's Corollary 12). *Completeness*'s opening
  states what the correctness section completes ("if the pebble game on $G$ rejects $G$ with $V'$,
  then $V'$ is a blocking witness for $G$"), states Lee–Streinu's Lemma 14, and says that
  correctness argues at the rejection, not by iterating Lemma 13. The opening's sentence on the
  return type of `def:tryAddEdge` (below) should agree with it.
- **`thm:pebble-game-correct`.** Its "edge list whose $\mathrm{Sym}_2$-image is $E(G)$" leaves out
  "each edge once", which its pin requires: write the list as 5.14 did (`F-036`). Part (2)'s step
  `runPebbleGameWith_witness_bridges` is unpinned: the witness's pair is an entry of the list, so
  an edge of $G$, and its $D$ orients only edges of $G$ (an induction on the list, like
  `lem:runPebbleGameWith-underline-subset` (2)). `lem:workhorseWitness-certifies` then applies; it
  is the only step that uses $\ell < 2k$ (`F-036`), and it assumes $G$ finite (`F-037`).
- **Statement vs pin.** Check the four statements for $\ell < 2k$ and finiteness: the verdict
  section's variables are `[DecidableEq V] [Fintype V]`, and `runPebbleGameExec_isAccept_iff` is in
  `Exec.lean`.
- **Lee–Streinu for 5.15**, all in `.refs/`: Theorem 8 (p. 1431), Corollary 11 (p. 1432), Lemma 15
  and "Corollary 12 and Lemma 15 prove Theorem 8" (p. 1433), and §§5–6 (the component pebble game
  and union pair-find from p. 1433; the Henneberg sequences).
- **For 5.15 and 5.16.** Lee–Streinu's $O(m_a n)$ bound (§3, p. 1430) counts linear-time searches,
  and this search is exponential in the worst case (`F-033`): no running-time claim for the formal
  algorithm. The opening (1–60) still says "matroidal regime" and "$I$-component", and that the
  per-edge equivalence is "recorded in the return type of `def:tryAddEdge`, one constructor per
  outcome". `executable.tex` cites `fmlnote:pebble-game-computable-core` for "the computable
  core" and "the convenience form", names the note no longer uses (it says: the forms with the
  lists as an argument, names ending in "With", and the forms with mathlib's lists).
  Jacobs–Hendrickson 1997 is cited only in 1–60 and the chapter's last paragraph; Crossref's record
  for DOI `10.1006/jcph.1997.5809` matches the bib entry (title, J. Comput. Phys. 137(2),
  346–365), as does Lee–Streinu's reference [14].
- **Terms fixed by 5.11, for 5.15–5.16.** "For $\ell < 2k$" replaces "the matroidal regime". A
  *component* of a sparse graph is a maximal tight set (Lee–Streinu's term, `count-matroid.tex`'s
  opening), and $C_G(X)$ is the union of the tight sets containing $X$; "$I$-component" is gone
  from that chapter. A set $I \subseteq E(K_V)$ is *$(k,\ell)$-sparse* if the graph on $V$ with
  edge set $I$ is. Write "section", not "chapter".
- **Sources checked by 5.4–5.14:** Jordán pp. 35–39, 43–45, 48–49 and 51; Lee–Streinu 2008:
  Lemma 1, Theorem 2, Theorem 5(1)–(4), Corollaries 6–7, §3 (p. 1430, and Fig. 4's Algorithm 1,
  p. 1431), §4 (the functions and Lemma 10, p. 1432; Corollary 12 and the sentence after it,
  p. 1432; $\mathrm{Reach}(v)$, Lemmas 13–14 with their proofs and the remark after Lemma 14,
  pp. 1432–1433), and the definition of an independent element (§2, p. 1429); Whiteley 1996 (a
  preprint: cite by number only), Proposition A.1.1. Asimow–Roth is verified only for "rigidity
  is decided for almost all placements" and "at a generic framework, rigid iff infinitesimally
  rigid". Detail is in each task's commit.
- **For the close (task 6):** `notes/BlueprintExposition.md`'s Group-A line still says
  "Lovász–Yemini easy direction" and "hard direction" (`F-025`). Then task 5.16 follows, and task 6
  closes the round.

**The PI's check on the first slices** (Stop 1, item 5): "the overriding goal is to make sure the
result is understandable". The coordinator read 5.1–5.3 in full against the exemplar (2026-10-07):
understandable, no prompt tightening needed; it keeps reading each slice's text.

## Decisions made during this round

- **The sample** (the open; approved at Stop 1): `notes/Prose.md` §3's default, `henneberg.tex`'s
  *Preservation of the Laman property*, typical of phases 1–6. Considered: `sparsity.tex`,
  `frameworks.tex`'s definitions.
- **The slicing** (approved at Stop 1): 150–430-line slices cut at subsection boundaries, openings
  last, `laman.tex` with `sparsity.tex`'s last slice; 16 slices averaging 306 lines, above
  `40-exposition`'s 270, since these chapters are less dense.
- **The screens** are recorded under *Scope*, since `notes/Prose.md` §7's regex was not.
- **Task 2: the Lean half is a non-`module` file importing the library root.** A `module`
  importer sees the project's theorems as axioms and none of its private declarations, so it
  cannot see what a proof reaches; measured, and recorded in `scripts/BlueprintDeps.lean`'s
  docstring. A `module` file also could not import the root, which is not a module.
- **Task 2: what counts as missing.** A reached node that is already a `\uses` ancestor is
  *implied*, not missing, since the graph is drawn transitively reduced and would not show the
  edge. Unbacked `\uses` split into those reached through another pinned node and those with no
  Lean basis. A missing edge that would close a cycle is flagged as a node-shape finding.
- **Task 2: the ledger groups the script's findings** (the coordinator's suggestion): one `E` entry
  per chapter group for missing edges, one for unbacked edges, and one `N` entry per node-shape
  pattern. The ledger's header states the rule; `--chapter` and `--label` reproduce the detail.
- **Stop 1: the PI's answer, verbatim** (2026-10-07; the items are numbered as under *Autopilot:
  for the PI*). On 1 and 2: "1-2 these look good." On 3: "edge notation, the graph G' names is not
  a big deal as long as it's understandable; I'm more concerned about the classical attribution:
  could we omit it or find something to back that up? The iff node also seems natural." On 4: "The
  amendment looks good." On 5: "I think this is reasonable; more than following rules strictly
  though, the overriding goal is to make sure the result is understandable. Perhaps the coordinator
  should pay careful attention to the first few Sonnet dispatches to ensure that the guidelines are
  working." On 6: "Looks good to me."
- **Stop 1: the attended session's notes** (not the PI's words) are under *Autopilot: for the PI*:
  option B; "These facts are classical." dropped (`e9e3f37d`); every slice at Opus. The verbatim
  answer above stays in this section (the project rule), whatever later compression does.
- **Stop 1: what the approval settles** (task 4's reading, not the PI's words). The sample is the
  exemplar for rounds 1–4, `notes/Prose-exemplar.md`. Choice (i) is now `AUTHORING.md` principle
  B's *Constructions* clause; (ii) and (iii) hold for every slice. 3a and 3b go to task 5.3, held
  to the PI's test that the result is understandable. 3d: `thm:typeI-isLaman-iff` stays a node of
  its own, and no finding is filed. The PI's item-5 sentence stands before `AUTHORING.md`'s six
  principles. The slice lists stand.
- **The carve-out in tasks 5.12–5.16** (Stop 1's item 5, approved). In `dfs.tex` and
  `pebble-game.tex`, a result type in a statement (`.inr D`, `some (w, p)`, `PebbleGameResult`) is
  restated as what the algorithm returns, in words, as choice (i) does for constructions.
  `executable.tex` is about the Lean artefact, so its names stay as addresses; but Lean stops being
  the subject of sentences, changelog prose goes, and Lean syntax leaves its statement blocks.
- **Task 5.4: the bar-joint notation** for the rest of the round. The rigidity map is $R(G, p)$, as
  Jordán writes the rigidity matrix and `generic-lift.tex` already does; the space of frameworks is
  $(\R^d)^V$; a framework is the map $p$ alone (also "placement"); the injective form is
  "injectively generically rigid". `RigidityMap G p` and `Framework V d` leave statements.
- **Task 5.7: the rows and the credit for the count.** The rows of $R(G, p)$ are the functionals
  $r_e$ in $((\R^d)^V)^*$, with the transpose $R(G, p)^{\top}$; the function/dual-space split of
  the Lean is one `fmlnote`. The $(2,3)$ count of row-independent sets is credited to Maxwell, with
  Whiteley's 11.1.3 and Jordán's 1.3.1, and "row-independent iff sparse" to Laman, as Jordán does
  (`F-025` records where the blueprint says Lovász–Yemini). A truncated `2 * card V - 3` in a pin
  is written $\max(2|V| - 3, 0)$: the pin's meaning, which the real-number reading made false.
- **Task 5.13: the pebble game's names**, for 5.14–5.16. The procedures are "the pebble search for
  $P$ from $v$ in $D$" (`def:tryReachPebble`), "processing $uv$ at $D$", which accepts $uv$ and
  returns $D'$ or rejects it and returns a *failure witness* $(D, V', (u, v))$ (`def:tryAddEdge`,
  `def:workhorseWitness`), and "the pebble game on a list from $D_0$" and "on $G$", which accepts
  $G$ with $D$ or rejects it with $V'$ (`def:runPebbleGame`). Each partial orientation comes with
  out-neighbour lists $N^+_D(a)$; $\mathrm{Reach}_D(x)$ is Lee–Streinu's reachability region. The
  Lean's verdict type is "the formal pebble game on $G$ returns its answer together with proofs".
- **Task 5.14: independence, and where Lee–Streinu's Lemma 13 sits.** An edge $uv$ not oriented
  in $D$ is *independent in $D$* if the graph on $V$ with edge set $\underline{D} \cup \{uv\}$ is
  $(k, \ell)$-sparse (Lee–Streinu §2, p. 1429); *Completeness*'s opening defines it. Correctness
  argues at the rejection, through the failure witness. The two Lemma 13 nodes stay, proved, and
  the opening says that correctness does not use them (their pins are dead, `F-012`). A Lean edge
  list is "the pairs $(u_i, v_i)$ list the edges of $G$, each once, as $(u, v)$ or as $(v, u)$".
