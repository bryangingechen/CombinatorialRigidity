# PROSE round 2/5 — `prose-molecular`, body-bar, body-hinge and the molecular foundations (work log)

**Status:** in progress (opened 2026-10-08). Round 2 of **PROSE**'s five rounds; their plan and the
PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round rewrites the prose of the eight chapters `matroid-union.tex` →
`meet.tex` to `40-exposition`'s register and round 1's exemplar. Every `\label`, pin, `\leanok`,
`\uses` edge and statement strength stays as it is. What else the round notices goes to the ledger
`notes/Prose-findings.md`: the open recorded `F-048`–`F-050`, tasks 2.1–2.15 `F-051`–`F-097`. 20
one-commit tasks; tasks 1 and 2.1–2.15 are done, and the round has no planned stop. **Next
concrete task:** task 2.16, `molecular-induction.tex` 1309–1551 at the open (1602–1844 now), at
Opus (*Lemma checklist*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. No entries yet.

## Current state

**Task 2.15 has landed** (this commit): `molecular-induction.tex` 1033–1308 at the open (1181–1600
now), KT Lemmas 4.3(ii) and 4.5–4.8 and the vertex-count lemma, 9 nodes; the crux
`lem:reduction-step` keeps its full proof. Every `\label`, `\lean{…}`, `\leanok` and `\uses` is
byte-identical; no node moved; one formalization note is new. Nothing is mid-stream; task 2.16 is
next.
- **Gates at this commit**, all the open's values: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, 9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and
  `b53eb8b1cf78cb06`; `print.log` 0 `LaTeX Warning` lines (82 overfull boxes, 86 at the parent;
  none in the slice). Screens: `molecular-induction` register 9 (29 at the open), devices 2 / 7
  (6 / 25), `\operatorname` Lean names 0 (7); the slice has none of the three; cross-chapter
  forward `\uses` 14, unchanged.

**Verified at the open** (2026-10-08, at `ac7bd966`; task 1, docs only):
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines. The axioms check
  runs only at round 1's open and round 5's close (`notes/Prose.md` §2).
- **The no-Lean-edit base is `ac7bd966`**, the open's parent (the close's check is under *Scope*).
- **The round's gate values**, round 1's close reproduced exactly: `lint.sh` green; `verify.sh`
  green (38 s), `checkdecls` silent, **9** `WARNING:` lines (plasTeX package and renderer notices);
  `print.log` **0** `LaTeX Warning` lines and **120** overfull boxes (counted, not gated); the
  built graph **657** nodes and **1 292** edges, fingerprint **`673e3178d1b3145e`**, pin hash
  **`b53eb8b1cf78cb06`** (1 030 pins, 1 020 distinct names; the commands are under *Scope*, gate 3).
- **The surface** (`notes/Prose.md` §3): 8 files, 4 792 lines, 151 nodes, 273 pins. Seven nodes have
  four or more pins (`F-009`): `def:rigidity-matrix` (14), `lem:case-III-claim612-line-in-panel-union`
  (12), `lem:trivial-motions-rank-bound` (9), `def:cut-edges-2ec`, `lem:cut-edge-decomposition` (7
  each), `lem:two-vertex-trichotomy`, `def:graph-operations` (4 each). 148 nodes are green;
  `def:dof-generic`, `def:induced-span` and `lem:forest-surgery-unsplit` are blue (`F-008`).
- **The open's findings:** `F-048`, `F-049` (S) and `F-050` (N). The crux nodes are under *Scope*.

## Scope and standing rules

From `notes/Prose.md` §2, restated only as far as a builder needs them.

- **Surface.** The eight chapters, in `blueprint/src/chapter/main.tex` order: `matroid-union`,
  `body-bar`, `body-hinge`, `extensor`, `rigidity-matrix`, `deficiency`, `molecular-induction`,
  `meet`. No other chapter's TeX. A docs edit that keeps a pointer into a rewritten chapter true is
  in scope (`notes/BlueprintExposition.md`'s entries for these chapters, below).
- **The hygiene rule.** The round does not change a headline statement or the strength of a
  blueprint statement. A finding that would need such a change becomes a ledger `S` entry and a
  line under *Candidates for the PI*. It is not acted on, and it is not a stop.
- **Prose only (rounds 1–4), and no Lean edits (all five rounds).** `CombinatorialRigidity/`,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` stay untouched; the close checks that
  their `git diff --stat` since `ac7bd966` is empty. Every node keeps its `\label`, its `\lean{…}`
  pins, its `\leanok` and its `\uses` edges. A statement block is edited for register and anchoring
  only. A node may move within its chapter to cure a forward reference (`blueprint/AUTHORING.md`
  principle E, *Node order*); a cross-chapter forward reference gets a `\cref` and a sentence
  instead (`F-050` lists fourteen). A graph or node-shape finding becomes a ledger `E` or `N` entry
  for round 5.
- **The register.** `blueprint/AUTHORING.md` principles A–F with their 2026-10-03 clauses, the
  2026-10-07 *Constructions* clause of B, and the PI's sentence before them ("the overriding goal
  is to make sure the result is understandable"); `40-exposition`'s exemplar
  `notes/Phase40-exposition-exemplar.md`; and round 1's pinned sample `notes/Prose-exemplar.md`. No
  chapter of this round is algorithmic, so principle A's carve-out does not apply. From `extensor`
  on, the reader is *Audience & vocabulary*'s rigidity theorist who knows KT 2011, and its
  terminology dictionary binds ("genuine" is "nondegenerate"; "splice" and "carry" go).
- **Crux nodes** keep their full proofs (the crux carve-out, `AUTHORING.md` *Proof verbosity*).
  These are the nodes with a *done* entry in `notes/BlueprintExposition.md`, checked by label:
  - `extensor`: `lem:extensor-independence` (KT Lemma 2.1).
  - `molecular-induction`: `rem:kt-lemma-41`, with the balanced-packing descent
    `lem:base-vfiber-count`, `lem:acyclic-insert-vfiber`, `lem:packing-move`,
    `lem:balanced-forest-packing` and the surgery family's `lem:forest-surgery-split`;
    `rem:kt-lemma-44` and `lem:removal-deficiency`; `lem:reduction-step`;
    `lem:chain-cycle-dichotomy` and `lem:chain-data-extract`.
  - `meet`: `def:meet-complement-iso`, and `lem:case-III-claim612-line-in-panel-union` (its entry
    is under the ledger's `algebraic-induction.tex` heading).

  Ledger verdicts also lean on text in chapters without a crux node; keep them true. The Group-B
  22i verdict says `lem:rank-parallel-full` spells out KT Lemma 5.3's argument in full;
  `deficiency.tex`'s scan names the full `thm:def-eq-corank`; the Phase-40c entry names
  `lem:deficiency-antitone` and `lem:relative-deficiency-rank-bound`. Group A screened phases 12–16
  (`matroid-union`, `body-bar`, `body-hinge`) out as self-exposited.
- **Evidence.**
  - Citations meet `CLAUDE.md` *Referencing prior work*. `.refs/` has every source these chapters
    cite except Nash-Williams 1966 and Edmonds 1970 (`nashWilliams1966`, `edmonds1970`): Edmonds
    1965, Nash-Williams 1961, Tutte 1961, Oxley 2011, Tay 1984 and 1989, Whiteley 1988 and 1996,
    White–Whiteley 1987, Barnabei–Brini–Rota 1985, Crapo–Whiteley 1982, Jackson–Jordán 2009, KT
    2011 and its 2009 arXiv version, and White 1994, which `meet.tex` does not yet cite. Check the
    two missing ones against the DOI landing page or publisher metadata, or weaken the claim to
    "classical" or "see X" (`REFS.md`). The commit that relies on a passage names it.
  - Claims about the Lean come from declarations' statements and bodies, never from docstrings,
    and from `scripts/blueprint-deps.py --label` or `--chapter` for what a pin reaches.
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
  close re-runs them). The first two are round 1's, over this round's files: per chapter, with TeX
  comments stripped, principle-A register hits, then Lean-device hits inside statement blocks and
  in the whole chapter. "Carries" is sometimes literal ("$G$ carries a framework"). The device
  screen misses `\operatorname{…}` Lean names, 34 more at the open (`deficiency` 20,
  `rigidity-matrix` and `molecular-induction` 7 each: `cutEdges`, `partitionDef`, `bodyBarDim`,
  `extProj`, …).
  ```sh
  python3 - blueprint/src/chapter/{matroid-union,body-bar,body-hinge,extensor,rigidity-matrix,deficiency,molecular-induction,meet}.tex <<'PY'
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
  The third counts, per chapter, the `\uses` edges (node, target) whose target is a node of a later
  chapter in `main.tex` order (`F-050`); prose-only slices leave it at the open's 14.
  ```sh
  python3 - matroid-union body-bar body-hinge extensor rigidity-matrix deficiency molecular-induction meet <<'PY'
  import re,sys,glob
  C=[l.strip()[15:-5] for l in open('blueprint/src/chapter/main.tex') if l.strip().startswith('\\input{chapter/')]
  W={}
  for f in glob.glob('blueprint/src/chapter/**/*.tex',recursive=True):
      c=f[22:-4].split('/')[0]
      if c in C: W.update({m:C.index(c) for m in re.findall(r'\\label\{([^}]*)\}',open(f).read())})
  for c in sys.argv[1:]:
      t=re.sub(r'(?<!\\)%.*','',open(f'blueprint/src/chapter/{c}.tex').read()); E=set()
      for s in re.split(r'\\begin\{(?:definition|lemma|theorem|corollary|proposition)\}',t)[1:]:
          s=re.split(r'\\begin\{(?:remark|example|fmlnote)\}',s)[0]; n=re.search(r'\\label\{([^}]*)\}',s).group(1)
          E|={(n,u.strip()) for x in re.findall(r'\\uses\{([^}]*)\}',s) for u in x.split(',') if W.get(u.strip(),-1)>C.index(c)}
      print(c,len(E),len({n for n,_ in E}))
  PY
  ```

## Per-chapter diagnosis

Seen at the open; line numbers are the open's, and the labels are the stable reference. Each slice
re-derives its own findings and records them in its commit and the ledger.

| Chapter | Lines | Nodes | Pins | Register | Lean devices (statements / all) | Forward `\uses` | Task |
|---|---|---|---|---|---|---|---|
| `matroid-union` | 193 | 9 | 15 | 2 | 0 / 5 | 0 | 2.1 |
| `body-bar` | 625 | 23 | 32 | 5 | 26 / 51 | 0 | 2.2, 2.3 |
| `body-hinge` | 144 | 4 | 5 | 3 | 0 / 1 | 0 | 2.3 |
| `extensor` | 215 | 7 | 12 | 1 | 0 / 1 | 0 | 2.4 |
| `rigidity-matrix` | 901 | 26 | 65 | 10 | 1 / 5 | 10 | 2.5–2.7 |
| `deficiency` | 712 | 23 | 54 | 3 | 1 / 2 | 0 | 2.8–2.10 |
| `molecular-induction` | 1 677 | 49 | 64 | 29 | 6 / 25 | 4 | 2.11–2.17 |
| `meet` | 325 | 10 | 26 | 3 | 15 / 56 | 0 | 2.18 |
| **total** | 4 792 | 151 | 273 | 56 | 49 / 146 | 14 | |

The body-bar chapters (phases 12–16) carry their Lean in statements, as round 1's did. The KT
chapters (phases 17–21a) were rewritten for the rigidity-theorist reader after Phase 23, but
predate the 2026-10-03 clauses: their problems are statements that bundle role clauses and
formalization remarks, Lean names in proofs, repeated connective verdicts, and the terminology
dictionary's words ("genuine" ten times in `molecular-induction`, "splice" eight in
`rigidity-matrix`).

- **Done:** `matroid-union` (task 2.1), `body-bar` (tasks 2.2, 2.3), `body-hinge` (task 2.3),
  `extensor` (task 2.4), `rigidity-matrix` (tasks 2.5–2.7) and `deficiency` (tasks 2.8–2.10);
  their open bullets are in this log at the open, `ea058ba8`. `molecular-induction` 43–1308 (tasks
  2.11–2.15; their open items are in this log at `1b06def1`, `90051e3c` and `d9b0e96a`).
- **`molecular-induction`** (phase 20, extended through phase 40; the most crux nodes). Line
  numbers below are the open's; from 1309 on, add 293 for the current text.
  - *Throughout:* the fresh edge label in three statements left (`def:chain-data`,
    `lem:chain-cycle-dichotomy`, `lem:chain-data-extract`; principle D: the labels are explained
    once, in `fmlnote:graph-operations`, with `rem:fresh-edge-supply`); Lean names in proofs
    (`Graph.loopless_of_isMinimalKDof`, `Graph.deficiency_nonneg`, `exists_extensor_in_two_panels`).
  - *2.16–2.17:* `thm:minimal-kdof-reduction`'s statement says "The formalization states this
    as…" (the induction principle is the pin's content: state it as mathematics). The two KT
    Lemma 6.1 realization lemmas use round 3's nodes (`F-050`). `lem:chain-cycle-dichotomy`
    writes $D = \binom{n+1}{2}$ and a length-$n$ chain, as `rem:kt-lemma-44` writes $n$; the
    opening (1–42) repeats §*Forest surgery*'s verdict.
- **`meet`** (phase 21a; crux `def:meet-complement-iso`,
  `lem:case-III-claim612-line-in-panel-union`). The most Lean in statements of the KT chapters:
  `\mathrm{topEquiv}`, `\mathrm{pairingDualEquiv}`, `\mathrm{complementIso}`,
  `\mathrm{wedgePairing}`, `\mathrm{toDual}`, `W.\mathrm{subtype}`, `\mathrm{gradedMul}`,
  `\mathrm{ScrewSpace}\,k`; proofs read as Lean (`Module.Basis.exteriorPower`,
  `LinearEquiv.funUnique`). It writes $V = K^{N}$, $N = k + 2$, where `extensor` writes
  $K^{d+1}$. It sits after `molecular-induction` but builds only on `extensor`: the opening says
  so. The 12-pin node's formalization note lists Case III's realization declarations, its statement
  uses round 3's panel $\Pi(u)$, and its proof cites `def:meet-complement-iso` for
  `lem:complement-iso-decomposable-wedge-perp`'s fact. `def:meet`, the chapter's object, comes
  last. White 1994 is in `.refs/` and uncited.

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
slice at Opus, a fresh agent per task; the close may run at Sonnet (§2).

- [x] **1. O — the open** (`ea058ba8`; docs only): this log, the baselines, the open's findings
  `F-048`–`F-050`, and the status surfaces.
- [ ] **2. The slices**, one commit each, in `main.tex` order, each chapter's opening in its last
  slice (principle F). The diagnosis of each is its chapter's, above.
  - [x] **2.1–2.15, `matroid-union.tex` through `molecular-induction.tex` 43–1308**: 2.1
    `6c26eed5`, 2.2 `7fe65223`, 2.3 `53ec36db`, 2.4 `47eb5225`, 2.5 `5399e053`, 2.6 `af438fd1`, 2.7
    `27daa953`, 2.8 `86b44e1b`, 2.9 `22317b88`, 2.10 `1b06def1`, 2.11 `ce54bf15`, 2.12 `01aec968`,
    2.13 `90051e3c`, 2.14 `d9b0e96a`, 2.15 this commit. Each commit message gives its ranges and
    findings (`F-051`–`F-097`). The ranges below are the open's.
  - [ ] **2.16 `molecular-induction.tex`, Theorem 4.9 and the adjacent degree-2 pair**
    (1309–1551): 8 nodes, 243 lines.
  - [ ] **2.17 `molecular-induction.tex`, the chain-or-cycle dichotomy and the opening**
    (1552–1677, 1–42): 4 nodes, 168 lines.
  - [ ] **2.18 `meet.tex`**: 10 nodes, 325 lines.
- [ ] **3. X — close the round** (`CLEANUP.md` *Workflow* 5; docs only).
  - *Gates:* whole-project `lake build` green; the no-Lean-edit check (`git diff --stat ac7bd966..
    -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` empty). The axioms
    check runs next at round 5's close, not here (§2).
  - *The blueprint:* `lint.sh` and `verify.sh` green, the invariance values the open's, the
    warning counts unchanged, overfull boxes counted; the three screens re-run beside the open's
    table.
  - *Findings:* every ledger entry the round found has its line here, and vice versa.
  - *The exposition ledger:* check the pointers into these chapters (*Scope*, crux nodes and
    verdicts) against the new text, and add a round note to `notes/BlueprintExposition.md`.
  - *Status surfaces:* the ROADMAP row reads ✓ Complete; ROADMAP's PROSE bullet and
    `notes/Prose.md`'s **Status** name round 3's open.
  - *The queue:* `prose-molecular`'s row in `.claude/autopilot/queue.toml` gets `done = true`, and
    nothing else there changes.

## Candidates for the PI

`S` and `M` findings, one line each naming the ledger ID (`notes/Prose-findings.md` holds the
finding). Recorded, never acted on in this round; round 5's report ranks them for the PI.

- `F-048` (S, task 1): `def:body-hinge-framework` gives each hinge an affine subspace that its pin
  does not record, so the main result `body_hinge_tay` is the bar-bundle form.
- `F-049` (S, task 1): `lem:rank-rotation-semicont` claims KT Lemma 5.2, which its pins are not,
  and a monotonicity form whose span inclusion is the reverse of its pins'.
- `F-051` (S, task 2.1): `thm:matroid-partition-rank` states the rank of every subset for any
  family, and the independence criterion; its pins give the first at $X = E$ only, and both for
  copies of one matroid.
- `F-053` (M, task 2.1): the credits for $M_f$, the polymatroid rank formula and the union's rank
  formula (Edmonds–Rota, not Edmonds 1970; Nash-Williams and Edmonds, not Edmonds 1965), fixed in
  `matroid-union.tex` and left in `intro.tex`, `deficiency.tex`, `molecular-induction.tex` and the
  Lean docstrings.
- `F-058` (S, task 2.3): `thm:tay-witness` and `thm:body-hinge-tay` assume $d \ge 2$, which their
  pins do not; `lem:edge-multiply-sparse`'s proof applies the first for every $d$.
- `F-060` (S, task 2.4): `lem:case-III-claim612-extensor-span` (round 3) states that the
  two-extensors $\bar p_i \vee \bar p_j$ span $\bigwedge^k K^{k+2}$; its pin is about the omit-two
  extensors, the same family only at $k = 2$.
- `F-079` (S, task 2.10): `lem:rk-within-parts` bounds the rank of all the edges inside the parts;
  its pin bounds every set of such edges, the form the formal proof of KT eq. (2.4) uses.
- `F-081` (M, task 2.10): KT eq. (2.4) was credited to Jackson and Jordán's Theorem 6.1 (the
  generic rank); it is their Theorem 4.1(a) at $\tilde G$. Fixed in `deficiency.tex`, left in
  `intro.tex`, `formalization.yaml` and the Lean docstrings.
- `F-083` (S, task 2.11): `lem:circuit-induces-rigid` states KT Lemma 3.4's partition of $X - e$
  into $D$ spanning trees, which no declaration states; its pins give the count and the rigidity.
- `F-084` (S, task 2.11): `lem:reduction-step` claimed that contraction gives a minimal
  $0$-dof-graph; its pin is the matroid form, which task 2.15 states, and the graph form is
  `lem:rigidContract-isMinimalKDof`'s.
- `F-086` (S, task 2.12): `lem:acyclic-insert-vfiber` and `lem:packing-move` assume that $v$ has
  degree two; their pins hold at every vertex.

## Moved to a later round

`E`, `N`, `T` and `U` findings for round 5, `prose-graph`, and `L` findings for a later Lean round,
one line each naming the ledger ID and the task that found it.

- `F-050` (N, task 1): 14 `\uses` edges at 11 nodes of `rigidity-matrix.tex` and
  `molecular-induction.tex` point at nodes of later chapters.
- `F-052` (N, task 2.1): Welsh's theorem, the induced-matroid-is-$M_f$ lemma and the $k$-copies
  independence criterion are load-bearing lemmas with no node.
- `F-054` (N, task 2.2): `lem:k-frame-span-le-pi`'s three pins have no Lean caller; the rank count
  uses their per-set analogues, which have no node.
- `F-055` (L, task 2.2): `exists_forestPacking_cover_of_isSparse_restrict` repeats the forward half
  of `tutte_nash_williams`, and both its callers repeat that proof's disjointification.
- `F-056` (T, task 2.3): `generic-lift.tex` and `intro.tex` keep Tay and Whiteley's $n$ and
  $d = n(n+1)/2$ (and $\delta$) for the body-bar dimension; round 4 rewrites both.
- `F-057` (L, task 2.3): three `BodyBar/` docstrings disagree with their declarations or sources
  (Whiteley's Theorem 13; a connectivity hypothesis; "degenerate" standard-basis two-extensors).
- `F-059` (N, task 2.4): `def:plucker-coords`'s pins have no Lean caller, and no declaration
  relates them to the extensor; the expansion the chapter states is unformalized.
- `F-061` (L, task 2.5): the "forest" row-independence lemmas pinned on `def:rigidity-matrix`
  assume that every component of the edges is a star.
- `F-062` (E, task 2.5): `lem:case-II-placement-new-rows` uses and cites `lem:rank-delete-vertex`
  for the dimension that `def:hinge-row-block` supplies.
- `F-063` (L, task 2.5): the pin of `lem:trivial-motions-rank-bound`'s deficiency bound asks
  $C(e) \neq 0$ at every edge label, not only at the edges of $G$.
- `F-064` (L, task 2.6): the docstring of `lem:block-rank-cut`'s first pin names a node label that
  does not exist.
- `F-065` (N, task 2.6): `cor:block-rank-vertex-two-cut` has no Lean caller and no user node.
- `F-066` (E, task 2.7): two `rigidity-matrix.tex` nodes use a node that their pins do not reach,
  and not the one they do.
- `F-067` (T, task 2.7): five chapters call the generic rank formula, KT Proposition 2.3, the
  "analytic half" of KT Proposition 1.1, which is Tay and Whiteley's theorem.
- `F-068` (N, task 2.7): `lem:rigidityRows-pinned-placement-rank-add`'s second pin has no Lean
  caller.
- `F-069` (L, task 2.7): four docstrings of `rigidity-matrix.tex` pins name the wrong node.
- `F-070` (L, task 2.7): a hypothesis of `lem:rank-polynomial-IH-relabel-proj`'s pin follows from
  another.
- `F-071` (E, task 2.8): four `deficiency.tex` nodes have edges their pins do not back, and
  `lem:cut-edge-decomposition`'s pins reach two later nodes of the chapter.
- `F-072` (T, task 2.8): `intro.tex` calls $M(\tilde G)$ the count matroid "at the boundary regime
  $\ell = 2k = D$", which is false ($\ell = k$) and no chapter now defines.
- `F-073` (T, task 2.8): `main-component.tex` and `pencil.tex` write the dimension as $n$ (about
  48 lines), where round 2 writes KT's $d$.
- `F-074` (L, task 2.8): `Graph.matroidMG`'s docstring repeats the false "boundary regime
  $\ell = 2k = D$"; two more call the independence criterion "boundary-regime cleanliness".
- `F-075` (L, task 2.8): the hypothesis $D \ge 1$ of KT Lemma 3.6's pin is unused, and two pins
  take it only to pass it on.
- `F-076` (E, task 2.9): three `deficiency.tex` nodes have edges their pins do not back, and their
  pins reach nodes of `molecular-induction.tex` and `jacobs.tex` that no `\uses` names.
- `F-077` (L, task 2.9): two docstrings of `deficiency.tex` pins are stale or name the wrong node,
  and an ear lemma's pin has an unused hypothesis.
- `F-078` (E, task 2.10): `thm:def-eq-corank` and `lem:rk-within-parts` have edges their pins do
  not back, and `lem:deficiency-zero-iff-tree-packing`'s pin reaches `def:k-dof`.
- `F-080` (L, task 2.10): four docstrings around KT eq. (2.4)'s pins are stale or name the wrong
  node.
- `F-082` (E, task 2.11): `def:induced-span` has natural pins; two contraction lemmas use
  `def:rigid-contraction`, which their pins do not reach.
- `F-085` (L, task 2.11): five docstrings of `molecular-induction.tex`'s first pins name the wrong
  node or claim an identity that no declaration states.
- `F-087` (N, task 2.12): `lem:packing-move`'s pin has no Lean caller; the balanced partition's
  pin makes the move inline.
- `F-088` (L, task 2.12): that inline move, and stale or misaddressed docstrings on the balanced
  partition's six pins.
- `F-089` (E, task 2.13): the reroute lemmas' edges to each other belong on their proofs; the
  fact they use, $G_v \le G_v^{ab}$, is `lem:splitoff-edge-substitution`'s, in `case-ii.tex`.
- `F-090` (N, task 2.13): `cor:forest-surgery-deficiency` restates `lem:forest-surgery-split`; its
  pin is a deprecated shim with no caller.
- `F-091` (N, task 2.13): the unfilled `lem:forest-surgery-unsplit` is a case of
  `lem:edge-splitting`, and no node uses it.
- `F-092` (L, task 2.13): an unused hypothesis in the two edge-splitting pins, and stale or
  misaddressed docstrings on the surgery's pins.
- `F-093` (E, task 2.14): `lem:splitoff-deficiency`'s edges to $M(\tilde G)$ and KT eq. (2.4), and
  `lem:removal-deficiency`'s to it, have no Lean basis.
- `F-094` (L, task 2.14): an unused $e_a \neq e_b$ in the upper bound's shared core, and docstrings
  crediting KT Lemmas 4.3–4.5 or 4.3(ii) on the deficiency bounds' pins.
- `F-095` (E, task 2.15): KT Lemmas 4.3(ii)–4.8's nodes have edges their pins do not back, and miss
  `lem:rigid-full-rank`, `lem:splitoff-edge-substitution` and `def:cut-edges-2ec`; two pointers
  from `case-i.tex` and `case-ii.tex` name the wrong node.
- `F-096` (N, task 2.15): `lem:removal-deficiency-strict` (KT 4.4's equality case and KT 4.7) and
  `lem:reduction-step` (KT 4.8(i) and, by a shared pin, KT 3.5) bundle what KT state separately.
- `F-097` (L, task 2.15): KT 4.8(ii)'s pin needs neither KT 4.7 nor $D \ge 3$; a derivable
  `hV3`; docstrings naming `lem:reduction-step` or stale.

## Blockers / open questions

- None. The round has no planned stop.

## Hand-off / next phase

**Next concrete task: task 2.16, `molecular-induction.tex` 1309–1551 at the open (1602–1844
now: the subsections *Theorem 4.9* and *Simplicity and the adjacent-degree-2-pair lemma*,
`thm:minimal-kdof-reduction` through `lem:chain-data-of-noRigid`), at Opus**, a fresh agent
(`notes/Prose.md` §2). Its diagnosis is the `molecular-induction` bullet's *Throughout* and
*2.16–2.17* items under *Per-chapter diagnosis*, its gates and screens under *Scope*. Then tasks
2.17–2.18 in order, and task 3 closes the round. For the slices:
- **The PI's check** (round 1's Stop 1, item 5: "the overriding goal is to make sure the result is
  understandable"): the coordinator has read tasks 2.1–2.3 in full against the exemplars.
- **Notation.** Tasks 2.8–2.18 write KT's $d$ and $D = \binom{d+1}{2}$, drop the stray $n$, and
  point at `body-hinge`'s $\tilde G = (D-1)\cdot G$ (*Decisions*). `body-bar.tex` writes bodies in
  $\R^d$ and a vector $b_e \in \R^D$ per bar (Tay's model); `thm:tutte-nash-williams` is
  *Decomposition into forests* (Tutte, Nash-Williams 1961 and 1964).
- **Crux nodes** keep their full proofs, in tasks 2.17 and 2.18 (*Scope*).
- **What `rigidity-matrix.tex` now says that later tasks lean on.** It recalls the deficiency
  before `lem:trivial-motions-rank-bound`, as `def:D-deficiency` states it. Its opening names the
  generic rank formula Jackson and Jordán's, KT Proposition 2.3, and KT Proposition 1.1 Tay and
  Whiteley's theorem (`F-067`). Its subgraph convention ($R(H,p)$ keeps $p$'s hinges and $G$'s
  bodies), row spaces $\mathcal R$, and $\pi_W$ for deleting the columns of $W$ are fixed in
  *Rank-addition lemmas*. `lem:block-rank-cut` is titled for a cut edge:
  `molecular-induction.tex`'s "block-rank addition" (task 2.16) follows it. Task 2.16 gives
  `F-050`'s molecular-induction edges a sentence each, as task 2.7 did for this chapter's.
- **What `deficiency.tex` now fixes (tasks 2.8–2.10).** Its subsections run: $M(\tilde G)$, the
  deficiency and $k$-dof-graphs; KT eq. (2.4) (`sec:molecular-deficiency-bridge`, moved second);
  rigid subgraphs and KT's §3 lemmas. Notation: $d_G(P)$ (`def:D-deficiency`), $\delta_G(V')$ and
  $d_G(V')$ (`def:cut-edges-2ec`), $\operatorname{def}_d(G)$ at dimension $d$, $G[X]$ and
  $\tilde G[X] = (D-1)\cdot G[X]$, $\tilde e$, "the set of the $D-1$ copies of $e$" (`def:k-dof`;
  "edge-fiber" and "fiber" go), the "value" of a partition, $M(\tilde G)\,|\,E(\tilde H)$,
  $\operatorname{def}(\tilde G; u, v)$, and the *corank* $D(|V(G)|-1) - \operatorname{rank}
  M(\tilde G)$ (the subsection's opening). It says *vertices* of a multigraph, as KT do. Partitions
  as labelings are explained once, in `fmlnote:partition-labeling`: `\cref` it. "Boundary-regime
  cleanliness (`\cref{def:matroid-MG}`)" (line 77) becomes the independence criterion (`F-072`).
  KT eq. (2.4) is `\cref{thm:def-eq-corank}`, credited as `F-081` says;
  `lem:deficiency-zero-iff-tree-packing` is KT Proposition 2.2 at $\tilde G$.
- **What `molecular-induction.tex` now fixes (task 2.11).** Its first subsection (*Circuits and
  the contraction of a rigid subgraph*) proves KT Lemma 3.4 in full and defines the contraction
  $G/E(H)$ of a subgraph $H$ to a vertex $r$ (`def:rigid-contraction`, moved there); KT Lemma 3.5
  is proved for the matroid contraction $M(\tilde G)/E(\tilde H)$ (Oxley §3.1, Proposition 3.1.6,
  Corollary 3.1.8), and the graph form is `lem:rigidContract-isMinimalKDof`'s, in Case I
  (`F-084`). The second (*Removal, splitting off and edge-splitting*) has `def:graph-operations`
  with KT's $G_v$, $G_v^{ab}$, $H_{ab}^v$ and pages; `fmlnote:graph-operations` explains the edge
  labels (the label $e_0$ of the new edge, `rem:fresh-edge-supply`) and the *endpoint choice*,
  which `lem:case-cut-edge-realization-gp` (task 2.16) and `case-i.tex` cite at
  `def:graph-operations`. The chapter's opening (task 2.17) still calls the first subsection
  inherited lemmas and the second the graph operations.
- **What the subsection on KT Lemmas 4.1 and 4.2 now fixes (tasks 2.12, 2.13).** Its opening
  fixes $v$, $e_a = va$, $e_b = vb$ ($a, b \neq v$), $\tilde e$, $\widetilde{ab}$ and "incident
  with $v$" ("$v$-fiber" goes); forests are `body-bar.tex`'s, a family is $F_1, \dots, F_D$ (KT's
  indexing), a copy is $(e, i)$ (`def:edge-multiply`). `rem:kt-lemma-41` defines *balanced at $v$*
  and gives its three points once: (3) says the deficiency bounds of KT Lemmas 4.3(i) and 4.4
  compare partition values, without KT eq. (2.4), and the surgery gives KT Lemma 4.3(ii), used in
  Cases II and III (the chapter's opening, task 2.17, says it never enters). The surgery needs
  $a \neq b$. `lem:edge-splitting` has KT's cases (i) $h' < D - 1$ and (ii) $h' = D - 1$. The
  ledger's KT 4.1 entry says (3) "through def = corank": task 3 aligns it.
- **What the subsection on KT Lemmas 4.3–4.8 now fixes (tasks 2.14, 2.15).** Its title is
  *Splitting off and removal: KT Lemmas 4.3–4.8*, and its opening sketches it. The deficiency
  bounds are KT 4.3(i) (`lem:splitoff-deficiency`, $D \ge 1$) and KT 4.4
  (`lem:removal-deficiency`, $D \ge 2$), together `lem:dof-tracking`. `rem:kt-lemma-44` follows
  the lemma's proof; the ledger's KT 4.4 entry says it "spells out the partition-count
  comparison": task 3 aligns it. The paragraph before `lem:no-rigid-edge-count` shows once that a
  minimal $k$-dof-graph has no loops (KT's multigraphs have none, KT §2.5): task 2.16's
  `lem:simple-minimal-noRigid` can point there. `lem:no-rigid-edge-count` is KT 4.5(i) for every
  $k$. `lem:low-degree-vertex` and `lem:reducible-vertex` are "from the proof of KT Lemma 4.6";
  the lead-in before them states KT 4.6 with KT's $d$ and a chain $v_0 v_1 \dots v_d$, proved for
  $k = 0$ in `lem:chain-cycle-dichotomy` (task 2.17 aligns its $n$). `lem:reduction-step` is (i) KT
  4.8(i) for $D \ge 2$ and (ii) KT 3.5's matroid form at $k = 0$; the prose after it gives the
  fewer vertices and the graph form, which `thm:minimal-kdof-reduction` (task 2.16) uses. Proofs
  write $G' = G_v^{ab}$, $G_v = G - v$ and "the fundamental circuit of $f$ with respect to $B$".
  The ledger's `lem:reduction-step` entry quotes "a rank count replaces KT's iterated
  fundamental-circuit swap", now "We replace this exchange by the count above": task 3 aligns it.
- **From task 2.4.** `meet.tex` (its opening and two nodes) cites `sec:molecular-homog` for the
  exterior algebra and the join, which are in `sec:molecular-extensor`: task 2.18 repoints them.
  `def:extensor` writes $v_1 \wedge \cdots \wedge v_j$, and $\vee$ arrives with `def:join`. The
  facts other nodes cite are in the prose after `def:extensor`, `def:join` (Barnabei–Brini–Rota's
  Propositions 3.4 and 3.5) and `def:affine-subspace-extensor`.
- **The open's findings** are recorded, not acted on.
- **Tools.** The three screens under *Scope*; `scripts/blueprint-deps.py --chapter <name>` for what
  pins reach. The ledger's next ID is `F-098`.

## Decisions made during this round

- **The slicing** (the open): eighteen slices, cut at subsection boundaries or where the argument
  turns; `body-hinge.tex` rides with `body-bar.tex`'s second slice; `deficiency.tex` splits at
  `lem:deficiency-cut-vertex`; mean 266 lines.
- **One notation for the body count** (the open's call). The chapters wrote Tay and Whiteley's $n$
  and $d = n(n+1)/2$ (`body-bar`; Whiteley 1988, Tay 1984), a second name $\delta = d$
  (`body-hinge`), and KT's $d$ and $D = \binom{d+1}{2}$ (`extensor` on). The round writes KT's $d$
  and $D$ throughout; task 2.3 says once that Tay and Whiteley write $n$ and $d$, and the Lean's
  `bodyBarDim n` gets a formalization note. A slice that keeps a source's letters records why here.
- **The crux list, by label** (the open): `rigidity-matrix.tex` has no crux node (its ledger entry,
  `prop:rigidity-matrix-prop11`, is in round 3's `panel-layer.tex`), so three chapters have them.
- **The no-Lean-edit base** is `ac7bd966`, the open's parent.
- **Tasks 2.1–2.10** (detail in each commit): nodes move only for node order; statements say what
  their pins prove ($D \ge 1$, $V \neq \emptyset$, …) or keep their strength with a note (`F-048`,
  `F-049`, `F-070`, `F-079`); KT's order (`F-071`); "boundary regime" goes (`F-072`); eq. (2.4) is
  credited to KT and JJ Theorem 4.1(a) (`F-081`); partitions in proofs, labelings in notes; the
  cycle matroid has no symbol.
- **Tasks 2.11–2.14, `molecular-induction.tex` 43–1032** (detail in each commit):
  `def:rigid-contraction` and `rem:kt-lemma-44` moved (node order; principle F); statements say
  what their pins prove (`F-083`, `F-084`) or keep a degree two their pins drop (`F-086`); KT's
  order and KT's (i)/(ii) of Lemma 4.2; the `F-090` and `F-091` nodes stay; the pencil variants
  state their constructions in words, with a note each on $e_0$.
- **Task 2.15, `molecular-induction.tex` 1033–1308.** `lem:reduction-step` states its pins: (i) KT
  4.8(i) for $D \ge 2$, (ii) KT 3.5's matroid form at $k = 0$, the graph form after it (`F-084`,
  as task 2.11 did). `lem:reduction-step-pos`'s step 3 was not its pin's: the proof now gives KT
  4.3(i)'s minimality clause as the pin does (KT 4.7 for $ab$, KT 4.3(ii) and 4.2(ii) otherwise),
  and the square $K_v^{ab} = H$ is step 2's. `lem:no-rigid-edge-count` states its pin's
  $V \neq \emptyset$. No node moved: KT 4.6's pair stays after KT 4.7's node, as at the open.
