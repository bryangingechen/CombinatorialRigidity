# PROSE round 2/5 — `prose-molecular`, body-bar, body-hinge and the molecular foundations (work log)

**Status:** in progress (opened 2026-10-08). Round 2 of **PROSE**'s five rounds; their plan and the
PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round rewrites the prose of the eight chapters `matroid-union.tex` →
`meet.tex` to `40-exposition`'s register and round 1's exemplar. Every `\label`, pin, `\leanok`,
`\uses` edge and statement strength stays as it is. What else the round notices goes to the ledger
`notes/Prose-findings.md`: the open recorded `F-048`–`F-050`, tasks 2.1–2.6 `F-051`–`F-065`. 20
one-commit tasks; tasks 1 and 2.1–2.6 are done, and the round has no planned stop. **Next concrete
task:** task 2.7, `rigidity-matrix.tex` 830–1108 and 1–51, at Opus (*Lemma checklist*). Round
manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. No entries yet.

## Current state

**Task 2.6 has landed** (this commit): `rigidity-matrix.tex` 478–739 (now 478–829), the first 8
nodes of the subsection now titled *Rank-addition lemmas*, and `lem:span-rigidityRows-eq-of-motions-eq`,
moved up from task 2.7's range. Every `\label`, `\lean{…}`, `\leanok` and `\uses` is
byte-identical. Outside the slice, the opening's "a vertex cut (KT Lemma 6.1" now reads "a cut
edge". Nothing is mid-stream; task 2.7 is next.
- **Gates at this commit**, all the open's values: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, 9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and
  `b53eb8b1cf78cb06`; `print.log` 0 `LaTeX Warning` lines (96 overfull boxes, 98 at the
  parent; none in the slice). Screens: `rigidity-matrix` register 8 (9 at the parent), devices
  0 / 0 (0 / 1); cross-chapter forward `\uses` 14, unchanged.

**Verified at the open** (2026-10-08, at `ac7bd966`; task 1, docs only):
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines (re-run here, all
  cached; the coordinator's run gave the same). The axioms check does not run at this open
  (`notes/Prose.md` §2: round 1's open and round 5's close only).
- **The no-Lean-edit base is `ac7bd966`**, the open's parent: the close checks that `git diff
  --stat ac7bd966.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` is
  empty.
- **The round's gate values**, round 1's close reproduced exactly (the blueprint has not changed
  since). Every slice must reproduce them:
  - `blueprint/lint.sh` green. `blueprint/verify.sh` green (38 s): `checkdecls` silent, and **9**
    `WARNING:` lines, all plasTeX package and renderer notices.
  - `blueprint/print/print.log`: **0** `LaTeX Warning` lines; **120** overfull boxes, counted at
    the open and close but not gated (`latexmk` found the PDF up to date).
  - The built graph: **657** nodes and **1 292** edges, fingerprint **`673e3178d1b3145e`**; pin
    hash **`b53eb8b1cf78cb06`** (`blueprint/lean_decls`: 1 030 pins, 1 020 distinct names). The
    commands are under *Scope*, gate 3.
- **The surface**, as `notes/Prose.md` §3 has it: 8 files, 4 792 lines, 151 nodes, 273 pins. Seven
  nodes have four or more pins (§7; `F-009`): `def:rigidity-matrix` (14),
  `lem:case-III-claim612-line-in-panel-union` (12), `lem:trivial-motions-rank-bound` (9),
  `def:cut-edges-2ec` and `lem:cut-edge-decomposition` (7 each), `lem:two-vertex-trichotomy` and
  `def:graph-operations` (4 each).
- In the graph, 148 of the 151 nodes are green and filled. `def:dof-generic`, `def:induced-span`
  and `lem:forest-surgery-unsplit` are blue (`F-008`).
- **The crux nodes, by label:** three chapters have them, not the four round 1's hand-off counted;
  the list is under *Scope*, and *Decisions* says why.
- **The open's findings:** `F-048` and `F-049` (S, *Candidates for the PI*) and `F-050` (N, *Moved
  to a later round*).

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

- **Done:** `matroid-union` (task 2.1), `body-bar` (tasks 2.2, 2.3), `body-hinge` (task 2.3) and
  `extensor` (task 2.4); their open bullets are in this log at `ea058ba8`, `6c26eed5`, `7fe65223`
  and `53ec36db`.
- **`rigidity-matrix`** (phase 18, extended through phase 40).
  - *2.5, 2.6:* done; their open bullets are in this log at `47eb5225` and `5399e053`.
  - *2.7:* the contraction-leg lemmas of Case I and the pencil chapters carry Lean in statements
    (`\operatorname{extProj}`, `\operatorname{ofNormals}`, "relabel selector", "parent selector").
    "Splice" is in `lem:rigidityRows-splice-rank-add`'s title (the open's *2.6* item named it; the
    node is in this range).
    `lem:rank-polynomial-IH-relabel` is superseded and stays (`blueprint/CLAUDE.md`, the
    supersession gate). The opening (1–51) is long and describes Proposition 1.1's halves:
    KT's Proposition 1.1 (p. 648) is Tay's and Whiteley's tree-packing characterization, and
    `prop:rigidity-matrix-prop11` (round 3) its rank form; check how both chapters name it.
    Ten `\uses` point forward (`F-050`): each gets a sentence.
- **`deficiency`** (phase 19). `def:matroid-MG` cites `thm:tay-witness` for Tutte–Nash-Williams and
  "the tree-packing chapter", and has a proof whose "boundary regime" and "boundary-regime
  cleanliness" recur in three proofs (principle E: define or drop). `def:D-deficiency`'s statement
  carries the labeling $f \colon V \to V$ (a formalization note) and "genuinely signed".
  `lem:deficiency-antitone` writes the deficiency "at $m$" and $\operatorname{def}_3$,
  $\operatorname{def}_2$. Statements carry role clauses: `def:rigid-subgraph` (why $|V(H)| \ge 2$,
  the circuit definition, Case III), `lem:cut-edge-decomposition` ("Packaged for the reduction
  principle", a `theorem` with a `lem:` label, 7 pins), `lem:minimal-kdof-spanning-subgraph`;
  `def:cut-edges-2ec` bundles a definition, a transfer lemma and a corollary (`F-009`).
  `\operatorname{bodyBarDim}` in three statements. `lem:two-vertex-trichotomy`'s proof cites a
  "parallel-pair criterion" of `def:k-dof` that is `lem:two-vertex-zero-dof`, a later chapter's.
  Check `thm:def-eq-corank`'s credit, "the project framing of … Jackson–Jordán Theorem 6.1",
  against JJ 2009 in `.refs/`. The paragraph after it repeats the opening ("wires", "routes").
- **`molecular-induction`** (phase 20, extended through phase 40; the most crux nodes).
  - *Throughout:* "No graph↔matroid correspondence is needed" three times; the fresh edge
    $e_0 \notin E(G)$ in five statements (principle D's canonical case for one labeled remark);
    Lean names in proofs (`Graph.loopless_of_isMinimalKDof`, `Graph.deficiency_nonneg`,
    `induce_insert_splitOff`, `collapseTo`); `\operatorname{def}(G)` beside
    `\operatorname{def}(\tilde G)`.
  - *2.11:* `def:induced-span` (no pin) names `Graph.fiberSpan`, `Graph.inducedSpan`,
    `Graph.induce`; `def:graph-operations` puts the endpoint selector `ends` ("a genuine link …,
    junk off $E(G)$") in a statement (principle E's own example; `endsOf` is `F-010`'s).
  - *2.12–2.13:* connective paragraphs after seven nodes (423–681) restate the remark's verdicts
    ("a gap, not an error"): once, in `rem:kt-lemma-41`. The remark and 676–690 call
    edge-splitting "deferred" and "unformalized" beside the formalized `lem:edge-splitting`:
    reconcile. `cor:forest-surgery-deficiency` repeats `lem:forest-surgery-split`'s conclusion
    (check its pin). `lem:edge-splitting` has `eₐ` (a Unicode subscript in the source, as in
    2.14's `lem:splitoff-deficiency`), `\operatorname{edgeFiber} e_0\, n`, "survivor conjunct"
    and `(eₐ, r.2)`.
  - *2.14–2.15:* *To check:* `lem:reduction-step-pos`'s step 3 shows "$\operatorname{def}(H) <
    k-1$" for a proper subgraph, where minimality wants the deficiency to rise: read the pin.
    `lem:reduction-measure`'s statement says "the genuine requirement".
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
  - [x] **2.1 `matroid-union.tex`** (`6c26eed5`; now 1–306, 9 nodes). Found `F-051`–`F-053`.
  - [x] **2.2 `body-bar.tex`, the prerequisites and the $k$-frame matroid** (`7fe65223`; now
    42–452, 14 nodes, with the two moved up from *Tree-packing*). Found `F-054`, `F-055`.
  - [x] **2.3 `body-bar.tex`'s rest and opening, and all of `body-hinge.tex`** (`53ec36db`; now
    `body-bar` 1–48 and 460–721, `body-hinge` 1–165; 13 nodes). Applied the round's notation
    (*Decisions*). Found `F-056`–`F-058`.
  - [x] **2.4 `extensor.tex`** (`47eb5225`; now 1–298, 7 nodes; crux `lem:extensor-independence`
    at full depth). Also the coordinator's scope-pin correction to task 2.3: `body-hinge.tex`'s
    last sentence now says we prove the simple-graph case of KT Conjecture 1.2. Found `F-059`,
    `F-060`.
  - [x] **2.5 `rigidity-matrix.tex`, the matrix and KT's rank lemmas** (`5399e053`; now 52–477, 9
    nodes). Found `F-061`–`F-063`.
  - [x] **2.6 `rigidity-matrix.tex`, rank addition at cuts, 2-cuts, paths and ears** (this commit;
    now 478–829, 9 nodes with `lem:span-rigidityRows-eq-of-motions-eq` moved in). Found `F-064`,
    `F-065`.
  - [ ] **2.7 `rigidity-matrix.tex`, the contraction-leg lemmas and the opening** (600–901 at the
    open, now 830–1108; and 1–51): 8 nodes, 330 lines.
  - [ ] **2.8 `deficiency.tex`, the matroid, the deficiency and the cut lemmas** (27–271): 9 nodes,
    245 lines.
  - [ ] **2.9 `deficiency.tex`, cut vertices, ears, restriction and minimality** (272–523): 9
    nodes, 252 lines.
  - [ ] **2.10 `deficiency.tex`, the corank bridge and the opening** (524–712, 1–26): 5 nodes, 215
    lines.
  - [ ] **2.11 `molecular-induction.tex`, inherited lemmas and graph operations** (43–260): 9
    nodes, 218 lines.
  - [ ] **2.12 `molecular-induction.tex`, KT Lemma 4.1 and the balanced packing** (261–516):
    `rem:kt-lemma-41`, its example and 5 nodes, 256 lines; crux throughout.
  - [ ] **2.13 `molecular-induction.tex`, the reroute, the surgery and edge-splitting** (517–802):
    9 nodes, 286 lines.
  - [ ] **2.14 `molecular-induction.tex`, splitting-off and removal by deficiency counting**
    (803–1032): `rem:kt-lemma-44` and 5 nodes, 230 lines.
  - [ ] **2.15 `molecular-induction.tex`, the criteria, the degree-2 vertex and the reduction
    step** (1033–1308): 9 nodes, 276 lines.
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

## Blockers / open questions

- None. The round has no planned stop.

## Hand-off / next phase

**Next concrete task: task 2.7, `rigidity-matrix.tex`, the contraction-leg lemmas and the opening
(830–1108 and 1–51; 600–901 at the open), at Opus**, a fresh agent (`notes/Prose.md` §2). Its
diagnosis is the *2.7* item of the `rigidity-matrix` bullet under *Per-chapter diagnosis*, its gates
and screens under *Scope*. Then tasks 2.8–2.18 in order, and task 3 closes the round. For the
slices:
- **The PI's check** (round 1's Stop 1, item 5: "the overriding goal is to make sure the result is
  understandable"): the coordinator has read tasks 2.1–2.3 in full against the exemplars.
- **Notation.** Task 2.3 applied *Decisions*' notation call to `body-bar` and `body-hinge`, and
  removed the "$D = \delta$" crosswalks and every $\delta$ from the round's other chapters. Tasks
  2.7–2.18 write KT's $d$ and $D$, drop the stray $n$, and point at `body-hinge`'s $\tilde G$.
- **Crux nodes** keep their full proofs, in tasks 2.12–2.15, 2.17 and 2.18 (*Scope*).
- **From tasks 2.1–2.3.** `body-bar.tex` writes bodies in $\R^d$, $D = \binom{d+1}{2}$, a vector
  $b_e \in \R^D$ per bar (Tay's model; Whiteley's bars are lines), and the row of a bar as
  $-\sum_c (b_e)_c\, a_e^{(c)}$, the $D$-frame row at $b$ up to sign; "isostatic" is defined in
  prose. `thm:tutte-nash-williams` is now *Decomposition into forests*, credited as Whiteley
  credits it (Tutte, Nash-Williams 1961 and 1964; `nashWilliams1964` is new in the bibliography).
  `body-hinge.tex` writes $(D-1)\cdot G$ and KT's $\tilde G$; `def:body-hinge-framework`'s
  formalization note says the Lean records bar bundles (`F-048`) and points at
  `cor:bodyhinge-generic-tree-packing`. `F-053` lists the credits left in tasks 2.10–2.12.
- **From task 2.4.** `def:extensor` writes the product $v_1 \wedge \cdots \wedge v_j$, and $\vee$
  arrives with `def:join`, as KT write it. Facts other nodes cite live in the prose after a
  definition: after `def:extensor`, multilinearity, alternation and "nonzero iff linearly
  independent"; after `def:join`, the concatenation identity and Barnabei–Brini–Rota's
  Propositions 3.4 and 3.5; after `def:affine-subspace-extensor`, $C(p_1, \dots, p_k) \ne 0$ iff
  affinely independent, and $C(U)$ determined by $U$ up to a scalar and determining $U$.
  `rigidity-matrix.tex` (its opening) and `meet.tex` (its opening and two nodes) cite
  `sec:molecular-homog` for the exterior algebra and the join, which are in
  `sec:molecular-extensor`: tasks 2.7 and 2.18 repoint them.
- **From task 2.5.** The screw space $\bigwedge^{d-1}K^{d+1}$ is identified with $K^D$ before
  `def:hinge-row-block`, whose rows are, through the dot product, the linear forms vanishing on
  $C(p(e))$; $\operatorname{rank} R(G,p) = D|V| - \dim Z(G,p)$ is stated after
  `def:rigidity-matrix`. Formalization notes: at `def:hinge-constraint`, the Lean records an
  extensor $C(e)$ per edge label, possibly zero, on a fixed body set, with $d = k + 1$; at
  `def:rigidity-matrix`, the rows are linear forms $S \mapsto r(S(u) - S(v))$. "Realization" is
  defined before `def:dof-generic`, the deficiency recalled before
  `lem:trivial-motions-rank-bound`, $\operatorname{pinned}(v)$ (round 3's notation) in
  `lem:rank-delete-vertex`, and "panel" in *Rank lemmas*' opening paragraph.
  `lem:rank-parallel-full` assumes linearly independent extensors (was "general position").
  For task 2.7's opening: it now repeats both subsections' orienting paragraphs (principle F,
  *Once*), and its "lower-bound half of Tay–Whiteley's Proposition 1.1" is the rank bound of
  `prop:rigidity-matrix-prop11`, Jackson and Jordán's formula.
- **From task 2.6.** The subsection is now *Rank-addition lemmas*. Its orienting paragraph already
  sketches task 2.7's lemmas (contracting a rigid subgraph, KT Lemma 6.2; restoring a body of degree
  two after splitting off, KT Lemmas 6.8 and 6.10), so task 2.7 adds only a lead-in before
  `lem:block-rank-contract`. A notation paragraph fixes the subgraph convention ($R(H,p)$, $Z(H,p)$
  with $p$'s hinges and $G$'s bodies), the row space as a span of linear forms, and $G[V_1]$; the
  proofs write row spaces $\mathcal R$. `lem:span-rigidityRows-eq-of-motions-eq` now sits before
  `lem:block-rank-cut-vertex`. `lem:block-rank-cut` is titled for a cut edge, not a vertex cut: the
  opening (task 2.7) and `molecular-induction.tex`'s "block-rank addition" (task 2.16) follow it.
- **The open's findings** are recorded, not acted on. Tasks 2.7 and 2.16 give `F-050`'s forward
  references a sentence each (task 2.6's range had none).
- **Tools.** The three screens under *Scope*; `scripts/blueprint-deps.py --chapter <name>` for what
  pins reach. The ledger's next ID is `F-066`.

## Decisions made during this round

- **The slicing** (the open). Eighteen slices from §3's provisional nineteen, cut at subsection
  boundaries where those fall in range and otherwise at the node where the argument turns.
  `body-hinge.tex` (144 lines) rides with `body-bar.tex`'s second slice, which shares its theorem,
  its existence-form paragraphs and its notation, as `laman.tex` rode with `sparsity.tex`.
  `deficiency.tex` splits its 405-line *Rigid subgraphs* subsection at `lem:deficiency-cut-vertex`,
  not §3's 92-line first slice. `molecular-induction.tex` keeps §3's seven, splitting after the
  balanced-packing descent (516) and after `lem:dof-tracking` (1032). Mean 266 lines (round 1: 306).
- **One notation for the body count** (the open's call). The chapters write it three ways: Tay's
  and Whiteley's $n$ and $d = n(n+1)/2$ (`body-bar`; Whiteley 1988 and Tay 1984, `.refs/`), a
  second name $\delta = d$ (`body-hinge`), and KT's $d$ and $D = \binom{d+1}{2}$ (`extensor` on,
  with "$D = \delta$" crosswalks). The round writes KT's $d$ and $D$ throughout: later chapters
  already write $(D-1)\cdot G$ for `body-hinge`'s multiplied graph. Task 2.3 says once that Tay and
  Whiteley write $n$ and $d$; the Lean's `bodyBarDim n` gets a formalization note. A slice that
  keeps a source's letters records why here.
- **The crux list, by label** (the open). The done entry under the exposition ledger's
  `rigidity-matrix.tex` heading is `prop:rigidity-matrix-prop11`, whose node is in `panel-layer.tex`
  (round 3); so `rigidity-matrix.tex` has no crux node, and three of the round's chapters have
  them. `lem:case-III-claim612-line-in-panel-union` (`meet.tex`) has its done entry under the
  `algebraic-induction.tex` heading.
- **The no-Lean-edit base** is `ac7bd966`, the open's parent; the open touches no Lean.
- **Task 2.1, `matroid-union.tex`.** `def:matroid-union` states the Lean's construction (Perfect;
  Oxley Theorem 11.2.12), and the proofs follow Oxley §§11.1–11.3. The opening's credit paragraph,
  which `DESIGN.md` *Attribution / license* relies on, says the rank formula's stated forms are the
  project's. Load-bearing unpinned lemmas are named as addresses (`F-052`).
- **Task 2.2, `body-bar.tex` 42–452.** `def:graph-sparse` and `thm:unionPow-cycle-indep-iff-sparse`
  moved to the first subsection, now *Sparsity and the union of cycle matroids* (principle E, *Node
  order*). The cycle matroid gets no symbol: `deficiency.tex`'s $M(\tilde G)$ is KT's union of $D$
  copies of it. `lem:k-frame-specialize-forest` assumes $(k,k)$-sparsity, its pin's hypothesis.
- **Task 2.3, `body-bar.tex` 1–48 and 460–721, and `body-hinge.tex`.** `thm:tay-witness` moved after
  its proof's two `\uses`, `prop:tay-witness-exists` and `lem:tay-isSparse-of-independent`
  (principle E, *Node order*). A bar carries any vector of $\R^D$ (Tay 1984's model); after the
  theorem, Whiteley's p. 243 shows that the witnesses' bars are lines. The existence form is said
  once, in `body-bar`'s opening. `def:body-hinge-framework` keeps its hinges (`F-048`), with a
  formalization note on the bar bundles. The old closing paragraph had panel-hinge frameworks
  covered by `thm:body-hinge-tay`; it now states KT Conjecture 1.2. Glosses that needed other
  nodes (forests, spanning trees) left the statements for the prose after them.
- **Task 2.4, `extensor.tex`.** Statements now say what their pins prove. `def:homogeneous-coords`
  defines $\bar p$ alone; its sentence defining affine independence through $\bar p$ went, and the
  prose recalls the standard definition, the Lean's. `lem:affine-indep-iff` lost its join form, a
  forward gloss its pins do not prove; the prose after `def:affine-subspace-extensor`, whose pin
  proves it, states it (as tasks 2.2 and 2.3 moved glosses). The crux proof keeps the join on the
  left and the reordering bijection (the exposition ledger's verdict); $d = e + 1$ and the pins'
  roles are a formalization note. Scope pin: KT prove Conjecture 1.2 for multigraphs (p. 648), so
  `body-hinge.tex`'s last sentence now says we prove its simple-graph case.
- **Task 2.5, `rigidity-matrix.tex` 52–337.** `lem:rank-parallel-full` states its pin's hypothesis,
  linearly independent extensors, for the undefined "general position"; KT's distinct-hinges
  argument (p. 670) follows its proof, so the 22i verdict holds. `lem:rank-rotation-semicont` keeps
  its statement (`F-049`): in the blueprint's model the hinges are nonzero, so its span inclusion
  is an equality and its proof says so; a formalization note gives the pins' reversed inclusion.
  `lem:trivial-motions-rank-bound` now assumes $V \neq \emptyset$, its pins' ambient hypothesis.
  The row-independence prose after `def:rigidity-matrix` claimed any spanning forest; it now
  states the pins' hypothesis (`F-061`).
- **Task 2.6, `rigidity-matrix.tex` 478–739.** `lem:span-rigidityRows-eq-of-motions-eq` moved up
  from task 2.7's range to before `lem:block-rank-cut-vertex`, curing two forward `\uses`
  (principle E, *Node order*). `lem:block-rank-cut` keeps "nonempty proper" (its pins need neither;
  the excluded cases are trivial). It is credited as the rank step of KT Lemma 6.1's proof (p. 672):
  the old statement said it replaced KT's isometry argument, which places the panels. The 2-cut
  lemma's lead-in says why its sides are any subgraphs (the ear's path), so its proof lost its
  "no non-adjacency" remark. "Open ear" points at `sec:main-component-chain` (an ear there has
  $k \ge 1$ and covers $V(G)$) and is not defined here.
