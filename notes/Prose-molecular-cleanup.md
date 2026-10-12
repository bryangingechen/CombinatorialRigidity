# PROSE round 2/5 — `prose-molecular`, body-bar, body-hinge and the molecular foundations (work log)

**Status:** closed (opened 2026-10-08, closed 2026-10-12). Round 2 of **PROSE**'s five rounds; their
plan and the PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round rewrote the prose of the eight chapters
`matroid-union.tex` → `meet.tex` to `40-exposition`'s register and round 1's exemplar, in eighteen
slices. Every `\label`, pin, `\leanok`, `\uses` edge and statement strength is as it was. The ledger
`notes/Prose-findings.md` holds the round's 67 findings, `F-048`–`F-114`. All 20 one-commit tasks
are done. **Next concrete task:** round 3, `prose-algebraic`, opens (*Hand-off*). Round manual:
`CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. None has been filed.

### 2026-10-12 — the PI's review of `F-084` (named in the paused session's status; not a stop)

**PI, 2026-10-12:** (transcribed verbatim from the attended session that reviewed `F-084`)
"The plan you suggest sounds reasonable. However, I think there might still be value in pointing
out the divergences between blueprint and formal text that survived even after the formalization
was declared complete. Part of the purpose of this project is to learn what the limits of
autoformalization are and these give examples of things to look out for. We should perhaps do more
thinking about this at the end of round 5 though."

*The attended session's notes* (not the PI's words). The plan: keep both narrowings, since KT 3.5's
graph form is proved (`lem:rigidContract-isMinimalKDof`) and only Case I uses it; round 5 moves
that node after `lem:contraction-minimality` (`F-098`) and aligns `formalization.yaml` (`F-099`);
round 3 repoints `case-i.tex`'s citations. These and the second point are in `notes/Prose.md` §3.

## Current state

**The round is closed** (task 3, docs only). Nothing is mid-stream.
- **Gates at the close**, all the open's values: whole-project `lake build` green (2 996 jobs, 0
  `warning:`, 0 `error:`); `git diff --stat ac7bd966.. -- CombinatorialRigidity/ lakefile.toml
  lake-manifest.json lean-toolchain` empty; `lint.sh` green; `verify.sh` green, `checkdecls` silent,
  9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and `b53eb8b1cf78cb06`;
  `print.log` 0 `LaTeX Warning` lines and 72 overfull boxes (120 at the open). The axioms check is
  round 5's (`notes/Prose.md` §2).
- **The screens, beside the open's table** (*Per-chapter diagnosis*): register 0 in prose in all
  eight chapters (56 at the open; the script's 10 are `\label` and `\cref` targets of
  `genuine-hinge-realization` and `rigidityRows-splice-rank-add`, kept by the label rule); Lean
  devices 0 in statements (49) and 31 in the whole text (146), the rest parenthetical `\texttt`
  addresses in formalization notes; `\operatorname` Lean names 0 (34); cross-chapter forward `\uses`
  14, unchanged (`F-050`).
- **The findings check**, by script: each of `F-048`–`F-114` has exactly one line here (16 under
  *Candidates for the PI*, 51 under *Moved to a later round*), with the ledger's category, and every
  line here has an entry. The ledger's next ID is `F-115`.
- **The exposition ledger** (`notes/BlueprintExposition.md`): five entries aligned with the new text
  (KT 4.1's third point, KT 4.4, `lem:reduction-step`, KT 4.6's `d`, `def:meet-complement-iso`);
  the crux nodes, the Group-B 22i verdict, the `deficiency.tex` scan and the Phase-40c entry checked;
  a round note added. Result unchanged: 0 pending / 50 done / 1 closed as superseded.

**Verified at the open** (2026-10-08, at `ac7bd966`; task 1, docs only), the baselines the close matched:
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines. The axioms check
  runs only at round 1's open and round 5's close (`notes/Prose.md` §2).
- **The no-Lean-edit base is `ac7bd966`**, the open's parent (the close's check is under *Scope*).
- **The round's gate values**, round 1's close reproduced exactly: `lint.sh` green; `verify.sh`
  green (38 s), `checkdecls` silent, **9** `WARNING:` lines (plasTeX package and renderer notices);
  `print.log` **0** `LaTeX Warning` lines and **120** overfull boxes (counted, not gated); the
  built graph **657** nodes and **1 292** edges, fingerprint **`673e3178d1b3145e`**, pin hash
  **`b53eb8b1cf78cb06`** (1 030 pins, 1 020 distinct names; the commands are under *Scope*, gate 3).
- **The surface** (`notes/Prose.md` §3): 8 files, 4 792 lines, 151 nodes, 273 pins; seven nodes
  have four or more pins (`F-009`), and three are blue (`F-008`). The open's findings: `F-048`–`F-050`.

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
  their open bullets are in this log at the open, `ea058ba8`. `molecular-induction` (tasks
  2.11–2.17; its open items are in this log at `1b06def1`, `90051e3c`, `d9b0e96a`, `a2df0ed3` and
  `1d455ed9`) and `meet` (task 2.18; its open bullet is in this log at `d5db0e0c`).

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
slice at Opus, a fresh agent per task; the close may run at Sonnet (§2).

- [x] **1. O — the open** (`ea058ba8`; docs only): this log, the baselines, the open's findings
  `F-048`–`F-050`, and the status surfaces.
- [x] **2. The slices**, one commit each, in `main.tex` order, each chapter's opening in its last
  slice (principle F): 2.1 `6c26eed5`, 2.2 `7fe65223`, 2.3 `53ec36db`, 2.4 `47eb5225`, 2.5
  `5399e053`, 2.6 `af438fd1`, 2.7 `27daa953`, 2.8 `86b44e1b`, 2.9 `22317b88`, 2.10 `1b06def1`,
  2.11 `ce54bf15`, 2.12 `01aec968`, 2.13 `90051e3c`, 2.14 `d9b0e96a`, 2.15 `4bbd8cf0`, 2.16
  `1d455ed9`, 2.17 `d5db0e0c`, 2.18 `b8ef7c67` (`meet.tex`). Each commit message gives its
  ranges and findings (`F-051`–`F-097`, `F-100`–`F-114`).
- [x] **3. X — close the round** (this commit) (`CLEANUP.md` *Workflow* 5; docs only).
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
finding). Recorded, not acted on in this round (`F-084` is the one exception); round 5's report
ranks them for the PI.

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
- `F-084` (S, task 2.11): `lem:contraction-minimality` and `lem:reduction-step` claimed KT Lemma
  3.5's graph form; their pin proves the matroid form. **Acted on, the one exception:** tasks 2.11
  and 2.15 narrowed both to it, the graph form in prose after them. The PI kept this (2026-10-12).
- `F-086` (S, task 2.12): `lem:acyclic-insert-vfiber` and `lem:packing-move` assume that $v$ has
  degree two; their pins hold at every vertex.
- `F-101` (S, task 2.16): `thm:minimal-kdof-reduction` claims KT 4.9's sequence; its pin is the
  induction principle, from which the sequence follows with KT 3.5's graph form.
- `F-102` (S, task 2.16): `lem:case-cut-edge-realization-gp` assumes less than its pin, whose
  hypothesis also asks nondegenerate-hinge realizations, unused.
- `F-107` (S, task 2.17): `lem:chain-cycle-dichotomy` also said that both branches occur, which no
  pin states; the sentence moved to prose after the lemma (principle B), its claim kept, proved.
- `F-112` (S, task 2.18): `def:meet` also said that the meet supports the intersection; no
  declaration states a property of the meet. Moved to prose after it (principle B), kept, proved.
- `F-113` (S, task 2.18): `lem:complement-iso-decomposable-wedge-perp` covers both vectors of
  $n_1 \vee n_2$; two of its pins state only the first, and none assumes independence.

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
- `F-098` (N, the PI's review): move `lem:rigidContract-isMinimalKDof` after
  `lem:contraction-minimality`, once the vertex count pinned in `main-component.tex` is re-homed.
- `F-099` (U, the PI's review): `formalization.yaml` on `body_hinge_tay` (`F-048`), the union's rank
  formula (`F-051`, `F-053`) and KT eq. (2.4)'s credit (`F-081`).
- `F-100` (E, task 2.16): KT Theorem 4.9 to `lem:chain-data-of-noRigid` have edges their pins do
  not back, and miss `def:cut-edges-2ec` and three general-position nodes; no pin reaches KT 4.9's.
- `F-103` (N, task 2.16): the $d = 3$ pair `lem:adjacent-degree-two-pair` and
  `lem:chain-data-of-noRigid` is a dead route; only the second is marked superseded.
- `F-104` (L, task 2.16): an unused `_hV3` in KT Lemma 6.1's two pins, and stale docstrings on the
  pins of KT 4.9, KT 6.1 and the $d = 3$ pair.
- `F-105` (E, task 2.17): KT Lemma 4.6's nodes have edges their pins do not back, and the dichotomy
  misses `lem:deficiency-zero-connected`, `def:cut-edges-2ec` and `def:edge-multiply`.
- `F-106` (N, task 2.17): `def:cycle-data`'s third pin has no caller; a short cycle's deficiency,
  the dichotomy's third pin, is a load-bearing lemma with no node.
- `F-108` (L, task 2.17): derivable hypotheses in `chainData_extract`, unused ones in
  `chainWalk_charging`, a duplicated triangle count, and stale or misattributing docstrings.
- `F-109` (E, task 2.18): `meet.tex`'s edges without a Lean basis (among them the line lemma's to
  its two step lemmas), and missing ones; the line lemma's nine realization pins draw 20.
- `F-110` (N, task 2.18): the line lemma's twelve pins are the lemma, a $d = 3$ Case III
  realization and the bare-to-generic upgrade; the lemma's form for every $d$ has no node.
- `F-111` (N, task 2.18): `meet.tex`'s two step lemmas and `def:meet-pairing-dual` have no Lean
  caller; the steps the line lemma's proof takes, and the basis and contragredient laws, no node.
- `F-114` (L, task 2.18): `Meet.lean`'s header and docstrings promise absent lemmas, narrate
  phases and codes, describe retired routes, and misdescribe the panel normals.

## Blockers / open questions

- None. The round has no planned stop.

## Hand-off / next phase

**Next concrete task: round 3, `prose-algebraic`, opens** (`notes/Prose.md` §3 *Round 3*; `CLEANUP.md`
*Workflow* for the open, an Opus task that creates `notes/Prose-algebraic-cleanup.md`). Carry-ins:
round 3's are in `notes/Prose.md` §3 (the `\cref` repoints, `case-i.tex`'s citations and the `meet.tex`
notation item); round 5's are in the ledger `notes/Prose-findings.md`. The round-2 gate values above
are the baselines for round 3's open to re-verify. The ledger's next ID is `F-115`.

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
- **Tasks 2.11–2.17, `molecular-induction.tex`** (detail in each commit): `def:rigid-contraction`
  and `rem:kt-lemma-44` moved (node order; principle F); statements say what their pins prove
  (`F-083`, `F-084`) or keep a claim their pins do not make, with a note (`F-086`, `F-101`,
  `F-102`); an essentiality sentence leaves a statement for prose, its claim kept (`F-107`); KT's
  order and cases (Lemma 4.2's (i)/(ii), §6's four); looplessness is shown once, before
  `lem:no-rigid-edge-count`; `thm:minimal-kdof-reduction` states KT's sequence as (i) and its
  pin's principle as (ii); fresh labels and record detail go to notes. No node moved in 2.15–2.17.
- **Task 2.18, `meet.tex`** (detail in its commit): `def:meet` moved before the duality lemmas,
  whose titles and statements name the panel-meet (principle E); the meet's geometric reading left
  the definition for prose, kept and proved (`F-112`). The chapter writes $V = K^{d+1}$, $\vee$ for
  the join, $\wedge$ for the meet and $*$ for the complement isomorphism. The crux proof of
  `lem:case-III-claim612-line-in-panel-union` follows its pin's route (the line $\Omega$ cut out by
  the coordinate pairing); the $\bigwedge^2 W$ picture of its two step lemmas follows the proof.
  White 1994 is cited (bibliography entry checked against Crossref).
- **`F-084` kept** (the coordinator after task 2.15; the PI, 2026-10-12, *Autopilot: for the
  PI*). Not a precedent: from task 2.16 on, a statement claiming more than its pins is an `S`
  finding and keeps its claim. Adding the hypothesis a pin states for a degenerate case
  ($D \ge 1$, $V \neq \emptyset$) is anchoring.
