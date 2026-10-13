# PROSE round 3/5 — `prose-algebraic`, the algebraic induction (work log)

**Status:** closed (opened 2026-10-12, closed 2026-10-13). Round 3 of **PROSE**'s five rounds;
their plan and the PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the
authority for which rounds are done. The round rewrote the prose of the chapter
`algebraic-induction.tex` and its five sections, `panel-layer.tex` → `case-iii.tex`, to
`40-exposition`'s register and round 1's exemplar, in sixteen slices. Every `\label`, pin,
`\leanok` and `\uses` edge is as it was. Statements changed only in register and anchoring, and
where `notes/dispatch-log.md` records a hygiene-rule reading the coordinator accepted (2026-10-12
and 2026-10-13: tasks 2.7, 2.10 and 2.12–2.14); a statement that claims more or less than its pins
keeps its claim, with a note and an `S` finding. The ledger `notes/Prose-findings.md` holds the round's 59 findings,
`F-115`–`F-173`. All 18 one-commit tasks are done. **Next concrete task:** round 4,
`prose-applications`, opens (*Hand-off*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. No entries yet.

## Current state

**The round is closed** (task 3, docs only). Nothing is mid-stream.
- **Gates at the close**, all the open's values: whole-project `lake build` green (2 996 jobs, 0
  `warning:`, 0 `error:`); `git diff --stat ef57b401.. -- CombinatorialRigidity/ lakefile.toml
  lake-manifest.json lean-toolchain` empty; `lint.sh` green; `verify.sh` green, `checkdecls` silent,
  9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and `b53eb8b1cf78cb06`;
  `print.log` 0 `LaTeX Warning` lines and 51 overfull boxes (72 at the open). The axioms check is
  round 5's (`notes/Prose.md` §2).
- **The screens, beside the open's table** (*Per-chapter diagnosis*): 5 931 lines (4 221), 106
  nodes and 152 pins (unchanged). Register 0 in prose in all six files (66); the script's 67 hits in
  all the text (129) are `\label`, `\lean`, `\uses` and `\cref` arguments, kept by the label rule.
  Lean devices 0 in statements (10) and 8 in the whole text (30), all `\texttt` Lean names;
  `\operatorname` Lean names 0 (1); vocabulary 23 (217), each "endpoint selector" in a formalization
  note. Forward `\uses` to later sections 18 at 10 nodes, unchanged; to later nodes of the same
  file 6 at 4 nodes (12 at 7), after the moves of tasks 2.10 and 2.14 (`F-119`).
- **The findings check**, by script: each of `F-115`–`F-173` has exactly one line here, with the
  ledger's category and the task of its *Found:* line (21 under *Candidates for the PI*: 20 `S`,
  1 `M`; 38 under *Moved to a later round*: 8 `E`, 13 `N`, 15 `L`, 1 `T`, 1 `U`), and every line
  here has an entry. The ledger's next ID is `F-174`.
- **The exposition ledger** (`notes/BlueprintExposition.md`): every pointer into these files
  checked against the new text; five entries aligned (`prop:rigidity-matrix-prop11` names KT
  Proposition 2.3; the N6-composer and conditioned-motive quotations; Claim 6.4's four steps; the
  general-`d` entry's R2 note); a round note added, with the crux proofs and texts that tasks 2.3,
  2.8 and 2.10–2.15 corrected. Result unchanged: 0 pending / 50 done / 1 closed as superseded.

**Verified at the open** (2026-10-12, at `ef57b401`; task 1, docs only), the baselines the close
matched:
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines. The axioms
  check does not run at the open (`notes/Prose.md` §2: round 1's open and round 5's close only).
- **The no-Lean-edit base is `ef57b401`**, the open's parent: the close checks that `git diff
  --stat ef57b401.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` is
  empty.
- **The round's gate values**, round 2's close reproduced exactly; every slice reproduces them:
  `lint.sh` green; `verify.sh` green (38 s), `checkdecls` silent, **9** `WARNING:` lines (plasTeX
  package and renderer notices); `print.log` **0** `LaTeX Warning` lines (**72** overfull boxes,
  counted at the open and close, not gated); the built graph's **657** nodes and **1 292** edges,
  fingerprint **`673e3178d1b3145e`**, and the pin hash **`b53eb8b1cf78cb06`** (1 030 pins, 1 020
  distinct names; the commands under *Scope*, gate 3).
- **The surface** (`notes/Prose.md` §3): 6 files, 4 221 lines, 106 nodes, 152 pins, all green and
  filled, no title `superseded`; two nodes with four or more pins (§7; `F-009`); 48 nodes with
  every pin dead (`F-012`, `F-118`). The open's findings `F-115`–`F-120` are under *Candidates* and
  *Moved*.

## Scope and standing rules

From `notes/Prose.md` §2, restated only as far as a builder needs them.

- **Surface.** The chapter `algebraic-induction.tex` (its opening) and its five sections, in
  `\input` order: `panel-layer`, `case-i`, `case-ii`, `genericity-and-count`, `case-iii` (under
  `blueprint/src/chapter/algebraic-induction/`). No other chapter's TeX. A docs edit that keeps a
  pointer into these files true is in scope (`notes/BlueprintExposition.md`'s entries, below).
- **The hygiene rule.** The round does not change a headline statement or the strength of a
  blueprint statement. A finding that would need such a change becomes a ledger `S` entry and a
  line under *Candidates for the PI*. It is not acted on, and it is not a stop. As in round 2 from
  task 2.16 on, a statement that claims more than its pins keeps its claim, with a note; adding a
  hypothesis that a pin states for a degenerate case ($D \ge 1$, $V \ne \emptyset$) is anchoring.
- **Prose only (rounds 1–4), and no Lean edits (all five rounds).** `CombinatorialRigidity/`,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` stay untouched; the close checks that
  their `git diff --stat` since `ef57b401` is empty. Every node keeps its `\label`, its `\lean{…}`
  pins, its `\leanok` and its `\uses` edges. A statement block is edited for register and anchoring
  only. A node may move within its section file to cure a forward reference
  (`blueprint/AUTHORING.md` principle E, *Node order*); a reference to a later section gets a
  `\cref` and a sentence (`F-119` lists them); moving nodes between sections is round 5's. A graph
  or node-shape finding becomes a ledger `E` or `N` entry for round 5.
- **The register.** `blueprint/AUTHORING.md` principles A–F with their 2026-10-03 clauses, the
  2026-10-07 *Constructions* clause of B, and the PI's sentence before them ("the overriding goal
  is to make sure the result is understandable"); `40-exposition`'s exemplar
  `notes/Phase40-exposition-exemplar.md`; round 1's pinned sample `notes/Prose-exemplar.md`. No
  section is algorithmic, so principle A's carve-out does not apply. The reader is *Audience &
  vocabulary*'s rigidity theorist who knows KT 2011, and its dictionary binds: "genuine" is
  "nondegenerate"; brick, motive, producer, splice and carry go; extensors are "linearly
  independent", never "parallel". Labels keep their words (`def:genuine-hinge-realization`, the
  `-producer` lemmas), as in round 2.
- **Crux nodes** keep their full proofs (the crux carve-out, `AUTHORING.md` *Proof verbosity*); the
  rewrite changes their register, not their depth. These are the done entries of
  `notes/BlueprintExposition.md`, checked by label (most sit under its `algebraic-induction.tex`
  heading; the first under `rigidity-matrix.tex`'s):
  - `panel-layer` (2.1–2.3, done): `prop:rigidity-matrix-prop11` with `thm:theorem-55-6` (the two
    halves); `thm:theorem-55` and the simplicity account, since 2.2 the paragraph before it.
  - `case-i` (2.7, 2.8): `lem:case-I` (KT eq. (6.3)'s rank addition, since 2.7 in its proof);
    `lem:rigidContract-isMinimalKDof` (union against contraction); `lem:claim-6-4`; the passage after
    `lem:case-I-splice-seed` (the two body sets); the passage before `lem:case-I-realization`
    (contraction and simplicity); `lem:case-I-realization`; the passage after it (genericity against
    general position); `lem:case-I-dispatch` (the trifurcation; since 2.8 KT Claim 6.6, with $G'$
    induced, is in the proof of `lem:case-I-realization-h65`).
  - `case-ii` (2.9, done), with `genericity-and-count`'s `lem:case-II-realization-placement` (2.10,
    done): `lem:case-II-realization` (KT eq. (6.12)'s degenerate placement).
  - `case-iii` (2.11–2.15, done): Claim 6.11's chain `lem:case-III-claim-6-11-base`,
    `lem:case-III-gap3-minimalKDof`, `lem:case-III-nested-rank-lower`, `lem:case-III-claim-6-11`
    and the remark on KT footnote 6 (2.11); `lem:case-III-columnop`,
    `lem:case-III-candidate-row-construction`, `lem:case-III-candidate-row`; the $d = 3$ worked
    case's lead, `lem:case-III-claim612-p3-placement`, `lem:case-III-claim612-eq644`,
    `lem:case-III-claim612`, `lem:case-III-candidate-dispatch-d3`; the opening of *The case of
    general $d$* (the triangle floor and the chain), `lem:case-III-chain-discriminator`,
    `lem:case-III-chain-dispatch` and `lem:case-III` (also the Case-naming entry).

  `meet.tex`'s `lem:case-III-claim612-line-in-panel-union` is round 2's. Ledger notes also point
  here: the Phase-33 note at the opening's *Field generality* paragraph (2.16, done; its run-in
  heading stays, as ROADMAP §33 and `notes/Phase33.md` name it too), and the Phase-40a note at the
  $d \le 3$ of *The case of general $d$*'s opening and `lem:case-III`'s single degree-2 vertex
  (2.15, done).
- **Evidence.**
  - Citations meet `CLAUDE.md` *Referencing prior work*. `.refs/` has every source these files
    cite except Tay–Whiteley 1984 (`tayWhiteley1984`), which is cited as KT cite it (round 2, task
    2.3): KT 2011 (§5–§6 are pp. 667–698) and its arXiv version, Crapo–Whiteley 1982, Whiteley
    1988, 1996 and 1999, and Jackson–Jordán 2009. The commit that relies on a passage names it.
  - Claims about the Lean come from declarations' statements and bodies, never from docstrings,
    and from `scripts/blueprint-deps.py --label` or `--chapter <section>` for what a pin reaches.
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
  close re-runs them). The first script prints, per file with TeX comments stripped: principle-A
  register hits in all the text and in prose (`\lean`, `\uses`, `\label` and `\cref` arguments
  removed; "carries" is sometimes literal); Lean-device hits inside statement blocks and in the
  whole file; `\operatorname` Lean names (round 2 counted these without a command); and the
  dictionary's words and Lean-side devices that the device screen misses (`\mathrm{ends}`,
  `\mathrm{vtx}` and the like are not counted by it).
  ```sh
  python3 - blueprint/src/chapter/algebraic-induction/{panel-layer,case-i,case-ii,genericity-and-count,case-iii}.tex blueprint/src/chapter/algebraic-induction.tex <<'PY'
  import re,sys
  E=r'(definition|lemma|theorem|corollary|proposition)'
  A=re.compile(r'\b(feeds?|drives?|fires?|firing|threads?|carr(?:y|ies|ied)|wired?|wiring|routes?|spine|heart of|crucial(?:ly)?|remarkabl[ey]|brick|motive|producer|strat(?:um|a)|honest|genuine|re-?aim|splice|leaf-most)\b',re.I)
  D=re.compile(r'\\texttt\{|\\mathtt\{|\\mathrm\{(?:none|some|Option|Sym2|Fin|List|SimpleGraph|fromEdgeSet|maxBlock|decide|span)\}|\\mathrm\{[^}]*(?:[a-z][A-Z]|\.|\\_)[^}]*\}')
  O=re.compile(r'\\operatorname\{[^}]*(?:[a-z][A-Z]|\.|\\_)[^}]*\}')
  V=re.compile(r'\b(endpoint selector|link-recording|free-normal|seeds?|bare|conjuncts?|device|legs?|splice|glue|producers?|motives?|bricks?|rides?|carrier)\b',re.I)
  P=lambda s: re.sub(r'\\(lean|uses|label|[cC]ref)\{[^}]*\}','',s)
  for f in sys.argv[1:]:
      t=re.sub(r'(?<!\\)%.*','',open(f).read()); B=re.findall(r'\\begin\{'+E+r'\}(.*?)\\end\{\1\}',t,re.S)
      print(f.split('/')[-1][:-4], len(A.findall(t)), len(A.findall(P(t))), sum(len(D.findall(P(b))) for _,b in B), len(D.findall(P(t))), len(O.findall(P(t))), len(V.findall(P(t))))
  PY
  ```
  The second counts, per file, the `\uses` edges (node, target) of statement blocks whose target
  lies in a later chapter, in a later section of this chapter, or later in the same file, as
  edges/nodes (`F-119`); prose-only slices leave the first two at the open's values.
  ```sh
  python3 - <<'PY'
  import re
  R='blueprint/src/'; C=lambda f: f.split('/')[1].removesuffix('.tex')
  def ex(f): return sum(([g]+ex(g) for g in (m+'.tex'*(not m.endswith('.tex')) for m in re.findall(r'^\s*\\input\{([^}]*)\}',open(R+f).read(),re.M))),[])
  F=ex('chapter/main.tex'); T={f:re.sub(r'(?<!\\)%.*','',open(R+f).read()) for f in F}
  W={m.group(1):(i,m.start()) for i,f in enumerate(F) for m in re.finditer(r'\\label\{([^}]*)\}',T[f])}
  for f in [f for f in F if C(f)=='algebraic-induction']:
      i=F.index(f); X=[set(),set(),set()]
      for s in re.split(r'\\begin\{(?:definition|lemma|theorem|corollary|proposition)\}',T[f])[1:]:
          s=re.split(r'\\begin\{(?:remark|example|fmlnote)\}',s)[0]; n=re.search(r'\\label\{([^}]*)\}',s).group(1)
          for u in (u.strip() for x in re.findall(r'\\uses\{([^}]*)\}',s) for u in x.split(',')):
              j,p=W.get(u,(-1,0))
              k=0 if j>i and C(F[j])!=C(f) else 1 if j>i else 2 if j==i and p>W[n][1] else -1
              if k>=0: X[k].add((n,u))
      print(f.split('/')[-1][:-4],*(f'{len(x)}/{len({n for n,_ in x})}' for x in X))
  PY
  ```

## Per-chapter diagnosis

Seen at the open; line numbers are the open's, and the labels are the stable reference. Each slice
re-derives its own findings and records them in its commit and the ledger.

| File | Lines | Nodes | Pins | Register (all / prose) | Lean devices (statements / all) | `\operatorname` | Vocabulary | Forward `\uses` (section / file) | Tasks |
|---|---|---|---|---|---|---|---|---|---|
| `panel-layer` | 1 352 | 35 | 51 | 63 / 15 | 0 / 17 | 1 | 44 | 10 / 5 | 2.1–2.5 |
| `case-i` | 832 | 19 | 31 | 31 / 20 | 0 / 1 | 0 | 49 | 6 / 0 | 2.6–2.8 |
| `case-ii` | 173 | 4 | 8 | 1 / 1 | 0 / 0 | 0 | 3 | 2 / 0 | 2.9 |
| `genericity-and-count` | 387 | 11 | 14 | 9 / 9 | 1 / 1 | 0 | 29 | 0 / 5 | 2.10 |
| `case-iii` | 1 386 | 37 | 48 | 24 / 20 | 9 / 11 | 0 | 92 | 0 / 2 | 2.11–2.15 |
| `algebraic-induction` | 91 | 0 | 0 | 1 / 1 | 0 / 0 | 0 | 0 | 0 / 0 | 2.16 |
| **total** | 4 221 | 106 | 152 | 129 / 66 | 10 / 30 | 1 | 217 | 18 / 12 | |

No `\uses` edge points at a later chapter. The register's other 63 hits are label words; the
vocabulary column is mostly "seed" (89), "conjunct(s)", "bare", "device", "endpoint selector",
"leg(s)" and "free-normal". The sections (Phases 21–27) predate the 2026-10-03 clauses: three names
for the dimension, the Lean's realization record and role clauses in statements, route history
("see the git history" twice), and prose that cites dead nodes as steps of the induction (`F-118`).

**Carried in** (`notes/Prose.md` §3 *Round 3*; the ledger's `F-067`): all seven done, 1–3 and 5
by 2.7, 2.9 and 2.15; 4 and 7 by 2.16 (the opening cites `thm:minimal-kdof-reduction-all-k`,
checked with `scripts/blueprint-deps.py --label thm:theorem-55`, and names the rank formula KT
Proposition 2.3); 6, the notation of `meet.tex`, by every slice (*Decisions*).

- **`panel-layer` … `genericity-and-count`.** *Done:* 2.1–2.10 (their open bullets are in this
  log at `efa7ed2b`, the last at `120eca58`).
- **`case-iii`.** *Done:* 2.11–2.15 (their open bullets are in this log at `fe05a812`, `ba79d703`,
  `4502f035`, `9190873a` and `c3586784`).
- **`algebraic-induction.tex`.** *Done:* 2.16 (its open bullet is in this log at `889ebc08`).

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
slice at Opus, a fresh agent per task; the close may run at Sonnet (§2).

- [x] **1. O — the open** (`efa7ed2b`; docs only): this log, the baselines, the open's findings
  `F-115`–`F-120`, and the status surfaces.
- [x] **2. The slices**, one commit each, in `\input` order. Each section's own opening goes in its
  file's last slice and the chapter's opening last (principle F). The diagnosis of each is above;
  the carry-ins are numbered as there.
  - [x] **2.1–2.5 `panel-layer.tex`** (`db237dfd`, `5c65ea52`, `fd204aa5`, `708f4443`,
    `8cfa4531`): panel-hinge frameworks and KT Proposition 2.3; KT Theorem 5.5; KT Theorem 5.6 and
    the molecular conjecture; the base and the cycle normals; the operations and the multigraph
    conjecture. Found `F-121`–`F-133`.
  - [x] **2.6–2.8 `case-i.tex`** (`9a465598`, `85e0e4f8`, `5e9e329c`): KT Lemma 5.4 and the block
    pin; KT eq. (6.3), the contraction and KT Claim 6.4 (two nodes moved within the file); KT
    Lemmas 6.2, 6.3 and 6.5, and the opening. Found `F-134`–`F-144`.
  - [x] **2.9–2.10 `case-ii.tex`, `genericity-and-count.tex`** (`120eca58`, `fe05a812`): KT Lemma
    6.8 and putting back a body (carry-in 3); the rank at generic normals, the relative counts and
    KT eq. (6.12) at $k = 0$ (two nodes moved). Found `F-145`–`F-153`.
  - [x] **2.11–2.15 `case-iii.tex`: KT Claim 6.11, the row operations, the case $d = 3$ and the
    general case** (`ba79d703`, `e5f16b29`, `9190873a`, `eed7e7a5`, `889ebc08`; 1–1386, now
    1–2150): KT's three steps (pp. 684–685) and KT footnote 6; KT's row and column operations
    (pp. 685–686) at $(G, p_1)$ (KT eq. (6.12)); KT pp. 680–691 for $d = 3$, its points in
    homogeneous coordinates and the rotation of KT Lemma 5.2; KT pp. 692–698 for every $d$, with
    the triangle of KT Lemma 6.7(i) and KT eq. (6.66). Found `F-154`–`F-172`.
  - [x] **2.16 `algebraic-induction.tex`, the chapter's opening** (`c766f589`; 1–86, now 1–88):
    what is proved (KT Theorems 5.5 and 5.6, the molecular conjecture, KT Proposition 2.3's rank
    formula), the field, KT's induction and four cases (KT p. 671), and the order of the ten
    subsections; carry-ins 4 and 7. Found `F-173`.
- [x] **3. X — close the round** (this commit; `CLEANUP.md` *Workflow* 5; docs only).
  - *Gates:* whole-project `lake build` green; the no-Lean-edit check (`git diff --stat ef57b401..
    -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` empty). The axioms
    check runs at round 5's close, not here (§2).
  - *The blueprint:* `lint.sh` and `verify.sh` green, the invariance values the open's, the
    warning counts unchanged, overfull boxes counted; the two screens re-run beside the open's
    table.
  - *Findings:* every ledger entry the round found has its line here, and vice versa.
  - *The exposition ledger:* check the pointers into these files (*Scope*: crux nodes and notes;
    the KT eq. (6.3) entry's pointer to `lem:case-I`'s proof, the `prop:rigidity-matrix-prop11`
    entry's "KT Prop 1.1", the Claim 6.11 entry's remark) against the new text, and add a round
    note to `notes/BlueprintExposition.md`.
  - *Status surfaces:* the ROADMAP row reads ✓ Complete; ROADMAP's PROSE bullet and
    `notes/Prose.md`'s **Status** name round 4's open.
  - *The queue:* `prose-algebraic`'s row in `.claude/autopilot/queue.toml` gets `done = true`, and
    nothing else there changes.

## Candidates for the PI

`S` and `M` findings, one line each naming the ledger ID (`notes/Prose-findings.md` holds the
finding). Recorded, not acted on in this round; round 5's report ranks them for the PI.

- `F-115` (S, task 1): `lem:cycle-realization` states KT Lemma 5.4 for $3 \le m \le D$; its pin
  covers $m \le d + 1$, and its note said $m \le d$ (corrected by task 2.6).
- `F-116` (S, task 1): `lem:case-I` states KT eq. (6.3)'s rank addition through the contraction;
  its three pins are block-pin criteria that mention no contraction (kept by 2.7, with a note).
- `F-117` (S, task 1): `lem:genericity-device` states Zariski-open rank loci; its pins give one
  point attaining a bound that the given point already attains.
- `F-118` (M, task 1): the prose of Cases I–III presents as steps of the induction nodes that no
  main result's proof takes (the genericity device, Claim 6.4, the Case II accounting, the
  candidate completion, the relabel lemmas).
- `F-121` (S, task 2.1): `prop:rigidity-matrix-prop11` states the rank formula at a generic
  realization; its pin assumes the generic bound, and the formalization has no generic realization.
- `F-122` (S, task 2.1): the formal panel-hinge framework's endpoint selector is unconstrained, so
  `IsHingeCoplanar` is broader than KT's notion and the molecular conjecture's panel side states
  no link-recording condition.
- `F-124` (S, task 2.2): `lem:generic-yields-genuine-hinge` is stated for every multigraph; its pin
  assumes no loops.
- `F-125` (S, task 2.2): `cor:theorem-55-d3-spanning` states a generic realization with
  $\dim Z = D$; its pin's conclusion, a framework on $G$ with $\dim Z = D$, holds with welded hinges.
- `F-128` (S, task 2.3): the spanning forms of KT Theorem 5.6 (`thm:theorem-55-6`, its $d = 3$ case,
  the first pin of `thm:theorem-55-6-genuine`) state no selector condition; off $G'$ their hinges
  are those of a fixed pair of bodies.
- `F-136` (S, task 2.7): `lem:case-I-splice-seed` glues $H$ and the contraction, which is no
  subgraph of $G$; its pin glues two subgraphs, and no pin gives the step to the contraction.
- `F-137` (S, task 2.7): `lem:rows-polynomial-in-normals` states rows polynomial in the normals;
  its pin states none, and its conclusion already holds at the point it starts from.
- `F-138` (S, task 2.7): `lem:claim-6-4` states an open set of good normals; its pin gives one
  point, and assumes $G/E(H)$ simple, which the statement does not.
- `F-141` (S, task 2.8): `lem:case-I-realization-h65` omits KT Lemma 6.5's proper rigid subgraph
  and `lem:case-I-dispatch` the induction hypothesis, both assumed by their pins;
  `lem:case-I-realization` assumes two realizations where its pin assumes the induction hypothesis.
- `F-142` (S, task 2.8): `lem:case-I-realization-nonsimple` is stated for every $d \ge 2$; its pin
  is the case $d = 3$ of an unpinned general form.
- `F-145` (S, task 2.9): the panel assertion of `lem:case-II` holds vacuously for $d \ge 2$ (no
  framework meets its hypothesis, once called KT Claim 6.9's general position); its body assertion
  is weaker than its pin.
- `F-149` (S, task 2.10): `lem:genericity-device`, read with $R(G,q)$, fails at degenerate hinges
  (the weld raises the rank); its proof assumes nondegenerate hinges, and a remark gives the example.
- `F-150` (S, task 2.10): `lem:case-II-realization-placement` starts from a rigid $G_v^{ab}$; its
  pin from a rigid subgraph of $G$ avoiding $v$, which Cases II and III exclude.
- `F-154` (S, task 2.11): `lem:case-III-nested-rank-lower` omits $G$ simple and the induction
  hypothesis, both assumed by its pin; it fails for a $G$ that is not simple.
- `F-158` (S, task 2.12): `lem:case-III-candidate-row` states KT's rank bound at $(G, p_1)$; its pin
  is linear algebra on forms whose old block KT's bottom rows do not satisfy.
- `F-165` (S, task 2.14): the second and third frameworks' lemmas state KT's rank bounds; their pins
  are the linear algebra of the last step, and the graph-level counts have no node.
- `F-169` (S, task 2.15): `lem:case-III-chain-discriminator` claims less than its pin (no general
  position, no redundancy of KT eq. (6.52)), so it holds for any graph; the dispatch uses the rest.

## Moved to a later round

`E`, `N`, `T` and `U` findings for round 5, `prose-graph`, and `L` findings for a later Lean round,
one line each naming the ledger ID and the task that found it.

- `F-119` (N, task 1): 18 `\uses` edges at 10 nodes point at later sections of the chapter, and 12
  at 7 nodes at later nodes of their own section.
- `F-120` (N, task 1): two of the blueprint's ten doubly pinned declarations are round 3's; the
  $d = 3$ point choice's pins have no Lean caller.
- `F-123` (L, task 2.1): the docstrings of `PanelHinge.lean`'s first pins (the selector field,
  `rigidityMatrix_prop11`, the moment-curve constructions) misdescribe their bodies or callers.
- `F-126` (L, task 2.2): the docstrings of the KT Theorem 5.5 pins name a dead predicate as the
  induction's, misplace KT p. 670, and contradict a signature's comments; one binder is unused.
- `F-127` (T, task 2.2): `molecular-induction.tex` and `main-component.tex` write the extensor of
  vectors with $\wedge$, the meet's symbol since `meet.tex`.
- `F-129` (E, task 2.3): `thm:theorem-55-6` uses `lem:subgraph-minimality`; its step is
  `lem:minimal-kdof-spanning-subgraph`'s, which no `\uses` of it names.
- `F-130` (L, task 2.3): the docstrings of the KT Theorem 5.6 and molecular-conjecture pins: dropping
  the nonzero-hinge conjunct does not falsify the equivalence; a wrong node; "KT Prop 1.1".
- `F-131` (N, task 2.4): the base's three cases and `lem:extensor-pair-in-panel` pin dead $d = 3$
  wrappers; the general forms the induction calls have no node.
- `F-132` (L, task 2.4): the docstrings of the base's pins name wrong nodes, a hypothesis the
  theorem lacks, and stale callers.
- `F-133` (L, task 2.5): the docstrings of the framework operations' pins name Cases I and II as
  users, and dead or misdescribed callers; the multigraph pins' docstrings use process codes.
- `F-134` (N, task 2.6): six of `case-i.tex`'s first ten nodes have every pin dead and uncalled
  outside the node; one restates `lem:theorem-55-base`.
- `F-135` (L, task 2.6): the docstrings of the cycle and block-pin pins name dead routes (generic
  extensors for the cycle, Case I's gluing) and a binder the signature lacks.
- `F-139` (N, task 2.7): the pins of `lem:claim-6-4`, `lem:rows-polynomial-in-normals`,
  `lem:case-I-splice-seed` and two of `lem:case-I`'s are dead; the first restates a live lemma.
- `F-140` (L, task 2.7): the docstrings of the KT eq. (6.3) and Claim 6.4 pins misname Claim 6.4,
  their callers and a hypothesis; one pin's conclusion sits under three discarded hypotheses.
- `F-143` (N, task 2.8): the pin of `lem:case-I-realization-nonsimple` is dead; the Case I split for
  every $k$, KT Claim 6.6 and KT Lemma 6.3's combination step have no node.
- `F-144` (L, task 2.8): the docstrings of the last four Case I pins name a `case_I_dispatch` that
  does not exist and a wrong node; three `d = 3` wrappers have no caller.
- `F-146` (E, task 2.9): `case-ii.tex`'s 15 missing edges (`lem:reducible-vertex` among them) and
  its unbacked ones.
- `F-147` (N, task 2.9): `case-ii.tex`'s first three nodes are off the formal Case II, their pins
  dead; KT Lemma 6.7 has no node.
- `F-148` (L, task 2.9): the docstrings of the Case II pins say KT Claim 6.9 supplies a hypothesis
  that holds nowhere, and name wrong nodes and callers.
- `F-151` (E, task 2.10): `genericity-and-count.tex`'s missing edge, its 18 unbacked edges, and the
  nodes its new proofs cite without an edge.
- `F-152` (N, task 2.10): five of the file's nodes have every pin dead; two general lemmas are
  stated narrowly; the open-set form of `lem:genericity-device` is a later node.
- `F-153` (L, task 2.10): the docstrings of the file's pins credit KT Claim 6.9, a Gram determinant,
  the split-off for `Gv ≤ G`, and a node that does not exist.
- `F-155` (E, task 2.11): the Claim 6.11 group's 12 missing and 3 unbacked edges, and the nodes its
  new proofs cite without an edge.
- `F-156` (L, task 2.11): the docstrings of the Claim 6.11 pins call the KT eq. (6.22) step
  deferred, point at a retired remark and carry process codes.
- `F-157` (N, task 2.11): `lem:case-III-claim-6-11` is stated narrowly, and its live callers, which
  give KT eq. (6.18) and the corank $k'$, have no node.
- `F-159` (N, task 2.12): six of the nine nodes of KT eqs. (6.24)–(6.29) have every pin dead; the
  live path (KT's $(G, p_1)$, the rank bound in restriction form) has no node.
- `F-160` (E, task 2.12): the group's 11 missing and 14 unbacked edges, and the nodes its new proofs
  cite without an edge.
- `F-161` (L, task 2.12): the docstrings of the group's pins call eq. (6.43) the open crux, credit
  KT eqs. (6.26) and (6.16) wrongly, and lift a singular block; process codes.
- `F-162` (E, task 2.13): the span and point choice's 13 edges with no Lean basis, and the nodes its
  new proofs cite without an edge.
- `F-163` (N, task 2.13): six of its ten nodes have every pin dead; the live point choice
  (`exists_homogeneousIncidence_of_normals_gen`) has no node.
- `F-164` (L, task 2.13): the docstrings of its pins name a wrong node for five pins, call a green
  node red, and carry process codes.
- `F-166` (E, task 2.14): the three frameworks and Claim 6.12's 23 missing and 16 unbacked edges,
  and the nodes its new proofs cite without an edge.
- `F-167` (N, task 2.14): ten of its thirteen pins are dead; the formal $d = 3$ route (one theorem at
  three roles, the choice of $r$) has no node.
- `F-168` (L, task 2.14): the docstrings of its pins misname KT's splittings, a conjunct, a branch
  and a caller, and carry process codes.
- `F-170` (E, task 2.15): the general case's 24 missing and 13 unbacked edges, and the nodes its new
  proofs cite without an edge.
- `F-171` (N, task 2.15): the formal route of KT Lemma 6.13 (the choice of $q$, KT's $\rho_i$, KT eq.
  (6.66), the arm theorem) has no node; the triangle realization and the $d = 3$ pin are dead.
- `F-172` (L, task 2.15): the docstrings of its pins deny two pins, cite KT Lemma 6.10 and a wrong
  page, and carry process codes.
- `F-173` (U, task 2.16): `README.md` calls the algebraic induction the realization of KT Theorem
  4.9's reduction, and `formalization.yaml` names the rank formula KT Proposition 1.1.

## Blockers / open questions

- None. The round is closed.

## Hand-off / next phase

**Next concrete task: round 4, `prose-applications`, opens** (`notes/Prose.md` §3 *Round 4*;
`CLEANUP.md` *Workflow* for the open, an Opus task that creates
`notes/Prose-applications-cleanup.md`). Round 3 carries nothing into round 4: its findings wait in
the ledger `notes/Prose-findings.md` for round 5 (`E`, `N`, `T`, `U`), a later Lean round (`L`) and
the PI (`S`, `M`). The round-3 gate values above are the baselines for round 4's open to
re-verify. The ledger's next ID is `F-174`.

## Decisions made during this round

- **The slicing** (the open): §3's sixteen slices, numbered 2.1–2.16 (task 1 the open, task 3 the
  close), cut at subsections and at the node boundaries the checklist names; 91–387 lines.
- **One notation** (the open's call; carry-in 6). The sections write the dimension as $n$, $d$ and
  $k+1$, and $k$ is both the grade and the dof. The round writes KT's $d$, $D = \binom{d+1}{2}$,
  $K^{d+1}$, $\bigwedge^{d-1} K^{d+1}$, $\vee$ for the join, $\wedge$ for the meet, $*$ for the
  complement isomorphism (`extensor.tex`, `meet.tex`) and KT's $\Pi(v)$ for the panel; $k$ is only
  the dof. 2.1's note says once that the formalization writes $d = k + 1$, as `rigidity-matrix.tex`
  and `meet.tex` do.
- **Terms** (the open's call; principle E *Terminology*). The Lean's realization record leaves
  statements: a statement says what the record means for $G$ (each hinge the meet of the panels of
  its edge's ends), and one note at `def:panel-hinge-framework` explains the selector. "Free-normal",
  "device", "glue", "leg" and "bare" go; "seed", if kept, is defined once where first used.
- **The crux list, by label** (the open): twelve slices, *Scope*; the done entry under the ledger's
  `rigidity-matrix.tex` heading is here (2.1). Node moves stay within a section file (`F-119`). The
  no-Lean-edit base is `ef57b401`, the open's parent.
- **Tasks 2.1–2.16 (done).** `panel-layer.tex` follows KT §5 and p. 671 (Proposition 2.3's halves,
  KT Lemma 5.3 before `thm:theorem-55`, Theorem 5.6 without the projective move, the base by KT's
  three cases); `case-i.tex` KT Lemma 5.4 for $m \le d + 1$ and KT §6.2; `case-ii.tex` KT §6.3;
  `genericity-and-count.tex` KT §5.1 and p. 680; `case-iii.tex` KT pp. 680–698 ($(G, p_1)$, its
  subspace $L$, KT's isomorphisms renaming one realization); the opening KT pp. 670–671. A
  statement that claims more than its pins, or less (`F-169`), keeps the claim, with a note; its
  proof assumes what it needs and says so (`F-136`–`F-138`, `F-141`, `F-142`, `F-145`, `F-149`,
  `F-150`, `F-154`, `F-158`, `F-165`).
