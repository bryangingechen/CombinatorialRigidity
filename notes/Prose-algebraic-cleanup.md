# PROSE round 3/5 — `prose-algebraic`, the algebraic induction (work log)

**Status:** in progress (opened 2026-10-12). Round 3 of **PROSE**'s five rounds; their plan and the
PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round rewrites the prose of the chapter `algebraic-induction.tex` and
its five sections, `panel-layer.tex` → `case-iii.tex`, to `40-exposition`'s register and round 1's
exemplar. Every `\label`, pin, `\leanok`, `\uses` edge and statement strength stays as it is. What
else the round notices goes to the ledger `notes/Prose-findings.md`: the open recorded
`F-115`–`F-120`, and tasks 2.1–2.12 `F-121`–`F-161`. 18 one-commit tasks; tasks 1 and 2.1–2.12
are done, and the round has no planned stop. **Next concrete task:** task 2.13, `case-iii.tex`'s
case $d = 3$: the span and the point choice (now 831–1149), at Opus (*Lemma checklist*). Round
manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. No entries yet.

## Current state

**Task 2.12 has landed** (this commit): `case-iii.tex`'s row operations of KT eqs. (6.24)–(6.29),
the open's 238–501 (350–612 at the parent), now 350–829 under the retitled subsubsection *The row
operations of KT eqs. (6.24)–(6.29)* (its label unchanged). Its 9 nodes keep every `\label`,
`\lean{…}`, `\leanok` and `\uses` byte-identical and in order; six formalization notes are new.
Nothing is mid-stream; task 2.13 is next.
- **Gates at this commit**, all the open's values: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, 9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and
  `b53eb8b1cf78cb06`; `print.log` 0 `LaTeX Warning` lines (59 overfull boxes, none in the
  slice). Screens on the slice: register 1 / 1 → 0 / 0, devices 0 / 0, `\operatorname` 0,
  vocabulary 4 → 3 (the endpoint selector, in three notes); the Lean names $w_{\mathrm{Gv}}$,
  $w_{\mathrm{Other}}$, which the screen misses, gone; `case-iii`'s forward `\uses` 0 / 2.

**Verified at the open** (2026-10-12, at `ef57b401`; task 1, docs only):
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines (re-run here, all
  cached; the coordinator's run gave the same). The axioms check does not run at the open
  (`notes/Prose.md` §2: round 1's open and round 5's close only).
- **The no-Lean-edit base is `ef57b401`**, the open's parent: the close checks that `git diff
  --stat ef57b401.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` is
  empty.
- **The round's gate values**, round 2's close reproduced exactly (the blueprint has not changed
  since). Every slice must reproduce them:
  - `blueprint/lint.sh` green. `blueprint/verify.sh` green (38 s): `checkdecls` silent, and **9**
    `WARNING:` lines, all plasTeX package and renderer notices.
  - `blueprint/print/print.log`: **0** `LaTeX Warning` lines; **72** overfull boxes, counted at the
    open and close but not gated.
  - The built graph: **657** nodes and **1 292** edges, fingerprint **`673e3178d1b3145e`**; pin
    hash **`b53eb8b1cf78cb06`** (`blueprint/lean_decls`: 1 030 pins, 1 020 distinct names). The
    commands are under *Scope*, gate 3.
- **The surface** (`notes/Prose.md` §3): 6 files, 4 221 lines, 106 nodes, 152 pins, all green and
  filled, no title `superseded`; `lem:case-III-claim612-eq644` (5) and `lem:cycle-realization-rigid`
  (4) have four or more pins (§7; `F-009`). `scripts/blueprint-deps.py --summary` agrees with the
  built graph and `lean_decls`; 48 nodes here have every pin dead (`F-012`, `F-118`). The crux
  nodes are under *Scope*, the open's findings `F-115`–`F-120` under *Candidates* and *Moved*.

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
  - `case-iii` (2.11–2.12 done; 2.13–2.15): Claim 6.11's chain `lem:case-III-claim-6-11-base`,
    `lem:case-III-gap3-minimalKDof`, `lem:case-III-nested-rank-lower`, `lem:case-III-claim-6-11`
    and the remark on KT footnote 6 (2.11); `lem:case-III-columnop`,
    `lem:case-III-candidate-row-construction`, `lem:case-III-candidate-row`; the $d = 3$ worked
    case's lead, `lem:case-III-claim612-p3-placement`, `lem:case-III-claim612-eq644`,
    `lem:case-III-claim612`, `lem:case-III-candidate-dispatch-d3`; *The triangle floor*; *The
    general-$d$ chain dispatch* with `lem:case-III-chain-discriminator`,
    `lem:case-III-chain-dispatch` and `lem:case-III` (also the Case-naming entry).

  `meet.tex`'s `lem:case-III-claim612-line-in-panel-union` is round 2's. Ledger notes also point
  here: the Phase-33 note at the opening's *Field generality* paragraph (2.16), and the Phase-40a
  note at *The triangle floor*'s $d \le 3$ and `lem:case-III`'s single degree-2 vertex (2.15).
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

**Carried in** (`notes/Prose.md` §3 *Round 3*; the ledger's `F-067`):
1.–3. Done (2.7, 2.9).
4. The opening says twice that KT Theorem 5.5 is proved with `thm:minimal-kdof-reduction`: the
   induction runs on `thm:minimal-kdof-reduction-all-k` (2.16; 2.7's "reduction theorem" is gone).
5. `lem:case-III-chain-discriminator`'s proof cites the line lemma as "the general" duality; it is
   the case $d = 3$, and the form for every $d$ has no node (`F-110`) (2.15).
6. Notation: $\vee$, $\wedge$, $*$, $\bigwedge$ as `meet.tex` writes them (2.1 and every slice;
   *Decisions*).
7. `F-067`: KT Proposition 1.1 is Tay and Whiteley's theorem; the rank formula is KT Proposition
   2.3 (Jackson–Jordán's Theorem 6.1), as `rigidity-matrix.tex` and `deficiency.tex` now say
   (2.16; the parts of 2.1 and 2.7 are done).

- **`panel-layer` … `genericity-and-count`.** *Done:* 2.1–2.10 (their open bullets are in this
  log at `efa7ed2b`, the last at `120eca58`).
- **`case-iii`.**
  - *Done:* 2.11–2.12 (their open bullets are in this log at `fe05a812` and `ba79d703`). The line
    numbers below are the open's; since 2.12, add 329 (*Hand-off*).
  - *2.13 (502–820):* `lem:case-III-claim612-extensor-span` is `F-060` (keep); "(finrank $D$)",
    "grade $e = k$". The point-choice statements carry $\mathrm{Fin}\,m$, $\mathrm{homogenize}$,
    $\mathrm{eval}_q$ and $pp$; `lem:case-III-claim612-panel-point-exists`'s title says KT eq.
    (6.45), its statement "(6.67) (p. 698)" and "a genuine … affine subspace". The producer and
    determinant nodes are off the formal route (`F-120`). The paragraph before
    `lem:case-III-claim612-points-affineIndep-real-normals` says `lem:case-II-realization` reads
    $n_a, n_b, n_c$, which Case II never does (check: the $d = 3$ dispatch does); $\mathrm{mulVecLin}$.
  - *2.14 (821–1104):* $\rho$ is KT's relabel (KT eq. (6.31)) and also the hinge-row functional in
    the proofs of the $p_2$ and $p_3$ lemmas: keep KT's, rename the other.
    `lem:splitOff-ofNormals-relabel`'s statement opens on a justification and states the Lean record
    ($\mathrm{ends}_0$, "three conjuncts", "recorded as a short corollary");
    `lem:splitOff-rigidityRows-relabel` and `lem:case-III-claim612` carry role clauses; the note
    after `lem:case-III-candidate-dispatch-d3` "rides" and names the "live path".
  - *2.15 (1105–1386, 1–14):* the two crux narratives ("the formalization must do visible work",
    "genuinely", "bare conjunct"); carry-in 5. The discriminator's and `lem:case-III`'s statements
    carry "general-position, link-recording realization" and "bare full-rank realization";
    `lem:case-III`'s also "One hypothesis rides explicitly", "discharged internally … not carried"
    and three letters for the dimension ($n$, $k$, $d$). Its proof: a `\texttt` name, "genuine
    branch" twice. The subsection's opening (1–14) last.
- **`algebraic-induction.tex` (2.16).** The chapter's opening, last (principle F): carry-ins 4 and
  7; "dimension $n \ge 2$ … the $d = 3$ instance"; "carries"; its Case I–III list repeats the
  sections' openings (principle F *Once*). The *Field generality* paragraph keeps its claim and its
  Whiteley 1988 credit (the Phase-33 ledger note points at it).

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
slice at Opus, a fresh agent per task; the close may run at Sonnet (§2).

- [x] **1. O — the open** (`efa7ed2b`; docs only): this log, the baselines, the open's findings
  `F-115`–`F-120`, and the status surfaces.
- [ ] **2. The slices**, one commit each, in `\input` order. Each section's own opening goes in its
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
  - [x] **2.11–2.12 `case-iii.tex`, KT Claim 6.11 and the candidate completion** (`ba79d703`,
    this commit; 15–501, now 14–829): KT's three steps (pp. 684–685) and KT footnote 6; KT's row
    and column operations (pp. 685–686) at $(G, p_1)$ with its subspace $L$ (KT eq. (6.12)).
    Found `F-154`–`F-161`.
  - [ ] **2.13 `case-iii.tex`, the case $d = 3$: the span and the point choice** (502–820): 10
    nodes, 319 lines; crux the subsubsection's lead.
  - [ ] **2.14 `case-iii.tex`, the case $d = 3$: the three candidates and KT Claim 6.12**
    (821–1104): 8 nodes, 284 lines; crux from `lem:case-III-claim612-p3-placement` on.
  - [ ] **2.15 `case-iii.tex`, the triangle floor, KT Lemma 6.13 and the opening** (1105–1386,
    1–14): 5 nodes, 296 lines; crux throughout; carry-in 5.
  - [ ] **2.16 `algebraic-induction.tex`, the chapter's opening** (1–91): no node, 91 lines;
    carry-ins 4 and 7.
- [ ] **3. X — close the round** (`CLEANUP.md` *Workflow* 5; docs only).
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

## Blockers / open questions

- None. The round has no planned stop.

## Hand-off / next phase

**Next concrete task: task 2.13, `case-iii.tex`'s case $d = 3$: the span and the point choice
(502–820 at the open, now 831–1149), at Opus**, a fresh agent (`notes/Prose.md` §2). Its diagnosis
is the *2.13* item under *Per-chapter diagnosis*, its gates and screens under *Scope*. Then tasks
2.14–2.16 in order, and task 3 closes the round. For the slices:
- **Line numbers.** 2.11 and 2.12 added 329 lines to `case-iii.tex`: the open's 502–820, 821–1104
  and 1105–1386 are now 831–1149, 1150–1433 and 1434–1715; the opening is still 1–13.
- **Notation and terms.** *Decisions*' notation (2.1; its note on $d = k + 1$ follows
  `def:panel-support-extensor`); the chapter's opening writes $n$ until 2.16. After
  `def:panel-hinge-framework`: a *nondegenerate* hinge, the framework identified with its
  body-hinge interpretation, the *endpoint selector* in notes only
  (`fmlnote:panel-hinge-nondegenerate`; `F-122`, `F-128`). `def:rank-hypothesis` defines *at the
  target rank* and *generic full-rank realization*, `def:genuine-hinge-realization`
  *nondegenerate-hinge panel realization*. Statements omit the fresh label (a note cites
  `rem:fresh-edge-supply`); `def:framework-with-graph` gives the framework on a new graph, the
  *restriction* on a subgraph.
- **From `case-i.tex`** (2.6–2.8). A realization statement opens "Let $d \ge 2$, let $K$ be an
  infinite field" and states the induction hypothesis as `lem:case-I-realization-nonsimple` does. A
  statement that omits a hypothesis its pin assumes keeps its claim; its proof assumes it and says
  so, and a note gives it (`F-141`, `F-154`). The passage after `lem:case-I-realization` explains
  KT's genericity by the non-roots of a product of polynomials; cite it (principle F).
  `lem:cycle-normals` gives normals, not a "seed" (2.15).
- **From tasks 2.9–2.10.** `lem:case-II-realization-placement` (`F-150`, `F-118`) is cited as a
  step at `case-iii.tex` 7, 1053, 1158, 1414 and 1637: cite KT eq. (6.12) and the proof of
  `lem:case-II-realization` instead (as 2.12 did). `lem:case-II`'s panel assertion is vacuous
  (`F-145`). KT Claim 6.9 (p. 678) is only that $(G, p_1)$ is a panel-hinge realization.
  `lem:genericity-device` is *the rank at generic normals* (KT §5.1, p. 668), used as
  `lem:rank-polynomial-of-le-finrank` (`F-149`); "the genericity device re-realizes" (1419, 1510,
  1646) and the opening's "Claim 6.4, `lem:genericity-device`" (2.16) follow this.
- **From task 2.11.** Later slices still say "free-normal" and "seed" (39 hits): write the
  panel-hinge framework $(G, q)$ with normals $q$. Statements write $G_v = G - v$, $|V(G_v)|$ and
  the "new edge $ab$" (the opening, 2.15, still says "deleted edge"). The remark after
  `lem:case-III-nested-rank-lower` cites the proof of `lem:case-III-chain-discriminator` for the
  product that fixes $q$: 2.15 keeps the two consistent.
- **From task 2.12.** KT §6.4.1 is $d = 3$ ($D = 6$); the general-$d$ form of eqs.
  (6.24)–(6.29) is KT eqs. (6.50)–(6.52), p. 693. Notation: the rows at $ab$ are
  $S \mapsto r_j(S(a) - S(b))$ for forms $r_j$ on $K^D$; $r = \sum_j \lambda_j r_j$ (KT's $r$,
  p. 690); the new row $w$ is $S \mapsto r(S(v) - S(a))$; $x$ is a generic form on $K^D$;
  `lem:case-III-conditional-block` has $\varphi_i$, $\omega$, $\psi_j$ as
  `lem:rigidityRows-pinned-placement-rank-add`; $\rho$ is left to KT's relabel (2.14).
  `lem:case-III-candidate-row` now states KT's bound at $(G, p_1)$ for a subspace $L \subset \Pi(a)$
  with $r$ not vanishing on $C(L)$; at the normals $q(a) + t\,q(b)$ at $v$ the block is singular
  (`F-158`), so the $p_2$, $p_3$ nodes (2.14) cite its argument with their own $L$. The coinage
  "candidate completion" left the subsubsection's title; 2.13's lead (856), 2.14 (1160, 1169,
  1294, 1352) and 2.15 (11, 1379, 1409) still use it.
- **Crux nodes** keep their full proofs: those of tasks 2.13–2.15 remain (*Scope*).
- **Carry-ins** 1–7 are under *Per-chapter diagnosis*, each with its task.
- **The open's findings** are recorded, not acted on: `lem:genericity-device` kept its statement
  (`F-117`, `F-149`). Where a proof cites a node its pin does not reach (`F-118`), a slice may name
  in prose the node the pin does reach, after checking it with the script; the edges wait for
  round 5. 2.14 gives `F-119`'s forward reference (`lem:case-III-claim612-p3-placement`) a sentence
  or a move within the file; 2.12 gave `lem:case-III-candidate-row`'s a sentence.
- **Tools.** The two screens under *Scope*; `scripts/blueprint-deps.py --label <label>` or
  `--chapter <section>` (e.g. `--chapter case-iii`). The ledger's next ID is `F-162`.

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
- **Tasks 2.1–2.12 (done).** `panel-layer.tex` follows KT §5 and p. 671 (Proposition 2.3's halves,
  KT Lemma 5.3 before `thm:theorem-55`, Theorem 5.6 without the projective move, the base by KT's
  three cases, `F-131`); `case-i.tex` KT Lemma 5.4 for $m \le d + 1$ (`F-115`) and KT §6.2;
  `case-ii.tex` KT §6.3; `genericity-and-count.tex` KT §5.1 and p. 680; `case-iii.tex` KT pp.
  684–686, with KT's $(G, p_1)$ and its subspace $L$ for eqs. (6.24)–(6.29). A statement that claims
  more than its pins, is vacuous or fails in a degenerate case keeps the claim, with a note; its
  proof assumes what it needs and says so (`F-136`–`F-138`, `F-141`, `F-142`, `F-145`, `F-149`,
  `F-150`, `F-154`, `F-158`).
