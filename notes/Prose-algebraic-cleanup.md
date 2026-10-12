# PROSE round 3/5 — `prose-algebraic`, the algebraic induction (work log)

**Status:** in progress (opened 2026-10-12). Round 3 of **PROSE**'s five rounds; their plan and the
PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round rewrites the prose of the chapter `algebraic-induction.tex` and
its five sections, `panel-layer.tex` → `case-iii.tex`, to `40-exposition`'s register and round 1's
exemplar. Every `\label`, pin, `\leanok`, `\uses` edge and statement strength stays as it is. What
else the round notices goes to the ledger `notes/Prose-findings.md`: the open recorded
`F-115`–`F-120`, task 2.1 `F-121`–`F-123`. 18 one-commit tasks; tasks 1 and 2.1 are done, and the
round has no planned stop. **Next concrete task:** task 2.2, `panel-layer.tex`'s realization
hypothesis and KT Theorem 5.5, at Opus (*Lemma checklist*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. No entries yet.

## Current state

**Task 2.1 has landed** (this commit): `panel-layer.tex` 1–228 at the open, now 1–328, 7 nodes,
every `\label`, `\lean{…}`, `\leanok` and `\uses` byte-identical and in order; the file's later
lines have moved by +100 (task 2.2's range, 240–497 at the open, is now 340–597). Nothing is
mid-stream; task 2.2 is next.
- **Gates at this commit**, all the open's values: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, 9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and
  `b53eb8b1cf78cb06`; `print.log` 0 `LaTeX Warning` lines (70 overfull boxes, the open's 72, none
  in lines 1–328). Screens on `panel-layer`: register 61 / 12, devices 0 / 16, `\operatorname` 1,
  vocabulary 41, forward `\uses` 10 / 5 (the open's 63 / 15, 0 / 17, 1, 44, 10 / 5). In lines
  1–328: register 0 in prose, one `\texttt` address in prose, "endpoint selector" twice in notes.

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
- **The surface**, as `notes/Prose.md` §3 has it: 6 files, 4 221 lines, 106 nodes, 152 pins. Two
  nodes have four or more pins (§7; `F-009`): `lem:case-III-claim612-eq644` (5) and
  `lem:cycle-realization-rigid` (4). All 106 nodes are green and filled; no title says
  `superseded`.
- `scripts/blueprint-deps.py --summary` (0.24 s) agrees with the built graph and `lean_decls`. In
  these files 48 nodes have every pin outside every main result's closure (`F-012`'s round-3
  count), among them steps the prose presents as the live induction's (`F-118`).
- **The crux nodes, by label:** twelve of the sixteen slices have them; the list is under *Scope*.
- **The open's findings:** `F-115`–`F-117` (S) and `F-118` (M) under *Candidates for the PI*;
  `F-119` and `F-120` (N) under *Moved to a later round*.

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
  - `panel-layer` (2.1–2.3): `prop:rigidity-matrix-prop11` with `thm:theorem-55-6-d3` (the two
    halves); `thm:theorem-55` and the formalization note after `thm:theorem-55-d3-instance` (the
    motive conditioned on simplicity; the entry's "line ~441" is line 455).
  - `case-i` (2.7, 2.8): `lem:case-I` (KT eq. (6.3)'s rank addition); `lem:rigidContract-isMinimalKDof`
    (union against contraction); `lem:claim-6-4`; the passage after `lem:case-I-splice-seed` (the
    two body sets); the passage before `lem:case-I-realization` (contraction and simplicity);
    `lem:case-I-realization`; the passage after it (genericity against general position);
    `lem:case-I-dispatch` (the trifurcation; the Claim 6.6 entry's induced $G'$ is in the ledger,
    not the chapter).
  - `case-ii` (2.9), with `genericity-and-count`'s `lem:case-II-realization-placement` (2.10):
    `lem:case-II-realization` (KT eq. (6.12)'s degenerate placement).
  - `case-iii` (2.11–2.15): Claim 6.11's chain `lem:case-III-claim-6-11-base`,
    `lem:case-III-gap3-minimalKDof`, `lem:case-III-nested-rank-lower`, `lem:case-III-claim-6-11`
    and the remark on KT's footnote-6 transfer; `lem:case-III-columnop`,
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

No `\uses` edge points at a later chapter. The register's other 63 hits are label words,
"genuine" (39), "producer" (19) and "splice" (5); in prose they are "carry" and its forms (50 of
66), "genuine" (6), "splice" (5) and "route" (5). The vocabulary column is mostly "seed" (89),
"conjunct(s)" and "bare" (31), "device" (22), "endpoint selector" (21), "leg(s)" (17) and
"free-normal" (15).

These sections were written in Phases 21–23, rewritten for the rigidity theorist after Phase 23,
and given their crux expositions in Phase 27; they predate the 2026-10-03 clauses. Their problems:
three names for the dimension ($n$, $d$, $k+1$) and a grade $k$ that collides with the dof $k$;
the Lean's realization record in statements (the endpoint selector, link-recording, the bare and
generic conjuncts, $\mathrm{ends}$, $\mathrm{Fin}\,4$); role clauses and formalization remarks in
statements; route history ("see the git history" twice); and prose that cites, as steps of the
induction, nodes whose pins no main result uses (`F-118`).

**Carried in** (`notes/Prose.md` §3 *Round 3*; the ledger's `F-067`):
1. `lem:case-I`'s statement cites `lem:contraction-minimality` for $G/E(H)$ being a smaller minimal
   $k$-dof-graph: the graph form is `lem:rigidContract-isMinimalKDof`'s, the count
   `lem:reduction-measure`'s (2.7).
2. `lem:rigidContract-isMinimalKDof` cites `lem:reduction-step` for the vertex count:
   `lem:reduction-measure`'s (2.7).
3. `lem:case-II-realization`'s proof cites `lem:reduction-step-pos` for the vertex of degree two:
   `lem:reducible-vertex`'s (2.9).
4. The opening says twice that KT Theorem 5.5 is proved with `thm:minimal-kdof-reduction`, and
   `lem:rigidContract-isMinimalKDof`'s proof calls it "the reduction theorem": the induction runs on
   `thm:minimal-kdof-reduction-all-k` (2.7, 2.16).
5. `lem:case-III-chain-discriminator`'s proof cites the line lemma as "the general" duality; it is
   the case $d = 3$, and the form for every $d$ has no node (`F-110`) (2.15).
6. Notation: $\vee$, $\wedge$, $*$, $\bigwedge$ as `meet.tex` writes them (2.1 and every slice;
   *Decisions*).
7. `F-067`: KT Proposition 1.1 is Tay and Whiteley's theorem; the rank formula is KT Proposition
   2.3 (Jackson–Jordán's Theorem 6.1), as `rigidity-matrix.tex` and `deficiency.tex` now say
   (2.1, 2.7, 2.16).

- **`panel-layer`.**
  - *Done:* 2.1 (task 2.1; its open bullet is in this log at `efa7ed2b`).
  - *2.2 (240–497):* `def:rank-hypothesis`'s note names two Lean predicates; `thm:theorem-55` and
    `thm:theorem-55-d3-instance` state "dimension $n \ge 2$" and the endpoint selector (link
    recording is a conjunct of the pin: say it mathematically, principle B *Constructions*).
    `rem:fresh-edge-supply` is principle D's canonical remark: keep it, in mathematical English,
    with five `\texttt` names to reduce. The note after `thm:theorem-55` "routes"; the proof of
    `cor:theorem-55-d3-spanning` is the selector's totality, a note's content.
  - *2.3 (498–777):* KT Theorem 5.6's four forms state "$n \ge 2$", "$K^{n}$" and the endpoint
    selector; `thm:theorem-55-6`'s proof ends on the "$n = k+1$ premise".
    `rem:molecular-conjecture-essential`'s second paragraph is about the formal statement's
    edge-label type, and `rem:molecular-conjecture-nonvacuous` names a Lean witness: formalization
    remarks in remark environments.
  - *2.4 (229–239, 778–1057):* the base-region statements say "minimal-$k$-dof-graph", "generic
    companion", and give "$D - 1 = 5$ (at $d = 3$)" and "$D \cdot 1 = 6$" in a statement for every
    $D$ (check the pins); proofs carry "bare conjunct", "per-link conjunct", $\mathtt{ofNormals}$,
    `\texttt{normalsJoin\_swap}` and "Witness: the standard basis restricted along the inclusion of
    index sets". `lem:extensor-pair-in-panel` is $K^4$ only. The subsection's lead (229–239) last.
  - *2.5 (1058–1352):* `lem:with-normal-preserves`'s proof is three `\texttt` names;
    `thm:theorem-55-6-multigraph`'s proof cites `exists_extensor_in_two_panels_grade` and writes
    $K^{k+2}$; `rem:coplanar-single-body` has the round's one `\operatorname` name; "the
    nondegeneracy condition ranges over the whole edge-label type" is the Lean's.
- **`case-i`.**
  - *2.6 (18–291):* `lem:cycle-realization-rigid` indexes the cycle by $\mathrm{vtx} \colon \Z/m \to
    V$ in its statement (principle B *Constructions*). `lem:cycle-realization` is `F-115`: keep the
    statement; its note misstates the pin's range ($m \le d$; the pin's is $m \le d+1$), and its
    attribution (Crapo–Whiteley Prop. 3.4, Whiteley 1999 Prop. 3: KT's [4] and [34], p. 670)
    belongs in the title or one sentence. Its proof cites the line lemma as "the bare-to-generic
    upgrade" (`F-110`). "parallel-hinges-full"; the block pin's lead-ins narrate Case I.
  - *2.7 (292–588):* `lem:case-I`'s statement carries role clauses ("framework-side carrier",
    "supplied the induction hypothesis") and claims a rank identity its pins do not state (`F-116`;
    keep it); carry-ins 1, 2, 4, 7. The exposition ledger's KT eq. (6.3) entry says `lem:case-I`'s
    proof gives the exterior-column projection; at the open that argument is in the passage after
    `lem:case-I-splice-seed` and in `lem:case-I-realization`'s proof (the close aligns the
    pointer). "Splice glue" (title), "legs", $\mathrm{complementIso}$; `lem:claim-6-4`'s proof:
    endpoint selector, "free-normal", "the genuine content".
  - *2.8 (589–832, 1–17):* the simplicity passage ("a genuine hypothesis", "routes the argument");
    `lem:case-I-realization`'s statement ends on a role clause; the genericity passage
    ($\mathrm{param}$; "the formalization" as subject); `lem:case-I-realization-nonsimple`'s
    $G[\{a,b\}] \restriction \{e,f\}$; the opening's "pieces of shared infrastructure" and "both
    legs of the block-triangular splice".
- **`case-ii` (2.9).** The opening's "Whiteley's bar-joint 1-extension" has no citation (the
  chapter's opening cites Whiteley 1996, Theorem 2.2.2). `lem:case-II-rank-lift` and
  `lem:splitoff-edge-substitution` carry role clauses and proof material in their statements;
  `lem:case-II` bundles a body-level and a panel-level equivalence, writes "(KT~4.6)", and its
  proof $\operatorname{insert} v\ t$. `lem:case-II-realization` (crux): carry-in 3, and "One
  hypothesis rides explicitly: a fresh edge name" (principle D: `\cref` `rem:fresh-edge-supply`).
- **`genericity-and-count` (2.10).** "Genericity device" is a coinage for KT Claims 6.4 and 6.9
  (title and fourteen `\cref`s). `lem:genericity-device` is `F-117` (keep the statement) and
  `F-118`; its proof's "the minor's Gram determinant", and `lem:rank-polynomial-of-le-finrank`'s
  "Gram-determinant coordinatization", describe the route Phase 33 replaced: over a field without
  order a Gram determinant can vanish on independent rows, and the engine uses a maximal minor
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, its header). "Genuinely multivariate". The
  relative-count statements carry "free-normal" and $\mathrm{ends}$; "Realization glue" (title);
  `lem:rank-polynomial-of-le-finrank`'s statement opens on a role clause. The Case II placement
  group: `lem:case-II-realization-placement` uses the four lemmas after it (`F-119`; move it);
  *Why the construction reproduces $e_0$* ends on route history ("see the git history");
  $\langle\mathrm{panelRow}(e,\cdot,\cdot)\rangle$ in a statement; "the genuine content standing
  between".
- **`case-iii`.**
  - *2.11 (15–237):* the "free-normal" paragraph and $\mathit{ends}$; `lem:case-III-claim-6-11-base`
    restates `lem:splitoff-kdof-criterion`'s forward half (`F-120`: say so); "Reroute". *KT's
    original seed-rank transfer* narrates the formalization's retired route and ends "see the git
    history": state KT's footnote-6 argument instead, which the ledger's Claim 6.11 entry says this
    remark summarizes. `lem:case-III-nested-rank-lower`'s statement carries the endpoint selector
    and a gloss after a colon; its proof's "rank-polynomial extractor".
  - *2.12 (238–501):* the subsubsection's lead lists its nine nodes (principle F *Once*);
    $w_{\mathrm{Gv}}$ and $w_{\mathrm{Other}}$ are Lean names; `lem:case-III-conditional-block`
    opens and closes its statement with its role, and `lem:case-III-transport-collapse` adds "A
    companion identity records …"; `lem:case-III-columnop`'s proof reads as a Lean case split.
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

- [x] **1. O — the open** (this commit; docs only): this log, the baselines, the open's findings
  `F-115`–`F-120`, and the status surfaces.
- [ ] **2. The slices**, one commit each, in `\input` order. Each section's own opening goes in its
  file's last slice and the chapter's opening last (principle F). The diagnosis of each is above;
  the carry-ins are numbered as there.
  - [x] **2.1 `panel-layer.tex`, panel-hinge frameworks and KT Proposition 2.3** (this commit; 1–228
    at the open, now 1–328, 7 nodes). Applied the round's notation and wrote its note. Found
    `F-121`–`F-123`.
  - [ ] **2.2 `panel-layer.tex`, the realization hypothesis and KT Theorem 5.5** (240–497): 6 nodes,
    258 lines; crux `thm:theorem-55` and the note after `thm:theorem-55-d3-instance`.
  - [ ] **2.3 `panel-layer.tex`, KT Theorem 5.6 and the molecular conjecture** (498–777): 5 nodes,
    280 lines; crux `thm:theorem-55-6-d3`.
  - [ ] **2.4 `panel-layer.tex`, the base region and the cycle seeds** (778–1057, and the
    subsection's lead 229–239): 9 nodes, 291 lines.
  - [ ] **2.5 `panel-layer.tex`, the framework operations and the multigraph conjecture**
    (1058–1352): 8 nodes, 295 lines.
  - [ ] **2.6 `case-i.tex`, KT Lemma 5.4 and the block pin** (18–291): 10 nodes, 274 lines.
  - [ ] **2.7 `case-i.tex`, KT eq. (6.3), the contraction and KT Claim 6.4** (292–588): 5 nodes,
    297 lines; crux throughout; carry-ins 1, 2, 4 and 7.
  - [ ] **2.8 `case-i.tex`, KT Lemmas 6.2, 6.3 and 6.5, and the opening** (589–832, 1–17): 4
    nodes, 261 lines; crux throughout.
  - [ ] **2.9 `case-ii.tex`** (1–173): 4 nodes, 173 lines; crux `lem:case-II-realization`;
    carry-in 3.
  - [ ] **2.10 `genericity-and-count.tex`** (1–387): 11 nodes, 387 lines.
  - [ ] **2.11 `case-iii.tex`, KT Claim 6.11** (15–237): 5 nodes, 223 lines; crux throughout.
  - [ ] **2.12 `case-iii.tex`, the candidate completion** (238–501): 9 nodes, 264 lines; crux
    `lem:case-III-columnop` and the candidate row's two nodes.
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
  covers $m \le d + 1$, and its note says $m \le d$.
- `F-116` (S, task 1): `lem:case-I` states KT eq. (6.3)'s rank addition through the contraction;
  its three pins are block-pin criteria that mention no contraction.
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

## Moved to a later round

`E`, `N`, `T` and `U` findings for round 5, `prose-graph`, and `L` findings for a later Lean round,
one line each naming the ledger ID and the task that found it.

- `F-119` (N, task 1): 18 `\uses` edges at 10 nodes point at later sections of the chapter, and 12
  at 7 nodes at later nodes of their own section.
- `F-120` (N, task 1): two of the blueprint's ten doubly pinned declarations are round 3's; the
  $d = 3$ point choice's pins have no Lean caller.
- `F-123` (L, task 2.1): the docstrings of `PanelHinge.lean`'s first pins (the selector field,
  `rigidityMatrix_prop11`, the moment-curve constructions) misdescribe their bodies or callers.

## Blockers / open questions

- None. The round has no planned stop.

## Hand-off / next phase

**Next concrete task: task 2.2, `panel-layer.tex`'s realization hypothesis and KT Theorem 5.5
(240–497 at the open, now 340–597), at Opus**, a fresh agent (`notes/Prose.md` §2). Its diagnosis
is under *Per-chapter diagnosis*, its gates and screens under *Scope*. Then tasks 2.3–2.16 in order,
and task 3 closes the round. For the slices:
- **The PI's check** (round 1's Stop 1: "the overriding goal is to make sure the result is
  understandable"). 2.1–2.3 open the round; the coordinator reads them in full against the
  exemplars, as round 2's hand-off asked for its first three.
- **Notation and terms.** 2.1 applied *Decisions*' notation; its note on $d = k + 1$, and on the
  separate dimension parameter of the deficiency, follows `def:panel-support-extensor`. Every later
  slice follows it and the terminology entry. The chapter's opening still writes $n$ until 2.16.
- **From task 2.1.** The prose after `def:panel-hinge-framework` defines a *nondegenerate* hinge
  ($C(p(e)) \neq 0$) for every body-hinge framework, and identifies a panel-hinge framework with
  its *body-hinge interpretation*; `fmlnote:panel-hinge-nondegenerate` names the *endpoint
  selector* and says that "each edge gets its ends" is a separate formal condition. Later
  statements say "realization of $G$" and `\cref` that note where a pin's selector condition is
  missing or differs (`F-122`: the molecular conjecture's panel side, 2.3). 2.2's
  `cor:theorem-55-d3-spanning` (title and proof), and 2.3's paragraph before `thm:theorem-55-6` and
  its proof, still say "KT Proposition 1.1" for the rank formula: carry-in 7 applies there, as in 2.1's subsection *The generic rank
  formula (KT Proposition 2.3)*. The note after `prop:rigidity-matrix-prop11` is the one place that
  says its pin assumes the generic bound (`F-121`).
- **Crux nodes** keep their full proofs: tasks 2.1–2.3 and 2.7–2.15 (*Scope*).
- **Carry-ins** 1–7 are under *Per-chapter diagnosis*, each with its task.
- **The open's findings** are recorded, not acted on: 2.6 keeps `lem:cycle-realization`'s
  statement and corrects its note's range (`F-115`); 2.7 keeps `lem:case-I`'s (`F-116`); 2.10
  keeps `lem:genericity-device`'s (`F-117`). Where a proof cites a node its pin does not reach
  (`F-118`), a slice may name in prose the node the pin does reach, after checking it with the
  script; the edges wait for round 5. 2.1–2.4, 2.6–2.10, 2.12 and 2.14 give `F-119`'s forward
  references a sentence or a move within the file.
- **Tools.** The two screens under *Scope*; `scripts/blueprint-deps.py --label <label>` or
  `--chapter <section>` (e.g. `--chapter case-i`). The ledger's next ID is `F-124`.

## Decisions made during this round

- **The slicing** (the open): sixteen slices, §3's count, numbered 2.1–2.16 as round 2's (task 1
  the open, task 3 the close). `panel-layer` splits at its subsections and before KT Theorem 5.6
  and the base region; `case-i` before `lem:case-I` and before the simplicity passage; `case-ii`
  and `genericity-and-count` one each; `case-iii` at §3's cuts, then after
  `lem:case-III-claim612-r-nonzero` and the $d = 3$ dispatch. 91–387 lines, mean 264.
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
  `rigidity-matrix.tex` heading is here (2.1). Node moves stay within a section file (`F-119`).
- **The no-Lean-edit base** is `ef57b401`, the open's parent.
- **Task 2.1, `panel-layer.tex` 1–228.** The subsection opens on KT's panel-hinge frameworks and
  their nonparallel realizations built from panels (KT p. 648, §5.1). A paragraph shows that KT's
  hinge extensor is a nonzero multiple of $*(n_1 \vee n_2)$, through the unpinned
  `extensor_join_proportional_complementIso_meet`. `lem:moment-curve-general-position` states
  the moment-curve construction that its pins and three other chapters use, with the old existence claim
  as its "in particular"; its pin-listing note is gone. KT Proposition 2.3's two halves and the
  two inequalities are the subsection's opening and the proof's backbone; the lower bound follows
  KT's proof of Theorem 5.6 (p. 670). `F-121`–`F-123` are recorded.
