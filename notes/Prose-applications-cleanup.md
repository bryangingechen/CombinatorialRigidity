# PROSE round 4/5 — `prose-applications`, applications, continuations and the introduction (work log)

**Status:** in progress (opened 2026-10-13). Round 4 of **PROSE**'s five rounds; their plan and the
PI's decisions are in `notes/Prose.md`, and `.claude/autopilot/queue.toml` is the authority for
which rounds are done. The round rewrites the prose of the five chapters `bar-joint-3d.tex`,
`molecule-modelling.tex`, `molecule-application.tex`, `jacobs.tex` and `generic-lift.tex`, then the
parts of `intro.tex` that `40-exposition` did not rewrite, to `40-exposition`'s register and round
1's exemplar. Every `\label`, pin, `\leanok`, `\uses` edge and statement strength stays as it is.
What else the round notices goes to the ledger `notes/Prose-findings.md`: the open recorded
`F-174`, and tasks 2.1–2.12 `F-175`–`F-225`. 16 one-commit tasks; tasks 1 and 2.1–2.12 (the five
chapters) are done, and the round has no planned stop. **Next concrete task:** task 2.13,
`intro.tex`, *Organization of the blueprint* and the continuation paragraph (51–364), at Opus
(*Lemma checklist*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: Stop 1 was the program's only one, in round 1 (`notes/Prose.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first, and the PI answers in an entry that starts `**PI,
<date>:**`. No entries yet.

## Current state

**Task 2.12 has landed** (this commit), the last of the five chapters: `generic-lift.tex`'s
opening is now 1–77, the lead of `sec:generic-lift-bodyhinge` 972–1031, and its last seven nodes
with the closing paragraph 1256–1546 (were 1–54, 949–998 and 1223–1442). Every node keeps its
`\label`, `\lean{…}`, `\leanok` and `\uses` byte-identical, in the same order; one note is new,
unlabelled. `intro.tex` is unchanged since the open, so its line numbers hold. Nothing is
mid-stream.
- **Gates at this commit**, all the open's values: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, 9 `WARNING:` lines; the invariance check `1292 edges 673e3178d1b3145e` and
  `b53eb8b1cf78cb06`; `print.log` 0 `LaTeX Warning` lines (45 overfull boxes, none in the slice).
  Screens on the slice: register 0 in prose, devices 0 / 0, `\operatorname` 0, vocabulary 0;
  forward `\uses` 0 / 0 for `generic-lift`. The open's (1–54, 735–784, 928–1147): register 4 in
  prose ("carry" and its forms), devices 0 / 0, `\operatorname` 0, vocabulary 7 (the selector twice,
  "link-recording" five times), 0 / 0.

**Verified at the open** (2026-10-13, at `baa224cc`; task 1, docs only):
- Whole-project `lake build` green: 2 996 jobs, 0 `warning:` and 0 `error:` lines (re-run here, all
  cached; the coordinator's gave the same). No axioms check at the open (`notes/Prose.md` §2). **The
  no-Lean-edit base is `baa224cc`**, the open's parent: the close checks that `git diff --stat
  baa224cc.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` is empty.
- **The round's gate values**, round 3's close reproduced exactly; every slice reproduces them:
  `lint.sh` green; `verify.sh` green (47 s), `checkdecls` silent, **9** `WARNING:` lines (plasTeX
  package and renderer notices); `print.log` **0** `LaTeX Warning` lines (**51** overfull boxes,
  counted at the open and close, not gated); the built graph's **657** nodes and **1 292** edges,
  fingerprint **`673e3178d1b3145e`**, and the pin hash **`b53eb8b1cf78cb06`** (1 030 pins, 1 020
  distinct names; the commands under *Scope*, gate 3).
- **The surface** (`notes/Prose.md` §3): 6 files, 3 640 lines, 95 nodes, 152 pins, all green and
  filled, no title `superseded`; six nodes have four or more pins (§7; `F-009`; listed at `69bc7afb`).
- `scripts/blueprint-deps.py --summary` agrees with the built graph and `lean_decls`: 76 edges
  missing (`F-004`), 43 unbacked, 22 through another node (`F-006`); 22 pins outside every main
  result's closure, every pin of 13 nodes (`F-012`), ten of them in `generic-lift`.
- **The crux nodes** (*Scope*): done in 2.2–2.3. The open's finding `F-174` (S): 2.3 anchored it.

## Scope and standing rules

From `notes/Prose.md` §2, restated only as far as a builder needs them.

- **Surface.** The chapters `bar-joint-3d`, `molecule-modelling`, `molecule-application`, `jacobs`
  and `generic-lift`, in `chapter/main.tex` order, then `intro.tex`'s parts below; no other
  chapter's TeX. In scope too: a docs edit keeping a pointer into these files true
  (`notes/BlueprintExposition.md`), and a `bibliography.bib` entry a slice relies on and verifies.
- **`intro.tex`'s parts** (the open's line numbers). `40-exposition` task 26 (`30e79461`) rewrote
  its reader path into `pencil.tex` and `main-component.tex`; `64bb9754` renamed its conjecture a theorem.
  - *Rewritten:* the opening from "This blueprint accompanies" through the sentence on
    `sec:jacobs` (9–44); *Organization of the blueprint* (51–329), the four-arc and per-phase
    lists; the continuation paragraph on phases 32–35 (331–364); *Reading this blueprint* (435–512).
  - *Kept:* the Caution paragraph (4–7, verbatim; it mirrors `README.md` and `home_page/index.md`);
    the opening's two sentences on the pencil chapters (44–49); the fifth continuation (366–433),
    whose first words alone 2.13 may change to fit; the pencil item's words in *Reading*.
  - *Its rules:* the per-phase list keeps its phase numbers (`lint.sh` check 5b exempts it) and
    loses "genuine" (`notes/Prose.md` §3). It is "a fixed-size orientation, not a status log", "one
    terse line per phase" (`blueprint/CLAUDE.md` *File layout*; `PHASE-BOUNDARIES.md` *Sync the
    user-facing status surfaces*): no raw label in prose, and green, red, forward and leaf-most
    only in its one dependency-graph note (`AUTHORING.md`'s dictionary).
- **The hygiene rule.** The round does not change a headline statement or the strength of a
  blueprint statement. A finding that would need such a change becomes a ledger `S` entry and a
  line under *Candidates for the PI*. It is not acted on, and it is not a stop. The readings the
  coordinator accepted in rounds 2–3 (`notes/dispatch-log.md`, 2026-10-08 to 2026-10-13) bind:
  - narrowing a statement to its pin's form is barred (`F-084` is no precedent); a statement that
    claims more than its pins, or less, keeps its claim, with a note;
  - principle B still moves essentiality talk and a definition's consequences out of a statement,
    kept and proved in the prose after;
  - dropping a false gloss, anchoring a definition's domain, and adding a hypothesis that the pin
    states for a degenerate case ($D \ge 1$, $V \ne \emptyset$, $K$ infinite) are anchoring;
  - a `\cref` that contradicts the statement's own words is a gloss, not the claim;
  - a hypothesis edit is tested against the old statement's own hypotheses.

  Each such reading is filed `S` and flagged in the slice's return.
- **Prose only (rounds 1–4), and no Lean edits (all five rounds).** `CombinatorialRigidity/`,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` stay untouched; the close checks that
  their `git diff --stat` since `baa224cc` is empty. Every node keeps its `\label`, its `\lean{…}`
  pins, its `\leanok` and its `\uses` edges. A statement block is edited for register and anchoring
  only. A node may move within its chapter to cure a forward reference (`blueprint/AUTHORING.md`
  principle E, *Node order*); a reference to a later chapter gets a `\cref` and a sentence. A graph
  or node-shape finding becomes a ledger `E` or `N` entry for round 5.
- **The register.** `blueprint/AUTHORING.md` principles A–F with their 2026-10-03 clauses, the
  2026-10-07 *Constructions* clause of B, and the PI's sentence before them ("the overriding goal
  is to make sure the result is understandable"); `40-exposition`'s exemplar
  `notes/Phase40-exposition-exemplar.md`; round 1's pinned sample `notes/Prose-exemplar.md`. No
  chapter is algorithmic. The reader is *Audience & vocabulary*'s rigidity theorist, and its
  dictionary binds: "genuine" is "nondegenerate"; producer, carry and route go; extensors are
  "linearly independent", never "parallel". Labels keep their words
  (`lem:normal-cross-count-producer`, `thm:theorem-55-6-genuine`). Round 3's notation and terms
  hold (*Decisions*).
- **Anchors in both directions** (principle E). Rounds 1–3 rewrote every chapter these five cite: a
  slice checks each `\cref` and imported term against its current text (titles; notation, such as
  `def:rigidityRow`'s $r_e$; credits, such as Laman's for row independence and KT Proposition 2.3;
  "nondegenerate"). No node here `\uses` a node of `pencil.tex` or `main-component.tex`
  (`thm:projective-invariance`'s statement `\cref`s `sec:pencil-duality`). Those two, final since
  `40-exposition`, cite five round-4 targets, and each rewrite keeps their reading true:
  `lem:panel-hinge-dual-molecular` (the lemma fixes $K = \R$; the polarity is an invertible linear
  map of the screw space over every field, sending the join of any two homogeneous points to their
  panel-support extensor); `thm:projective-invariance` (field-general, for a collineation or a
  correlation); `sec:molecule-modelling-defs` (the molecular reading); `lem:screw-map-rows` (an
  invertible screw map keeps the row rank); `lem:partitionDef-merge` (merging lowers the value by $D(m-1) - (D-1)e$).
- **Crux nodes** keep their full proofs (the crux carve-out, `AUTHORING.md` *Proof verbosity*); the
  rewrite changes their register, not their depth. They are the three done entries under
  `notes/BlueprintExposition.md`'s `molecule-modelling.tex` heading, checked by label:
  `thm:molecular-iff-square-bar-joint`, statement and proof (2.3), with its order-four general
  position, whose sharpness example ends `lem:screw-determination`'s proof (2.2); the chapter's
  opening with `thm:panel-hinge-iff-molecular` (2.3), the chain of ranks against Jackson–Jordán's
  deficiency induction; `lem:theorem-56-general-position`'s proof (2.3), KT's "nonparallel" (p.
  671). The other chapters have no entry by the ledger's judgment, which points at expositions in
  place that keep their content: `fmlnote:isLaman3-guard`, the lead of `sec:jacobs-zero-extension`
  and `cor:zero-extension-clique-rank`'s $K_5$ argument; `lem:coordinate-extensor-basis` with
  `lem:endpoint-witness`, the lead of `sec:generic-lift-bodyhinge` with `lem:hinge-point-witness`,
  and `lem:simultaneous-affine-position`'s credit to JJ's Lemma 7.1.
- **Evidence.**
  - Citations meet `CLAUDE.md` *Referencing prior work*. `.refs/` has KT 2011 (and arXiv),
    Jackson–Jordán 2008, 2009 and the 2006 pin-collinear report, Crapo–Whiteley 1982, Whiteley
    1988, 1996 and 1999, Tay 1984 and 1989, Tay–Whiteley 1985, Jordán 2016, Lee–Streinu 2008,
    Nash-Williams 1961, Tutte 1961, Edmonds 1965, Oxley and Schrijver. Not there: Jacobs 1998,
    Franzblau 2000, and the introduction's Laman 1970, Lovász–Yemini 1982,
    Graver–Servatius–Servatius 1993, Edmonds 1970, Nash-Williams 1966 and Jacobs–Hendrickson 1997
    (a DOI landing page, or weaken the claim; `REFS.md`). The commit relying on a passage names it.
  - Claims about the Lean come from declarations' statements and bodies, never from docstrings,
    and from `scripts/blueprint-deps.py --label` or `--chapter <name>` for what a pin reaches.
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
  close re-runs them). The first prints, per file with TeX comments stripped: principle-A register
  hits in all the text and in prose (`\lean`, `\uses`, `\label` and `\cref` arguments removed;
  "carries" is sometimes literal); Lean-device hits inside statement blocks and in the whole file;
  `\operatorname` Lean names; and the dictionary's words and Lean-side devices the device screen
  misses. Round 3's regexes, with "genuinely", "capstone" and "bottoms out" added to the register
  and "shadowing", "transplant", "consume" and "package" to the vocabulary.
  ```sh
  python3 - blueprint/src/chapter/{bar-joint-3d,molecule-modelling,molecule-application,jacobs,generic-lift,intro}.tex <<'PY'
  import re,sys
  E=r'(definition|lemma|theorem|corollary|proposition)'
  A=re.compile(r'\b(feeds?|drives?|fires?|firing|threads?|carr(?:y|ies|ied)|wired?|wiring|routes?|spine|heart of|crucial(?:ly)?|remarkabl[ey]|brick|motive|producer|strat(?:um|a)|honest|genuine(?:ly)?|re-?aim|splice|leaf-most|capstone|bottoms? out)\b',re.I)
  D=re.compile(r'\\texttt\{|\\mathtt\{|\\mathrm\{(?:none|some|Option|Sym2|Fin|List|SimpleGraph|fromEdgeSet|maxBlock|decide|span)\}|\\mathrm\{[^}]*(?:[a-z][A-Z]|\.|\\_)[^}]*\}')
  O=re.compile(r'\\operatorname\{[^}]*(?:[a-z][A-Z]|\.|\\_)[^}]*\}')
  V=re.compile(r'\b(endpoint selector|link-recording|free-normal|seeds?|bare|conjuncts?|device|legs?|splice|glue|producers?|motives?|bricks?|rides?|carrier|shadowing|transplants?|consum(?:e|es|ed|ing)|packag(?:e|es|ed|ing))\b',re.I)
  P=lambda s: re.sub(r'\\(lean|uses|label|[cC]ref)\{[^}]*\}','',s)
  for f in sys.argv[1:]:
      t=re.sub(r'(?<!\\)%.*','',open(f).read()); B=re.findall(r'\\begin\{'+E+r'\}(.*?)\\end\{\1\}',t,re.S)
      print(f.split('/')[-1][:-4], len(A.findall(t)), len(A.findall(P(t))), sum(len(D.findall(P(b))) for _,b in B), len(D.findall(P(t))), len(O.findall(P(t))), len(V.findall(P(t))))
  PY
  ```
  The second counts, per chapter, the `\uses` edges (node, target) of node blocks whose target lies
  in a later chapter or later in the same file, as edges/nodes; prose-only slices leave the first
  at the open's value.
  ```sh
  python3 - <<'PY'
  import re
  R='blueprint/src/'; C=lambda f: f.split('/')[1].removesuffix('.tex')
  def ex(f): return sum(([g]+ex(g) for g in (m+'.tex'*(not m.endswith('.tex')) for m in re.findall(r'^\s*\\input\{([^}]*)\}',open(R+f).read(),re.M))),[])
  F=ex('chapter/main.tex'); T={f:re.sub(r'(?<!\\)%.*','',open(R+f).read()) for f in F}
  W={m.group(1):(i,m.start()) for i,f in enumerate(F) for m in re.finditer(r'\\label\{([^}]*)\}',T[f])}
  for f in [f for f in F if C(f) in ('bar-joint-3d','molecule-modelling','molecule-application','jacobs','generic-lift')]:
      i=F.index(f); X=[set(),set()]
      for s in re.split(r'\\begin\{(?:definition|lemma|theorem|corollary|proposition)\}',T[f])[1:]:
          s=re.split(r'\\begin\{(?:remark|example|fmlnote)\}',s)[0]; n=re.search(r'\\label\{([^}]*)\}',s).group(1)
          for u in (u.strip() for x in re.findall(r'\\uses\{([^}]*)\}',s) for u in x.split(',')):
              j,p=W.get(u,(-1,0))
              k=0 if j>i else 1 if j==i and p>W[n][1] else -1
              if k>=0: X[k].add((n,u))
      print(C(f),*(f'{len(x)}/{len({n for n,_ in x})}' for x in X))
  PY
  ```

## Per-chapter diagnosis

Seen at the open; line numbers are the open's, and the labels are the stable reference. Each slice
re-derives its own findings and records them in its commit and the ledger.

| File | Lines | Nodes | Pins | Register (all / prose) | Lean devices (statements / all) | `\operatorname` | Vocabulary | Forward `\uses` edges (chapter / file) | Tasks |
|---|---|---|---|---|---|---|---|---|---|
| `bar-joint-3d` | 238 | 9 | 9 | 1 / 1 | 1 / 3 | 0 | 1 | 0 / 0 | 2.1 |
| `molecule-modelling` | 476 | 13 | 31 | 13 / 13 | 0 / 0 | 0 | 5 | 0 / 2 | 2.2–2.3 |
| `molecule-application` | 215 | 5 | 9 | 1 / 1 | 1 / 6 | 0 | 12 | 0 / 0 | 2.4 |
| `jacobs` | 1 052 | 36 | 61 | 8 / 1 | 0 / 0 | 0 | 4 | 0 / 0 | 2.5–2.8 |
| `generic-lift` | 1 147 | 32 | 42 | 18 / 10 | 0 / 0 | 0 | 27 | 0 / 0 | 2.9–2.12 |
| `intro` | 512 | 0 | 0 | 15 / 15 | 0 / 57 | 0 | 7 | — | 2.13–2.14 |
| **total** | 3 640 | 95 | 152 | 56 / 41 | 2 / 66 | 0 | 56 | 0 / 2 | |

The register's 15 other hits are label words. In prose: "carry" and its forms 19, "genuine(ly)"
12, "route" 5, "capstone" 3, "feed" 1, "leaf-most" 1 (the introduction's graph note, where it may
stay). Vocabulary: "endpoint selector" 12, "link-recording" 9, "carrier" 7, "shadowing" 5, "seed"
5, "consume"/"package" 12. The introduction's 57 devices are its per-phase Lean file names and
identifiers. These chapters (Phases 24–26, 32, 34) predate the 2026-10-03 clauses and round 3's
notation.

**Carried in** (the ledger's findings addressed to these files, and round 3's carry-in 4):
1. `F-056`: KT's $d$ and $D$ for the body-bar dimension, as round 2 wrote `body-bar.tex`:
   `generic-lift`'s body-bar section (done in 2.10), the Phase-15 and -16 items ($\delta$; 2.13).
2. `F-067`: KT Proposition 1.1 is Tay and Whiteley's theorem, the rank formula KT Proposition 2.3
   (JJ 2009, Theorem 6.1): the Phase-18 and -21 items (lines 222, 277; 2.13), *Reading* (474–476;
   2.14).
3. `F-072`: "boundary regime" leaves the Phase-19 item (2.13).
4. `F-081`: $\operatorname{def} = \operatorname{corank}$ is KT eq. (2.4), JJ 2009's Theorem 4.1(a)
   at $\tilde G$, as `deficiency.tex` credits it (Phase-19 item; 2.13).
5. `F-025`: row independence $\Leftrightarrow$ $(2,3)$-sparsity is Laman's (Jordán's Theorem
   2.2.1), as `rigidity-matroid.tex` now says, not Lovász–Yemini's (Phase-6, -7, -8 items; 2.13).
6. `F-053`: the Phase-12 item's credits follow `matroid-union.tex`'s, after Oxley (2.13).
7. `F-048`: `thm:body-hinge-tay` is formalized for bundles of bars; the form with hinges is
   `cor:bodyhinge-generic-tree-packing`, for simple graphs. `generic-lift`'s opening says so (2.12);
   the Phase-16 item and the phase-34 sentence (2.13) follow it.
8. Round 3's carry-in 4 (`F-100`, `F-173`): the Phase-20 and -21 items say the algebraic induction
   realizes KT Theorem 4.9's reduction (`thm:minimal-kdof-reduction`); it runs on
   `thm:minimal-kdof-reduction-all-k`, as `algebraic-induction.tex` says (principle E; 2.13).
9. `F-117`, `F-118`: done in 2.3; the Phase-21 item's "generic-max-rank device underpinning the
   induction" (2.13).
10. `F-137`, `F-139`, `F-152`, `F-059`, `F-121`: done in 2.9–2.12.

- **The five chapters.** *Done:* 2.1–2.12 (the open bullets are in this log at `69bc7afb`, and each
  slice's own at its parent).
- **`intro.tex`.**
  - *2.13 (51–364):* the per-phase list runs 2–28 lines an item, where `PHASE-BOUNDARIES.md` asks
    for one terse line. LaTeX numbers its last three items 22–24, but they are phases 24–26 (item
    21 covers phases 21–23): label them. Three "Files:" name paths that are directories now
    (`Molecular/RigidityMatrix.lean`, `Molecular/AlgebraicInduction.lean`,
    `Molecular/Induction.lean`): keep the file lists true or drop them. Carry-ins 1–8; "genuine" in
    the Phase-18 item; "capstone" twice, "the project's largest single undertaking", "bottoms out
    on", "carries". The Phase-21 item's "Whiteley's bar-joint 1-extension" and "the
    cycle-realization Lemma 5.4 (Crapo–Whiteley)" follow `case-ii.tex` (Whiteley 1996 Theorem
    2.2.2) and `case-i.tex` (Crapo–Whiteley Proposition 3.4, Whiteley 1999 Proposition 3). The
    continuation paragraph: align with `jacobs.tex`, the *Field generality* paragraph (Whiteley
    1988's precedent), `generic-lift.tex` (its panel form too) and the multigraph subsection of
    `panel-layer.tex`.
  - *2.14 (435–512, 9–44):* *Reading this blueprint*'s second paragraph (460–495) recaps the
    *Organization* as status (principle F *Once*; a status log): "genuine hinges", "all three
    cases" (KT p. 671 has four, as `algebraic-induction.tex` says), carry-in 2; its third
    (497–504) ends "are now in place". The opening: "now formalized", "A continuation chapter";
    the sentence crediting Tay and Whiteley 1985 and Jordán §2.2 is `AUTHORING.md` *Citations*'
    canonical example: check it against `.refs/` and round 1's `henneberg-rigidity.tex` and
    `laman-theorem.tex`, and keep it or update the example in the same commit.

## Lemma checklist (the round's task list)

One commit per task, in this order (`notes/Prose.md` §3). Each line gets its commit's sha; the
commit, with this log as of that commit, carries the task's diagnosis and findings. Rungs: every
slice at Opus, a fresh agent per task; the close may run at Sonnet (§2).

- [x] **1. O — the open** (`69bc7afb`; docs only): this log, the baselines, the open's finding
  `F-174`, and the status surfaces.
- [ ] **2. The slices**, one commit each, in `chapter/main.tex` order. Each chapter's opening goes
  in its last slice, and `intro.tex` comes last (principle F). The diagnosis of each is above; the
  carry-ins are numbered as there.
  - [x] **2.1–2.8** `bar-joint-3d.tex`, `molecule-modelling.tex` (2), `molecule-application.tex`,
    `jacobs.tex` (4) (`67d44583`, `db71b408`, `e5adefe1`, `9c97fecc`, `bc6573b9`, `723c460d`,
    `0e8d7546`, `7c268bce`): found `F-175`–`F-205`.
  - [x] **2.9–2.12 `generic-lift.tex`**: abundance, squares and panel-and-hinge; body-and-bar;
    generic hinge-point assignments; body-and-hinge, its lead and the opening (`c8f1f0f1`,
    `dc58265b`, `ac88bd18`, this commit): found `F-206`–`F-225`.
  - [ ] **2.13 `intro.tex`, *Organization of the blueprint* and the continuation paragraph**
    (51–364): no node, 314 lines; carry-ins 1–8.
  - [ ] **2.14 `intro.tex`, *Reading this blueprint* and the opening** (435–512, 9–44): no node,
    113 lines; carry-in 2.
- [ ] **3. X — close the round** (`CLEANUP.md` *Workflow* 5; docs only).
  - *Gates:* whole-project `lake build` green; the no-Lean-edit check (`git diff --stat baa224cc..
    -- CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` empty). The axioms
    check runs at round 5's close, not here (§2).
  - *The blueprint:* `lint.sh` and `verify.sh` green, the invariance values the open's, the warning
    counts unchanged, overfull boxes counted; the two screens re-run beside the open's table.
  - *Findings:* every ledger entry the round found has its line here, and vice versa.
  - *The exposition ledger:* check every pointer into these files (*Scope*: the three done entries
    and the judged chapters' pointers) against the new text, and add a round note to
    `notes/BlueprintExposition.md`.
  - *Status surfaces:* the ROADMAP row reads ✓ Complete; ROADMAP's PROSE bullet and
    `notes/Prose.md`'s **Status** name round 5's open.
  - *The queue:* `prose-applications`' row in `.claude/autopilot/queue.toml` gets `done = true`,
    and nothing else there changes.

## Candidates for the PI

`S` and `M` findings, one line each naming the ledger ID (`notes/Prose-findings.md` holds the
finding). Recorded, not acted on in this round; round 5's report ranks them for the PI.

- `F-174` (S, task 1): `thm:molecular-iff-square-bar-joint`'s "in particular" realizability
  equivalence is unpinned, and false for coincident centres, which `def:hinge-concurrent` admits.
- `F-177` (S, task 2.1): `def:genericRigidityMatroid`'s placement independence and `def:genericRank`'s
  KT Corollary 5.7 clause left the definitions (principle B); the lemma and the opening keep them.
- `F-178` (S, task 2.2): `thm:projective-invariance` is stated over a field $K$, the block's own
  "the Lean statement holds over an arbitrary field"; the projective reading went to prose.
- `F-179` (S, task 2.2): principle B's moves out of `def:hinge-concurrent`, `def:screw-velocity`
  (its swapped coordinate gloss dropped) and `lem:panel-hinge-dual-molecular`'s setup.
- `F-180` (S, task 2.2): `lem:panel-hinge-dual-molecular`'s (3) is unpinned and its (1) narrower than
  its pin; `lem:screw-determination`'s (2) assumes more than its pin. Kept, with notes.
- `F-183` (S, task 2.3): `F-174`'s call: the realizability sentence asks nondegenerate hinges and
  is proved, unpinned, with a note.
- `F-184` (S, task 2.3): principle B's moves out of `thm:panel-hinge-iff-molecular` (label supply,
  selector, role clauses; new title), `lem:theorem-56-general-position` and
  `def:general-position-placement`.
- `F-187` (S, task 2.4): `lem:molecule-graph-carrier`'s label bound left the statement for its note,
  though one of its pins states it (two readings).
- `F-188` (S, task 2.4): `lem:square-rank-le-genericRank`'s rank form is unpinned; kept, with a note.
- `F-191` (S, task 2.5): four tight-partition statements assume what their pins do not ($V(G)$
  nonempty, $|Q| \ge 2$, $G$ simple, the two vertices nonadjacent); kept, with one note.
- `F-195` (S, task 2.6): `thm:laman-square-count` asks $V$ nonempty, the lemmas the subsection's $G$,
  and two claims are not in their nodes' pins; kept, with one note.
- `F-206` (S, task 2.9): the endpoint selector, the label set and the spanning left five panel
  statements for two notes (two readings).
- `F-207` (S, task 2.9): `thm:panel-generic-rank`'s and `cor:panel-generic-rigid`'s pins are vacuous
  at minimal $k$-dof-graphs (`hends` against `hfresh`); kept, with a note; also 2.12's four pins.
- `F-211` (S, task 2.10): principle B's moves out of `def:two-extensor` (the coordinates' formulas
  and degrees) and `def:generic-endpoints` (the orientation aside), to the prose after them.
- `F-212` (S, task 2.10): the statements assign endpoints to the bars, the polynomial in
  $2d\,|E(G)|$ coordinates; the pins to every edge label. Kept, with a note.
- `F-216` (S, task 2.11): the selector and the label sets left five hinge-point statements, as in
  `F-206`; "a genuine hinge" and "(so $D \ge 2$)" left too (principle B). Two readings.
- `F-217` (S, task 2.11): `lem:hinge-rows-polynomial-in-points`' degree bound is unpinned and
  unused; kept, with a note.
- `F-221` (S, task 2.12): the selector, the spanning and "(equivalently $D \ge 3$)" left the four
  body-hinge statements, as in `F-206` (two readings); `F-207` holds for their pins.
- `F-222` (M, task 2.12): `body-hinge.tex` presents `cor:bodyhinge-generic-tree-packing` as KT
  Proposition 1.1's form for hinges; it is for simple graphs.

## Moved to a later round

`E`, `N`, `T` and `U` findings for round 5, `prose-graph`, and `L` findings for a later Lean round,
one line each naming the ledger ID and the task that found it.

- `F-175` (E, task 2.1): `bar-joint-3d.tex`'s six missing edges and one unbacked.
- `F-176` (L, task 2.1): the docstrings of `GenericRigidityMatroid.lean` (process, a stale sketch).
- `F-181` (E, task 2.2): the first eight nodes of `molecule-modelling.tex`: eight missing, three
  unbacked.
- `F-182` (L, task 2.2): the docstrings of its pins (a swapped $\omega$/$t$ gloss, a stale header).
- `F-185` (E, task 2.3): its last five nodes: nine missing edges, five unbacked, uncited edges.
- `F-186` (L, task 2.3): the docstrings of its pins (a misattribution, process narration).
- `F-189` (E, task 2.4): `molecule-application.tex`'s six missing edges and two unbacked.
- `F-190` (L, task 2.4): the docstrings of its pins (a false count, a loose credit).
- `F-192` (N, task 2.5): two lemmas pin the definitions of a tight partition and of $e_G(Q)$.
- `F-193` (E, task 2.5): the first ten nodes of `jacobs.tex`: two missing edges, three unbacked.
- `F-194` (L, task 2.5): the docstrings of its pins (a dead label, a misdescribed source).
- `F-196` (E, task 2.6): the counting bound's eleven nodes: 18 missing, 14 unbacked, a dead pin.
- `F-197` (N, task 2.6): two lemmas pin definitions beside their claims; the converse's pin is dead.
- `F-198` (L, task 2.6): the docstrings of its pins (split-off labels, JJ's $e_G(P)$ as $d_G(P)$).
- `F-199` (E, task 2.7): its ten nodes: 12 missing edges, one dead pin (`genericRank_eq_rk_image`).
- `F-200` (L, task 2.7): the docstrings of its pins (process narration only).
- `F-201` (E, task 2.8): its five nodes: one missing edge, one dead pin (`degree_one_rank_tree`).
- `F-202` (N, task 2.8): `def:two-core` pins three consequences; the core facts used are unpinned.
- `F-203` (T, task 2.8): "core" names JJ's core here and a contracted set in `main-component.tex`.
- `F-204` (U, task 2.8): README and the home page on the degree-one formula; Jacobs 1998's DOI.
- `F-205` (L, task 2.8): the docstrings of its pins (process narration, a loose credit).
- `F-208` (E, task 2.9): its eleven nodes: eight missing edges, six unbacked, nine dead pins.
- `F-209` (N, task 2.9): the rank-form row extraction and the panel rows' polynomials: no node.
- `F-210` (L, task 2.9): the docstrings of its pins (JJ's genericity, stale text, JJ's year).
- `F-213` (E, task 2.10): its nine nodes: one missing edge, three unbacked, three dead pins.
- `F-214` (N, task 2.10): `def:two-extensor` pins a bijection and a dead polynomial form.
- `F-215` (L, task 2.10): the docstrings of its pins (a false count, JJ's notation and signs).
- `F-218` (E, task 2.11): its five nodes: one missing edge, three unbacked, no dead pin.
- `F-219` (N, task 2.11): two nodes pin a definitional identity or a definition beside a claim.
- `F-220` (L, task 2.11): the docstrings of its pins (JJ §6 credits, an unproved degree bound).
- `F-223` (E, task 2.12): its seven nodes: four missing edges, three unbacked, no dead pin, and the
  nodes the rewritten text cites without an edge.
- `F-224` (N, task 2.12): the induced screw automorphism and the panel meet decomposition: no node.
- `F-225` (L, task 2.12): the docstrings of its pins (JJ §6 credits, a genericity claim for $q_0$,
  process narration).

## Blockers / open questions

- None. The round has no planned stop.

## Hand-off / next phase

**Next concrete task: task 2.13, `intro.tex`, *Organization of the blueprint* and the continuation
paragraph (51–364; the file is unchanged since the open), at Opus**, a fresh agent
(`notes/Prose.md` §2). Its diagnosis is the *2.13* item under *`intro.tex`* in *Per-chapter
diagnosis*, with carry-ins 1–9; `intro.tex`'s kept parts and rules, the gates and the screens are
under *Scope*. Then task 2.14, and task 3 closes the round. What the five rewritten chapters say,
which 2.13 and 2.14 must agree with:
- **From task 2.1.** `bar-joint-3d.tex` (*The generic bar-joint rigidity matroid*) builds
  $\mathcal{R}_d(V)$ in every dimension (Jordán §1.3.1; JJ 2008 §2, Theorems 4.1 and 4.3). Keep
  true: the intro's "in dimension 3" and line 486 (2.13, 2.14).
- **From task 2.2.** The polarity $*$ is defined over every field before
  `lem:panel-hinge-dual-molecular` (over $\R$); `thm:projective-invariance` is over $K$; $\bar c = (c, 1)$.
- **From task 2.4.** `molecule-application.tex`'s opening credits JJ 2008's Conjecture 2.2 (the
  formula), Theorem 4.1 ($\le$) and Theorem 4.3 (its equivalence with their Conjecture 2.1, the
  bar-joint molecular conjecture), and KT p. 671 for KT's deduction: 2.13 and 2.14 agree with it.
  The chapter ends on generic rigidity of squares (JJ Conjecture 2.1, KT §7), citing
  `cor:molecule-generic-rigid`; the intro's "protein-flexibility" and "capstone" (2.13, 2.14) have
  no counterpart in it.
- **From task 2.8.** `jacobs.tex`'s opening credits Jacobs' conjecture to Jacobs 1998 (JJ
  Conjecture 5.1; JJ §5: stated as a result, with an incomplete proof) and the degree-one rank
  formula to JJ Lemma 4.2, part (a) by JJ to Franzblau 2000. That formula does not use the rank
  formula (JJ prove it so that the rank formula at the core gives $r(G^2)$ for every graph), so the
  intro's "two further Jackson--Jordán consequences of the rank formula" (lines 42–43, 332–333) is
  false for the second (2.13, 2.14; `F-204`).
- **From tasks 2.9–2.12.** `generic-lift.tex`'s opening lists the generic forms it proves: the
  molecule rank formula at every generic placement, with the six-trees consequence JJ noted (JJ
  2010 p. 586); the rank formula (KT Proposition 2.3, JJ 2010 Theorem 6.1) at generic normals of a
  simple graph, whose corollary contains JJ Theorem 7.2; Tay's theorem at generic endpoints (JJ
  Lemma 5.1, from Whiteley's framework); the rank formula and Tay and Whiteley's theorem at generic
  hinge points of a simple graph (JJ prove the formula for multigraphs). Genericity is the transfer
  of row independence; it agrees with JJ's maximum-rank genericity for placements and bars and
  implies it for hinge points ($d \ge 2$, no loops), for panels only over nondegenerate hinges.
  `jacksonJordan2009` is JJ 2010 and renders [JJ10].
- **Notation and terms** (*Decisions*); **carry-ins** 1–9 under *Per-chapter diagnosis*.
- **Tools.** The two screens under *Scope*; `scripts/blueprint-deps.py --label <label>` or
  `--chapter <name>`. `lint.sh` 5a bans JJ's "brick" too (2.3 wrote "maximal subgraphs of
  deficiency zero"). The ledger's next ID is `F-226`.

## Decisions made during this round

- **The slicing** (the open): fourteen slices, 2.1–2.14, one more than §3's thirteen, as
  `generic-lift`'s body-and-hinge section splits before `lem:screw-map-rows` (467 lines whole).
- **One notation** (round 3's, carried; carry-in 1). KT's $d$ for the dimension (the bar-joint
  chapters' $d$ already), $D = \binom{d+1}{2}$, $K^{d+1}$, $\bigwedge^{d-1} K^{d+1}$, $\vee$ for
  the join, $\wedge$ for the meet, $*$ for the complement isomorphism; $k$ is only the dof.
  `generic-lift` has it throughout (2.9–2.12); its notes say where the formalization writes
  $d = k + 1$.
- **Terms** (round 3's, carried). The realization record (the endpoint selector, link-recording)
  and the fresh-label supply leave statements, `\cref`ing round 3's note at
  `def:panel-hinge-framework` and `rem:fresh-edge-supply`; "genuine" is "nondegenerate".
- **`bar-joint-3d`'s opening** (2.1): the title drops "in dimension three"; the false sentence on
  $3|V| - 6$ (Jordán's Lemma 1.2.1) is cut, its reading left to `molecule-application.tex`.
- **`molecule-modelling`** (2.2, 2.3): `thm:projective-invariance` over $K$ (`F-178`); `F-174`
  anchored (`F-183`); the equivalence is Whiteley's 2004 manuscript, via JJ §2.1 and KT pp. 650, 671.
- **`molecule-application`** (2.4): "shadowing carrier" replaced, not defined (`F-187`).
- **`jacobs`** (2.5–2.8): JJ introduced once, in the opening, and each JJ result credited as JJ
  state it (Lemma 3.2 from their [10], Lemma 3.3 beside Whiteley's Lemma 9.1.3, Lemma 4.2(a) to
  Franzblau). One note per subsection (`F-191`, `F-195`); the $K_5$ examples, the core's
  maximality and the tree case are argued in prose.
- **`generic-lift`** (2.9–2.12): the selector and "every label is an edge" go to
  `fmlnote:generic-normals-selector` and three unlabelled notes (`F-206`, `F-207`, `F-216`,
  `F-221`); `def:generic-hinge-points` defines the hinge-point assignment, so the polynomial lemma
  follows it (principle E *Node order*). The opening compares the two genericities, with the
  caveats of the three section paragraphs. Witnesses: for bars JJ Lemma 5.1 by Whiteley's argument
  (JJ's Remark) in linear form, our lift $(1, p)$ against JJ's $(p, 1)$; for hinge points KT 5.6's
  realization moved off infinity (JJ Lemma 7.1's choice of coordinates; JJ Theorem 6.4 unused).
  `jacksonJordan2009` says 2010 (*Eur. J. Combin.* 31(2)); the key stays.
