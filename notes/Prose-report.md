# PROSE findings report (round 5, tasks 8.1–8.2)

The report on the `S`, `L` and `M` entries of the ledger `notes/Prose-findings.md`, for the PI
(`notes/Prose.md` §3 *R*). The ledger holds each finding, its evidence and its disposition; this
report groups the entries by the kind of divergence, merges the entries that record one
divergence, ranks the groups, and suggests a disposition and a commit estimate for each. Part 1,
the `S` group, is task 8.1's (2026-10-15). Part 2, the `L` and `M` groups and the graph findings
the round left, and Part 3, the proposed follow-up program, are task 8.2's (2026-10-15). The
report is not a stop (`notes/Prose-graph-cleanup.md` *Autopilot: for the PI*).

**Evidence.** Each item restates its entries' evidence from the ledger, which names what was read
(a declaration's statement or body, never its docstring; a source passage) or measured
(`scripts/blueprint-deps.py`). Where task 8.1 re-checked an item, it says so and names the
statements and bodies it read, at `30c4b950`. *State* is the blueprint as it stands at this
commit.

**Dispositions suggested.** *Keep*: the node and its note stay. *Confirm*: the PI confirms a
round's repair or reading; no commit. *Restate*: a blueprint statement change, which the hygiene
rule leaves to the PI, under round 5's expected-diff gate. *Repin*: a pin added or moved under the
honesty gate. *Lean+*: a new declaration that states the claim, then a pin. *Lean±*: a change of a
signature, definition or structure, with its dependents and the nodes that state them; a recon
first. *Merge/retire*: not among principle D's fixes, so listed in §2.5.

## Part 1 — the `S` group

The 67 `S` entries are statements whose blueprint and formal texts disagreed after the
formalization was declared complete. The prose rounds found them between 2026-10-07 and
2026-10-14 (13 in round 1, 14 in round 2, 20 in round 3, 18 in round 4, 2 in round 5), each at a
node that carried `\leanok`, with every pin resolving under `checkdecls`, except the two unfilled
nodes of `F-038` and `F-234`. Two were resolved in passing by task 3.7's repins (`F-137`,
`F-142`). The PI asked that they be presented as one group, for what they show about the limits of
autoformalization (2026-10-12, `notes/Prose.md` §1): §1.1 collects that material, §1.2–§1.3 rank
the 65 open entries in 42 items, §1.4 adds up the estimates, and §1.5 maps each entry to its item.

### 1.1 What the group shows

Material for the PI's question, not conclusions.

1. **The gates check names; the gates run by eye check hypotheses, once.** `checkdecls` checks
   that each pin exists, and `\leanok` that it compiles without `sorry`. The gates run by eye
   (`blueprint/CLAUDE.md`) read a pin's hypotheses (the honesty gate, whose producer clause also
   scopes a producer's claim to the conjunct built) and a definition's cheapest witness (the
   definition-faithfulness gate), on the commit that adds a `\leanok`; `CLEANUP.md` §A's audit
   compares statements with signatures between phases. The divergences here survived them (kind
   G's readings arose in the rounds' own rewrites). The prose rounds found them by reading each
   pin's statement beside its node (the ledger's *read*), in the opens and the 64 slices of rounds
   1–4 and in round 5's node-shape tasks.
2. **The direction.** In 34 entries the blueprint claims more than its pins prove, or something
   else (five of kind A's, and kinds B–E). In 17 it claims less (kind H, and `F-169`). The rounds
   repaired 4 in place (kind F) and recorded 9 as two readings (kind G); `F-145` is empty in both
   texts; 2 are resolved.
3. **Where they cluster.** The algebraic induction (round 3's chapters, 20 entries) holds ten of
   the thirteen entries of kinds A and B, and `generic-lift.tex` (7 entries) holds S1. There the
   formal proof left Katoh and Tanigawa's route: the blueprint kept KT's statement, and its pin is
   a step, a special case or the linear-algebra core of the route the formalization took (S7,
   S19–S21), or of one it abandoned. Ten open entries (`F-116`, `F-117`, `F-125`, `F-136`,
   `F-138`, `F-145`, `F-149`, `F-150`, `F-158`, `F-165`) and both resolved ones sit at nodes whose
   pins, or the pins at issue, lie outside every main result's closure. The script's dead-pin
   report (`F-012`) is a cheap screen for this kind.
4. **The worst are invisible in either text alone.** S1 and S2 touch main results of
   `formalization.yaml`, and neither the statement nor the pin's signature, read alone, shows the
   gap: it takes a witness. `F-207`'s is the hypothesis pair at a minimal graph, `F-128`'s the
   framework with every normal zero. Both come from a carrier that records less than the
   mathematical object: a label type standing for the edge set (`hends`), a free selector field
   (`ends`). `F-048` (a bar coordinate per copy of an edge) and `F-212` (an endpoint pair per
   label) are the same pattern. Such a carrier makes an existential conclusion weaker, and a
   universal hypothesis stronger, than either reads.
5. **Definitions diverge at corners.** `F-020`: the formal infinitesimal rigidity agrees with
   Jordán's wherever a main result uses it and is weaker at $2 \le |V| \le d - 1$.
6. **The false statements fail at inputs the project's definitions admit**: a reversed
   inclusion (S6), a family of two-extensors for the omit-two one (S9), a hypothesis of the
   setting left out (simple, S8), a form that fails at $D = 1$ (S10), and source claims that fail
   at the degenerate objects the project's definitions admit (S7, S31). The rounds checked them
   and their kin with `lake lean` witnesses (`F-145`, `F-149`, `F-150`), a count by hand (`F-154`)
   and an edge count ($C_7^2$, `F-174`).
7. **Underclaims transcribe standing assumptions.** Kind H adds the source's or the chapter's
   standing hypotheses ($V$ finite, $d \ge 2$, simple, degree two, $V \ne \emptyset$) that the pins
   do not take. They are harmless to soundness, but a node cited in general reads as a special case
   (S38).
8. **A rewrite can move a hypothesis out of sight.** Round 4 moved Lean devices (the endpoint
   selector, the label sets, the label supply) from statements to notes, recording two readings
   (kind G). At S34 the moved pair is S1's.

**Checks the kinds suggest**, for the follow-up that Part 3 proposes:
- for each main result, a non-vacuity witness (its hypotheses met at a minimal input of the
  intended class; S1), and for each existential conclusion the definition-faithfulness gate's
  cheapest witness (S2);
- for every node, a map of its clauses to the pins that prove them: round 5's honesty gate for a
  new node, clause (i) (`notes/Prose-graph-cleanup.md` *Scope*), applied to all (D, E, H);
- a `lake lean` counterexample probe for a statement over a definition that admits degenerate
  objects (B);
- the dead-pin screen, `scripts/blueprint-deps.py`'s report 2, as a trigger to re-read a node
  (A, B, E).

### 1.2 The kinds, ranked

A kind ranks by whether a main result or a status surface is involved, whether a text a reader
trusts is false or empty, the direction (a claim the Lean does not make before one it exceeds),
and the cost. Within a kind, items rank the same way. An item merges the entries that record one
divergence, or one fix at one place.

| Kind | What diverges | Entries | Items |
|---|---|---|---|
| A | One text is vacuous or met trivially | 7 | S1–S5 |
| B | A statement is false as written (four `\leanok`, one unfilled) | 6 | S6–S10 |
| C | The carrier or a definition differs from the source's object | 3 | S11–S13 |
| D | The statement omits a hypothesis its pin assumes | 4 | S14–S17 |
| E | The statement claims what no declaration states | 16 | S18–S30 |
| F | False text that rounds 1–4 repaired in place | 4 | S31–S33 |
| G | The hygiene rule's two readings of a move out of a statement | 9 | S34–S37 |
| H | The pin proves more: the statement is a special case | 16 | S38–S42 |
| — | Resolved in passing by task 3.7's repins | 2 | §1.3, end |

### 1.3 The items

#### A. One text is vacuous or met trivially

- **S1. The generic panel and body-hinge theorems are vacuous at every minimal $k$-dof-graph**
  (`F-207`; the pins of `F-206`, `F-216` and `F-221`). Main result:
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`
  (`cor:bodyhinge-generic-tree-packing`), and the panel form its row names
  (`cor:panel-generic-rigid`). The pins of
  `thm:panel-generic-rank`, `cor:panel-generic-rigid`, `lem:hinge-point-witness`,
  `thm:bodyhinge-generic-rank` and its two corollaries take `hends` (every edge label links its
  selector pair in $G$, so $E(G)$ is the whole label type) and `hfresh` (every minimal
  $k'$-dof-graph on the bodies misses some label). At $G' = G$ these contradict each other
  whenever $G$ is itself minimal: a single edge, a tree, every minimal $0$-dof-graph. The pins are
  not empty: $|E(G)| > D(|V| - 1)$ gives `hfresh` (`rem:fresh-edge-supply`), for instance $K_7$
  at $d = 2$; which graphs between the two they cover is not settled. The statements,
  `formalization.yaml`'s row and README's paragraph state the theorem without this scope.
  *Evidence:* ledger (read; a `lake lean` witness). Re-checked from the main result's signature
  (`GenericLift/HingeGeneric.lean`): `hfresh _ G hmin` gives $e_0 \notin E(G)$, and `hends e₀`
  gives $e_0 \in E(G)$.
  *State:* kept; the notes after `cor:panel-generic-rigid` and
  `cor:bodyhinge-generic-tree-packing` say it.
  *Suggested:* Lean±: index the families by $E(G)$, so that the label set may exceed $E(G)$
  (`F-207`'s candidate); `rankHypothesis_of_theorem_55_gen` takes its label supply as a bound on
  the label type (`hcard`), with no `hends`. Then restate the notes, the row and README. Until
  then, state the scope on the row and in README (docs).
  *Estimate:* 1 docs commit; a recon, then 3–5 commits.
- **S2. The endpoint selector is free and hinges may be degenerate, so KT Theorem 5.6's main
  result is met by a zero framework** (`F-122`, `F-125`, `F-128`). Main results:
  `rankHypothesis_of_theorem_55_gen` (`thm:theorem-55-6`) and `molecular_conjecture`.
  `PanelHingeFramework` records for each edge label a pair of bodies, `ends`, and computes the
  hinge from their normals; nothing ties the pair to the ends of the edge. So `IsHingeCoplanar`
  holds whenever each hinge is the meet of the panels of some two bodies, and the panel side of
  `molecular_conjecture` (nonzero hinges, rigid) states no condition on `Q.ends`. The pins of the
  KT Theorem 5.6 nodes conclude `∃ Q, Q.graph = G ∧` the rank hypothesis, with no condition on
  `Q.ends` or on the hinges, while the statements, since round 3's task 2.1, take each hinge from
  its edge's ends; both texts allow degenerate hinges. At deficiency zero the conclusion is met by
  the framework with every normal zero, for every spanning $0$-dof-graph: each hinge is zero and
  welds its ends, and a $0$-dof-graph is connected. `cor:theorem-55-d3-spanning`'s pin (dead, no
  caller) is met the same way without its hypothesis. The link-recording form with nondegenerate
  hinges is proved (`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, the second pin of
  `thm:theorem-55-6-genuine`).
  *Evidence:* ledger (read: the structure, `toBodyHinge`, `IsHingeCoplanar`, the pins' statements
  and `reaimSub`). Re-checked from the statements of `rankHypothesis_of_theorem_55_gen` and
  `molecular_conjecture` (`Theorem55.lean`), the bodies of `RankHypothesis` and `hingeConstraint`,
  and `panelSupportExtensor_ne_zero_iff` (two dependent normals give a zero hinge).
  *State:* kept; `fmlnote:panel-hinge-nondegenerate`, the note after `def:hinge-coplanar` and the
  theorems' notes say it.
  *Suggested:* docs first: the KT Theorem 5.6 row cites the nondegenerate, link-recording form
  beside or in place of `rankHypothesis_of_theorem_55_gen` (a `declaration:` change, which task 7
  did not make). Then Lean±: the link condition in the structure, or in the main results'
  conclusions as additive successors. Retiring the dead $d = 3$ corollary is G6's.
  *Estimate:* 1 docs commit; a recon, then 2–4 commits for successors, or a phase for a structure
  field (every constructor of `PanelHingeFramework`).
- **S3. The KT eq. (6.12) placement pin assumes what no framework of Cases II and III has**
  (`F-150`; `lem:case-II-realization-placement`). `case_II_placement_eq612` assumes a subgraph
  `Gv ≤ G` without $v$, on $|V(G)| - 1$ vertices, rigid on its vertex set with nondegenerate
  hinges. Such a subgraph has deficiency zero, so for $|V(G)| \ge 3$ it is a proper rigid subgraph
  of $G$, which Cases II and III exclude; the pin is dead. The statement, from a rigid realization
  of the splitting-off $G_v^{ab}$, holds by round 3's proof, with no pin behind it.
  *Evidence:* ledger (read; a `lake lean` witness of `Gv.deficiency n ≤ 0`).
  *State:* kept, with a note.
  *Suggested:* keep; or Lean+ (the count at a rigid splitting-off, which
  `lem:case-II-realization`'s proof gives) and repin. Retiring the node is G4's (`F-152`).
  *Estimate:* 0, or 2 commits.
- **S4. A Case II assertion that holds only vacuously** (`F-145`; `lem:case-II`,
  `lem:splitoff-edge-substitution`). The second assertion of `lem:case-II`, as its pin
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` (`hspan`), asks that every
  motion $S$ of the framework on $G_v$ with $S(v) = 0$ have $S(a) \in \operatorname{span} C(e_a)$.
  As $v$ lies on no edge of that framework, every screw gives such a motion, so the hypothesis
  makes a line the whole screw space: the assertion is vacuous for $d \ge 2$, in both texts. The
  first assertion is weaker than its pin (which holds for every framework, set and body);
  `lem:splitoff-edge-substitution`'s "$G_v^{ab}$ is not a subgraph of $G$" has no pin; the old
  title named KT Lemmas 6.7 and 6.8, which neither assertion is.
  *Evidence:* ledger (read; KT pp. 677–679; a `lake lean` witness).
  *State:* kept, in register only; the gloss dropped, the titles corrected, the notes say it. The
  three nodes of `F-147` are dead.
  *Suggested:* restate: drop the vacuous assertion. Retiring the dead nodes is G4's.
  *Estimate:* 1 commit.
- **S5. A Case III statement that every graph meets** (`F-169`;
  `lem:case-III-chain-discriminator`). The statement asks for normals $q$, a nonzero form $r$
  vanishing on $C(q(v_0), q(v_2))$, and $r(C(q(u_i), n')) \ne 0$ for some $i$ and some $n'$
  independent of $q(u_i)$; with $q(v_0) = q(v_2)$ this holds for any graph. The pin
  `chainData_fire_discriminator` gives far more (general position, KT eq. (6.52), and
  $D(|V(G)| - 2)$ independent rows of $R(G_1, q)$), all of which `lem:case-III-chain-dispatch`'s
  pin uses.
  *Evidence:* ledger (read).
  *State:* kept; the proof derives the rest, and the note says that the pin gives it.
  *Suggested:* restate to the pin's conclusion (a strengthening).
  *Estimate:* 1 commit.

#### B. A statement is false as written

S6–S9 are `\leanok` nodes whose statements still read as below; one commit could restate all four.

- **S6. The monotonicity of the motions, with the inclusion reversed** (`F-049`;
  `lem:rank-rotation-semicont`, `rigidity-matrix.tex`). The statement: if
  $\operatorname{span} C(p(e)) \subseteq \operatorname{span} C(p'(e))$ at every edge, then
  $Z(G,p') \subseteq Z(G,p)$. The pin `infinitesimalMotions_mono_of_span_le` assumes the reverse
  inclusion, under which that conclusion holds; under the stated one it fails (a hinge with
  $C = 0$ welds its two bodies, one with $C \ne 0$ does not). The title's KT Lemma 5.2 is neither
  pin; `meet.tex`'s note gives that role to
  `PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals`.
  *Evidence:* ledger (read; KT pp. 668–669). Re-checked from the pin's statement and the body of
  `hingeConstraint` ($S(u) - S(v) \in \operatorname{span}\{C(e)\}$), `RigidityMatrix/Basic.lean`.
  *Suggested:* restate with the pin's inclusion, and retitle; the KT Lemma 5.2 attribution goes
  where its formal form is pinned.
  *Estimate:* 1 commit.
- **S7. The genericity device: false at degenerate hinges, and its pins hold at the given point**
  (`F-117`, `F-149`; `lem:genericity-device`). Read with `def:rigidity-matrix`, the statement (each
  locus $\{q : \operatorname{rank} R(G,q) \ge r\}$ is Zariski-open) fails at degenerate hinges: for
  the graph with one edge the rank is $D$ on the closed set of dependent normals and $D - 1$
  elsewhere. The pins say less: `exists_good_realization` gives a point $p$ with
  $\#s + \dim Z \le D|V|$ when the rows indexed by $s$ are independent at $p_0$, which $p_0$ itself
  satisfies, and `exists_good_realization_const` the bound at one framework. The open-set form,
  with nondegenerate hinges, is `lem:rank-polynomial-of-le-finrank`'s pin,
  `exists_rankPolynomial_of_le_finrank_linking`. `lem:relative-device-count` and
  `lem:realization-of-independent-rows` hold at the given normals in the same way (`F-152`), as
  `lem:rows-polynomial-in-normals`'s old pin did (`F-137`).
  *Evidence:* ledger (read; KT p. 668; a `lake lean` witness: a zero hinge forces $S(u) = S(v)$).
  *State:* kept; the proof assumes nondegenerate hinges and says so, and the remark after it gives
  the example. The pins are dead (`F-152`); seven proofs cite the node for a step that no main
  result's proof takes (`F-118`, M3).
  *Suggested:* restate with nondegenerate hinges (KT §5.1's nonparallel realizations) and repin on
  `exists_rankPolynomial_of_le_finrank_linking`; or join the node to
  `lem:rank-polynomial-of-le-finrank` (a merge, G3).
  *Estimate:* 1–2 commits.
- **S8. A Case III rank bound that fails without simplicity** (`F-154`;
  `lem:case-III-nested-rank-lower`). The statement omits two hypotheses of its pin
  `exists_nested_rankPolynomial_lower_all_k`: $G$ simple (`hSimple`) and the induction hypothesis
  (`hIH`). Without simplicity it fails: at $d = 2$, the graph with the edges $va$, $vb$, $cb$ and
  two edges $ac$ is a minimal $0$-dof-graph in which $v$ has degree two, and wherever the two
  hinges of $(G_v, q)$ are nondegenerate its rank is at most $4 < 5$. For a simple $G$ the omitted
  induction hypothesis loses nothing (KT Theorem 5.5 at $G_v$).
  *Evidence:* ledger (read; the example's deficiencies by hand).
  *State:* kept; the proof assumes both, the note gives them, and the paragraph after it the
  example.
  *Suggested:* restate: add "simple".
  *Estimate:* 1 commit.
- **S9. Two-extensors stated to span $\bigwedge^{d-1} K^{d+1}$** (`F-060`;
  `lem:case-III-claim612-extensor-span`). The statement: the $D$ joins $\bar p_i \vee \bar p_j$ of
  $d + 1$ linearly independent vectors span $\bigwedge^{d-1} K^{d+1}$. A join of two vectors lies
  in $\bigwedge^2$, so this holds only at $d = 3$. The pin `span_omitTwoExtensor_eq_top` is about
  the omit-two extensors, each the join of the other $d - 1$ vectors, which are the proof's
  $E_{ij}$.
  *Evidence:* ledger (read: the pin's statement).
  *Suggested:* restate as the omit-two family.
  *Estimate:* 1 commit.
- **S10. An unfilled node that fails at $D = 1$** (`F-234`; `lem:forest-surgery-unsplit`). No
  declaration proves its forest form (each forest of $\tilde H$ extends to a forest of
  $\widetilde{H^v_{ab}}$ with one more edge), stated for every $D$; at $D = 1$ neither multigraph
  has an edge, and its proof uses the copy $(vb, 1)$. `splitOff_indep_extend_of_fiber_lt` proves
  the form of independent sets, for $D \ge 2$ and distinct $a, b$.
  *Evidence:* ledger (read: the pin's statement; the node's statement and proof).
  *State:* unfilled; task 3.4 found it under the honesty gate.
  *Suggested:* restate in the pin's form and fill it, or retire the node (`F-091`, G4).
  *Estimate:* 1 commit.

#### C. The carrier or a definition differs from the source's object

- **S11. `Graph.BodyHingeFramework` holds bars, not hinges** (`F-048`; `def:body-hinge-framework`,
  `thm:body-hinge-tay`). Main result: `body_hinge_tay`. The structure records a multigraph and a
  two-extensor coordinate for each of the $D - 1$ copies of every edge, degenerate ones allowed,
  and no hinge, where the definition gives each edge a $(d-2)$-dimensional affine subspace, its
  hinge, and its copies a basis of the Plücker vectors of the lines that meet it. So
  `body_hinge_tay` is Tay's body-bar theorem on $(D - 1)G$: its proof is
  `edgeMultiply_isSparse_iff` with `tutte_nash_williams`.
  *Evidence:* ledger (read; `notes/Phase16.md`). Re-checked from the structure and the theorem's
  statement and body (`BodyBar/BodyHinge.lean`).
  *State:* the definition's formalization note says it, and every status surface since task 7
  (`F-099`). The form with hinges is `cor:bodyhinge-generic-tree-packing`, which S1 finds vacuous
  at minimal graphs.
  *Suggested:* keep; S1's fix makes the form with hinges cover them.
  *Estimate:* 0.
- **S12. Infinitesimal rigidity is weaker than Jordán's for $2 \le |V| \le d - 1$** (`F-020`;
  `def:isInfinitesimallyRigid`). `IsInfinitesimallyRigid` asks $\dim \ker R(G,p) \le d(d+1)/2$,
  where Jordán (2016, pp. 36–37) asks rank $S(|V|, d)$. The two agree for $|V| \ge d$ and
  $|V| \le 1$, so always at $d = 2$; for $2 \le |V| \le d - 1$ the formal notion is weaker (two
  unjoined vertices in $\R^3$ satisfy it), and `IsGenericallyRigid` inherits it. No main result is
  affected: the characterization is at $d = 2$, and the hypotheses of the $d = 3$ results exclude
  $|V| = 2$.
  *Evidence:* ledger (read; a `lake lean` witness on `Fin 2` at $d = 3$). Re-checked from the
  definition's body (`Framework.lean`).
  *State:* `fmlnote:infinitesimal-rigidity` says it (round 1, task 5.4).
  *Suggested:* keep; Lean± to Jordán's bound only if a later result needs small $|V|$ at
  $d \ge 3$.
  *Estimate:* 0.
- **S13. Endpoint assignments are indexed by labels, not bars** (`F-212`; `def:generic-endpoints`,
  `lem:generic-endpoints-abundance`). The pins give a pair to every edge label, and the abundance
  polynomial has $2d$ variables for each label; the statements give pairs to the bars of $G$ and a
  polynomial in their $2d\,|E(G)|$ coordinates. The rows read only the bars' pairs, so the forms
  are equivalent, but no declaration says that the polynomial involves only the bars'
  coordinates.
  *Evidence:* ledger (read).
  *State:* kept, with the note after the definition.
  *Suggested:* keep; or Lean±, indexing by $E(G)$, with S1's refactor.
  *Estimate:* 0, or within S1's.

#### D. The statement omits a hypothesis its pin assumes

- **S14. Three Case I statements** (`F-141`; `lem:case-I-realization-h65`, `lem:case-I-dispatch`,
  `lem:case-I-realization`). The first omits a proper rigid subgraph (`hrig`), which KT Lemma 6.5
  (p. 676) assumes and KT Claim 6.6 needs; without it the statement is Case III at $k = 0$, which
  also needs the induction hypothesis at positive deficiencies. The second omits the induction
  hypothesis (`hIH`). The third assumes realizations of $H$ and $G/E(H)$, its pin the induction
  hypothesis for every smaller graph, of which the proof uses those two instances.
  *Evidence:* ledger (read; KT pp. 673–676).
  *State:* kept; the proofs run under the pins' hypotheses, with a sentence and a note each.
  *Suggested:* restate the first two with their pins' hypotheses; keep the third.
  *Estimate:* 1 commit.
- **S15. KT Lemma 5.4's range** (`F-115`; `lem:cycle-realization`). The statement takes KT's
  range, cycles on $3 \le m \le D$ vertices. The pin `cycle_realization` assumes `cy.m ≤ n + 1`,
  so it covers $3 \le m \le d + 1$, fewer once $d \ge 3$, and the note gives the formalized range
  as $m \le d$, one less than the pin's. KT's one use (the proof of their Lemma 6.13, p. 692)
  needs $m \le d$.
  *Evidence:* ledger (read: the pin's statement and the step `hnk` of its body; KT pp. 670, 692).
  *Suggested:* restate to the pin's range, which loses nothing KT use; correct the note.
  *Estimate:* 1 commit.
- **S16. Loops** (`F-124`; `lem:generic-yields-genuine-hinge`). The statement covers every
  multigraph with at least two vertices and a generic full-rank realization; the pin
  `hasPanelRealization_of_generic` assumes `[G.Loopless]` and returns the generic framework
  itself, whose hinge at a loop is zero. The claim holds with loops (a loop gives no row, and its
  hinge can be replaced by a nonzero extensor of its panel); the pin's three callers apply it to
  simple graphs.
  *Evidence:* ledger (read: the pin and its callers).
  *State:* kept; the proof treats loops, and the note says that the pin assumes none.
  *Suggested:* restate with "loopless", or Lean+ the case with loops.
  *Estimate:* 1 commit.
- **S17. An extra conjunct the pin does not use** (`F-102`; `lem:case-cut-edge-realization-gp`).
  The pin `case_cut_edge_realization_gp_gen` also assumes nondegenerate-hinge panel realizations
  of the smaller minimal graphs, the second conjunct of the hypothesis that
  `theorem_55_minimalKDof_k_all_k` inducts on; its proof uses only the first, which the statement
  states.
  *Evidence:* ledger (read: the pin and its call).
  *State:* kept, with a note; `F-104` (`L`) records the conjunct and an unused `_hV3`.
  *Suggested:* Lean±: drop both, in the later Lean round.
  *Estimate:* 1 commit.

#### E. The statement claims what no declaration states

- **S18. KT Proposition 2.3 at a generic realization** (`F-121`; `prop:rigidity-matrix-prop11`).
  The statement is the rank formula (KT Proposition 2.3, Jackson and Jordán's Theorem 6.1) at a
  generic panel-hinge realization with nondegenerate hinges. The pin `rigidityMatrix_prop11` takes
  any body-hinge framework with every hinge nonzero, assumes the generic bound
  $\dim Z(G,p) \le D + \operatorname{def}(\tilde G)$ (`hgen`) and closes by `omega` from the
  genericity-free bound. No pin shows that a generic realization meets `hgen`; `def:dof-generic`
  is unfilled. The formula at every generic realization is `generic-lift.tex`'s
  (`thm:panel-generic-rank`, `thm:bodyhinge-generic-rank`), with no edge to this node, and with
  S1's vacuity.
  *Evidence:* ledger (read; measured).
  *State:* kept, with a note; the callers prove `hgen` for the realizations they build.
  *Suggested:* after S1, restate as the conditional form and cite the generic forms, or repin on
  them.
  *Estimate:* 1 commit, after S1.
- **S19. KT eq. (6.3)'s rank addition** (`F-116`; `lem:case-I`, a crux node). The statement: for a
  minimal $k$-dof-graph $G$ with a proper rigid subgraph $H$, $(G,p)$ attains the target rank if
  and only if $\operatorname{rank} R(G,p) = D(|V(H)| - 1) + \operatorname{rank} R(G/E(H), p_2)$.
  No pin mentions the contraction, minimality or the identity: the three pins are block-pin
  criteria for any framework, two of them dead. `lem:case-I-realization`'s proof argues the rank
  addition in full.
  *Evidence:* ledger (read; measured).
  *Suggested:* keep, with a note naming the live route; or Lean+ (the identity); the crux
  carve-out keeps the proof's depth either way.
  *Estimate:* 0, or 2–3 commits.
- **S20. Case III's counts at KT's three frameworks are pinned on linear algebra** (`F-158`,
  `F-165`; `lem:case-III-candidate-row`, `lem:case-III-claim612-p2-placement`,
  `lem:case-III-claim612-p3-placement`). The statements are KT's counts (pp. 684–689): if a block
  of KT eq. (6.29), (6.30) or (6.41) is nonsingular, the rank at $(G, p_i)$ is at least
  $D(|V(G)| - 1)$. Their pin, `linearIndependent_sum_augment_candidateRow` at three roles, is
  linear algebra on families of forms, with no graph, framework or rank. (The open of round 3 took
  $p_1$ where the block is singular; its task 2.12 anchored $p_1$ at KT eq. (6.12).) Since task
  3.9 the graph-level count `case_III_rank_certification` is pinned at
  `lem:case-III-rank-certification`, and KT's $(G, p_1)$ at `def:case-III-candidate`.
  *Evidence:* ledger (read; three `lake lean` witnesses; KT pp. 678, 682–691).
  *State:* kept, with notes; the three nodes' pins are dead (`F-159`, `F-167`).
  *Suggested:* repin the three on `case_III_rank_certification` at their roles, or merge them into
  `lem:case-III-rank-certification` (G3).
  *Estimate:* 1 commit.
- **S21. KT Claim 6.4 as a polynomial, pinned on a point** (`F-138`; `lem:claim-6-4`). The
  statement gives a nonzero polynomial off whose zeros the rows of $G \setminus E(H)$ have rank
  $D(|s_c| - 1)$. The pin `rigidContract_exterior_rank_transport_htransport` gives one point (KT's
  choice in the proof of the claim) and assumes $G/E(H)$ simple, of deficiency zero, which the
  statement's hypotheses do not give (the proof needs only that it has no loops). The open-set
  form for every $k$ is `lem:rank-polynomial-IH-relabel-proj`'s, which the formal Case I reaches.
  *Evidence:* ledger (read; KT p. 675; measured).
  *State:* kept, with a note; the pin is dead (`F-139`).
  *Suggested:* merge into `lem:rank-polynomial-IH-relabel-proj` (G3), or restate at the
  point.
  *Estimate:* 1 commit.
- **S22. KT Theorem 4.9's sequence** (`F-101`; `thm:minimal-kdof-reduction`). Part (i), KT's
  sequence of minimal $0$-dof-graphs down to the two-vertex double edge, is stated by no
  declaration; part (ii), the induction principle, is the pin's. The sequence follows from the pin
  with `isMinimalKDof_ncard_le_two_trichotomy` and `rigidContract_isMinimalKDof` ($D \ge 2$), as
  the proof derives it.
  *Evidence:* ledger (read).
  *State:* round 2 split the statement into (i) and (ii), with a note that (i) is not formalized.
  *Suggested:* Lean+ (the sequence) and a pin, or keep.
  *Estimate:* 1–2 commits, or 0.
- **S23. KT Lemma 3.4's tree partition** (`F-083`; `lem:circuit-induces-rigid`). The statement
  says that $X - e$ is the union of $D$ edge-disjoint spanning trees on $V(X)$. The pins state the
  count and the rigidity of $G[V(X)]$, and no declaration applies `isSpanningTreePacking_of_isTight`
  (`cor:k-spanning-trees`) to a circuit.
  *Evidence:* ledger (read: the pins; the callers).
  *State:* kept; the proof derives it from the count, and a note says it is not formalized.
  *Suggested:* Lean+ (one application) and a pin, or keep.
  *Estimate:* 1 commit, or 0.
- **S24. The rank of the union of a family** (`F-051`; `thm:matroid-partition-rank`). The
  statement gives the rank of every $X$ in the union of any finite family, and the independence
  criterion for any family. `Matroid.Union_rank_eq` gives the rank at $X = E$,
  `Matroid.Union_pow_rk_eq` every $X$ for copies of one matroid, and the criterion is proved only
  in that case (the unpinned `Matroid.Union_pow_indep_iff_count`), the only one used later.
  *Evidence:* ledger (read); `adjMap_rk_eq` with `sum'_rk_eq_rk_sum` would give the family form.
  *State:* kept, with a note; `formalization.yaml` says it since task 7.
  *Suggested:* Lean+ (the family form at every $X$, and the criterion), or keep.
  *Estimate:* 2–3 commits, or 0.
- **S25. The pebble game's failure witness** (`F-041`; `thm:pebble-game-correct`). The statement
  adds to its pin's equivalence that the set of a returned failure witness is a blocking witness
  for $G$. That is proved inside the pin's proof and the bodies of `runPebbleGame.aux` and
  `runPebbleGameExec.aux`, but no declaration states it. The statement's other addition is two
  other nodes' pins.
  *Evidence:* ledger (read: the pin and the two bodies).
  *Suggested:* Lean+ (the witness clause) and a pin, or keep.
  *Estimate:* 1 commit, or 0.
- **S26. A rank form whose declaration is unpinned** (`F-188`; `lem:square-rank-le-genericRank`).
  "Equivalently, $\operatorname{rank} R(H, p) \le r_d(H)$" has no pin. The unpinned
  `finrank_range_rigidityMap_le_genericRank` states it, and `lem:molecule-rank-lower-bound`'s pin
  uses it.
  *Suggested:* repin: add it as the clause's pin.
  *Estimate:* 1 commit.
- **S27. A degree bound no declaration proves** (`F-217`; `lem:hinge-rows-polynomial-in-points`).
  The statement claims a polynomial of degree at most $d - 1$. `hingeExtensorPoly` is a
  $(d-1) \times (d-1)$ minor of a matrix whose entries are indeterminates or $1$, so the bound can
  be read off it, but no declaration states it, and nothing uses it.
  *Evidence:* ledger (read: the two pins' bodies).
  *State:* kept, with the note after the proof; since task 3.11 the node pins
  `hingeExtensorPoly_eval` alone.
  *Suggested:* restate without the bound, or Lean+ (the total degree of the minor).
  *Estimate:* 1 commit.
- **S28. One of two symmetric cases** (`F-113`; `lem:complement-iso-decomposable-wedge-perp`). The
  statement covers $n \in \{n_1, n_2\}$ for linearly independent $n_1, n_2$; its second and third
  pins state only $n = n_1$, and assume no independence. The case $n_2$ follows by alternation,
  inline in the proof of `complementIso_smul_eq_extensor_join`.
  *Evidence:* ledger (read).
  *Suggested:* restate to $n_1$, or Lean+ the case $n_2$.
  *Estimate:* 1 commit.
- **S29. The molecular dictionary's scalars and field** (`F-180`; `lem:panel-hinge-dual-molecular`,
  `lem:screw-determination`). The rescaling, the ledger's part (3) and now part (2) of the first
  lemma (normals $\lambda_v \bar c(v)$), has no pin: its pins state part (1) at the normals
  $\bar c(v)$. The polarity, the ledger's part (1), is `lem:polarity-join` since task 3.11, stated
  over $\R$, where its pins are field-general. `lem:screw-determination`'s part (2) asks a finite
  family and every non-collinear triple; its pin takes any index type and one triple.
  *Evidence:* ledger (read; the body of `exists_molecular_rankHypothesis_generalPosition`, which
  proves the rescaling inline). Re-checked from the statements of the first lemma's pins
  (`Molecule/Duality.lean`).
  *Suggested:* restate `lem:polarity-join` over $K$ and the screw part (2) as its pin's
  (strengthenings); pin the rescaling or keep its note.
  *Estimate:* 1 commit.
- **S30. Claims that round 2 narrowed or moved to prose** (`F-084`, `F-107`, `F-112`).
  `lem:reduction-step`'s contraction branch states the matroid form its pin proves, and the graph
  form is `lem:rigidContract-isMinimalKDof`'s (the PI kept the narrowing on 2026-10-12; task 3.5
  moved that node, `F-098`). The claim that both branches of `lem:chain-cycle-dichotomy` occur, and
  `def:meet`'s property of supporting extensors, moved to the prose after their nodes, where it
  proves them; no declaration states either (the meet's is formalized for two hyperplanes).
  *Evidence:* ledger (read).
  *Suggested:* keep. The double pin of `lem:reduction-step` is G2's (`F-096`, `F-120`).
  *Estimate:* 0.

#### F. False text that rounds 1–4 repaired in place

Three more repairs ride with other items: S20's $p_1$, S25's edge lists (each edge once, also at
`thm:pebble-game-soundness`, `F-036`), and S37's swapped components of a screw.

- **S31. The molecular frameworks and the squares of graphs** (`F-174`, `F-183`;
  `thm:molecular-iff-square-bar-joint`, a crux node). Read with `def:hinge-concurrent`, which
  admits coincident centres, the old "in particular" was false: with all centres equal every hinge
  is welded and the molecular framework of a connected $G$ is rigid, while the square of $C_7$ has
  $14 < 3 \cdot 7 - 6$ edges. Round 4 anchored it to nondegenerate hinges ($c(u) \ne c(v)$ at every
  edge), "Moreover": the modelling equivalence of Whiteley and Jackson–Jordán, now true and proved
  in the prose, with no pin (the pin gives the dimension equality at one placement). Two readings
  were recorded: anchoring a definition's domain, or a hypothesis added to a false claim.
  *Evidence:* ledger (read; JJ 2008 §2.1; KT pp. 650, 671; Whiteley 1999 p. 27).
  *Suggested:* confirm; Lean+ the equivalence, whose steps are pinned
  (`thm:panel-hinge-iff-molecular`, `lem:relative-deficiency-rank-bound`,
  `lem:exists-generic-general-position`).
  *Estimate:* 0, or 2–3 commits.
- **S32. "Both subgraphs of $G$"** (`F-136`; `lem:case-I-splice-seed`). The open of round 3 glued
  $H$ and the contraction $G/E(H)$, "both subgraphs of $G$"; the contraction is not one when an
  edge outside $H$ has an end in $V(H) \setminus \{r\}$. The pin glues two subgraphs. Round 3 kept
  the contraction, stated with the hinges of $p$, and dropped the gloss; the statement holds, as a
  motion of $(G,p)$ constant on $V(H)$ is a motion of $(G/E(H), p)$, a step no pin states.
  *State:* the pin is dead (`F-139`).
  *Suggested:* confirm; keep.
  *Estimate:* 0.
- **S33. The blocking witness's two readings** (`F-038`; `def:blockingWitness`, unpinned). The
  definition's two sentences differed when $\ell > k|V'|$. Round 1 added $\ell \le k|V'|$, the
  reading the reject verdict carries (`PebbleGameResult.reject`'s `h_size` and `h_lt`); the
  coordinator accepted it, and the hygiene rule sends it to the PI.
  *Suggested:* confirm.
  *Estimate:* 0.

#### G. The hygiene rule's two readings of a move out of a statement

Round 4 moved Lean devices, and principle B moved definitions' consequences, out of statements,
and recorded two readings each: an anchoring that leaves the claim (principle E's "a Lean-side
device … stays out of statements"), or a statement that now drops what its pins carry.

- **S34. `generic-lift.tex`'s selector, label sets and spanning** (`F-206`, `F-216`, `F-221`). The
  endpoint selector, the label sets, "every label is an edge", the spanning and the separate
  dimension parameter went to notes, in fourteen nodes. The dropped pair `hends`, `hfresh` is
  S1's.
  *Suggested:* reading two until S1's fix, then reading one.
  *Estimate:* 0 (S1 carries the work).
- **S35. The label supply** (`F-187`; `lem:molecule-graph-carrier`). The bound of more than
  $6(|V| - 1)$ labels went to the note; one of the five pins, `card_shadowLabel_lt`, is that
  bound. `shadowGraph`, a pinned helper, stays with a role map (`F-010`).
  *Suggested:* restate with the bound as a clause, so the statement says what its pins prove; or
  confirm.
  *Estimate:* 1 commit, or 0.
- **S36. The molecular realization theorem and its general position** (`F-184`;
  `thm:panel-hinge-iff-molecular`, `lem:theorem-56-general-position`,
  `def:general-position-placement`). The selector, the label bound and the spanning went to notes,
  the theorem's title changed, and the definition's consequence (an injective placement with no
  three points collinear) went to the prose, with a proof. The theorem keeps "In particular" (at
  $\operatorname{def}(\tilde G) = 0$, an infinitesimally rigid molecular realization), which its
  pin does not state; `rankHypothesis_zero_iff` gives it.
  *Suggested:* confirm; pin the "In particular" on `rankHypothesis_zero_iff`, or keep its note.
  *Estimate:* 0, or 1 commit.
- **S37. Definitions' consequences and setups** (`F-177`, `F-178`, `F-179`, `F-211`).
  `def:genericRigidityMatroid`'s independence of $p$ (another node's statement) and
  `def:genericRank`'s role clause; `thm:projective-invariance` stated over a field $K$, which its
  seven pins hold over (`pencil.tex` reads it so); `def:hinge-concurrent`'s five sentences and its
  selector, and `def:screw-velocity`'s gloss, which swapped the two components (dropped, the
  components defined by their values); `def:two-extensor`'s degrees of its coordinates (since task
  3.11 `twoExtensorPoly` is unpinned, and `lem:two-extensor-polynomial` states the polynomial form
  without a degree, as its pin does).
  *Suggested:* confirm reading one.
  *Estimate:* 0.

#### H. The pin proves more: the statement is a special case

- **S38. Two special cases cited in general** (`F-239`; `lem:case-II-placement-old-rows-extract`,
  `lem:case-II-placement-block-independent`). The first is stated for a realization of a
  splitting-off; its pins hold for every body-hinge framework rigid on its vertex set, and the
  proofs of `cor:panel-generic-rigid` and `cor:bodyhinge-generic-rigid` cite its dimension count
  for such a framework. The second is stated for rows of $R(G,q)$; its pin holds for any two
  families of linear forms on the screw assignments, the second vanishing on those that vanish off
  $v$, and `lem:rigidityRows-pinned-placement-rank-add` uses it so.
  *Evidence:* ledger (read: the pins; the citing proofs).
  *Suggested:* restate both generally (`F-152`'s third candidate).
  *Estimate:* 1 commit.
- **S39. Domains the pins do not need** (`F-079`, `F-086`, `F-191`, `F-195`). `lem:rk-within-parts`
  for the set of all edges within parts, where the pin holds for every such set, the form the
  formal proof of `thm:def-eq-corank` uses; `lem:acyclic-insert-vfiber` and `lem:packing-move` at
  a vertex of degree two, unused; four tight-partition lemmas of `jacobs.tex` with a nonempty
  $V(G)$, $|Q| \ge 2$, $G$ simple or nonadjacent vertices, which their pins do not ask
  (`main-component.tex` reads the merge lemma for $m \ge 1$ parts); `thm:laman-square-count` with
  $V$ nonempty, and the counting lemmas with the subsection's $G$, where of 23 pins one asks the
  minimum degree. `F-195` also has two clauses that are another node's pin or an equality of
  counts.
  *State:* kept; `fmlnote:tight-partition-consumed-forms` and `fmlnote:normal-cross-split` say it.
  *Suggested:* keep; restate the merge lemma, and `lem:rk-within-parts`, whose general form the
  formal proof of `thm:def-eq-corank` uses.
  *Estimate:* 0–2 commits.
- **S40. The pebble game's $\ell < 2k$** (`F-034`, `F-036`). `lem:pebble-game-invariants` assumes
  $V$ finite and $\ell < 2k$, and `thm:pebble-game-soundness` $\ell < 2k$; their pins assume
  neither, parts (1)–(2) of the invariants hold for every vertex and finite $V'$, and no proof uses
  $\ell < 2k$.
  *Suggested:* restate: drop $\ell < 2k$, and give each part of the invariants its own hypotheses.
  *Estimate:* 1 commit.
- **S41. $d \ge 2$ in Tay's theorems** (`F-058`; `thm:tay-witness`, `thm:body-hinge-tay`). Main
  results `tay_witness` and `body_hinge_tay` hold for every $d$; the proof of
  `lem:edge-multiply-sparse` applies `thm:tay-witness` for every $d$.
  *Suggested:* restate: drop $d \ge 2$.
  *Estimate:* 1 commit.
- **S42. Finiteness** (`F-015`, `F-026`, `F-027`, `F-028`, `F-031`, `F-037`, `F-042`, `F-046`).
  Fifteen nodes of round 1's chapters assume $V$ finite, or $G$ finite, where their pins take only
  finitely many edges, decidable equality or a linear order, or nothing.
  *Suggested:* keep; or one restatement sweep.
  *Estimate:* 0, or 1 commit.

**Resolved in passing by task 3.7** (`d851de0f`; dispositions `done`):
`lem:rows-polynomial-in-normals` was pinned on `exists_good_realization_ofParam`, which states no
polynomial and holds at the given point (S7's pattern), and is repinned on `annihRowPoly_eval`,
`annihRowPoly_totalDegree_le` and `span_annihRow_eq_dualAnnihilator`, a pin per clause (`F-137`);
`lem:case-I-realization-nonsimple`, KT Lemma 6.2 for every $d \ge 2$, was pinned on the dead
$d = 3$ wrapper and is repinned on `case_I_realization_nonsimple_gen`, which matches its dimension
and, assuming less of the smaller graphs, proves more (`F-142`).

### 1.4 Estimates

If the PI takes every suggestion, the items' estimates add up to:
- **docs** (the status surfaces' scope for S1 and S2): 2 commits;
- **blueprint restatements and repins** (S4–S10, S14–S16, S18 after S1, S20, S21, S26–S29, S35,
  S36, S38–S42): 24 items, about 10 commits when batched by chapter, each under the expected-diff
  gate;
- **Lean** (S1 and S2 after a recon each; S17, S22–S25, S31): 13–20 commits; 18–26 with the
  optional S3, S16 and S19; more if S2 takes a structure field;
- **no commit** (confirm or keep): S11–S13, S30, S32–S34, S37.

The smallest set that leaves no `\leanok` statement false and no main result's scope unstated is
S6–S9 (one blueprint commit, S7's repin aside) and S1–S2's surfaces (one docs commit).

### 1.5 Entry → item

`F-015` S42 · `F-020` S12 · `F-026` S42 · `F-027` S42 · `F-028` S42 · `F-031` S42 · `F-034` S40 ·
`F-036` S40 · `F-037` S42 · `F-038` S33 · `F-041` S25 · `F-042` S42 · `F-046` S42 · `F-048` S11 ·
`F-049` S6 · `F-051` S24 · `F-058` S41 · `F-060` S9 · `F-079` S39 · `F-083` S23 · `F-084` S30 ·
`F-086` S39 · `F-101` S22 · `F-102` S17 · `F-107` S30 · `F-112` S30 · `F-113` S28 · `F-115` S15 ·
`F-116` S19 · `F-117` S7 · `F-121` S18 · `F-122` S2 · `F-124` S16 · `F-125` S2 · `F-128` S2 ·
`F-136` S32 · `F-137` resolved · `F-138` S21 · `F-141` S14 · `F-142` resolved · `F-145` S4 ·
`F-149` S7 · `F-150` S3 · `F-154` S8 · `F-158` S20 · `F-165` S20 · `F-169` S5 · `F-174` S31 ·
`F-177` S37 · `F-178` S37 · `F-179` S37 · `F-180` S29 · `F-183` S31 · `F-184` S36 · `F-187` S35 ·
`F-188` S26 · `F-191` S39 · `F-195` S39 · `F-206` S34 · `F-207` S1 · `F-211` S37 · `F-212` S13 ·
`F-216` S34 · `F-217` S27 · `F-221` S34 · `F-234` S10 · `F-239` S38.

## Part 2 — the `L` and `M` groups, and the graph findings the round left

Part 2 reports the 76 `L` entries (§2.1–§2.3) and the 6 `M` entries (§2.4), recounted at
`f6ddebb5`: 61 `L` entries from rounds 1–4 and 15 from round 5. §2.5 lists the `E` and `N`
entries that round 5 left, wholly or in part, for a merge, a retirement, a pin change or a Lean
change, with `F-012`'s liveness, the one entry that had no disposition. §2.6 reports a stale
example in an agent manual, §2.7 adds up the estimates, and §2.8 maps each entry to its item.
Part 3 proposes the follow-up program. No PROSE round edits the Lean, so every `L` entry
describes the tree as it stands at this commit, and the `L` items carry no *State* line.

Beyond Part 1's vocabulary, Part 2 suggests: *Docs*, a status surface or a design document;
*Lean (text)*, a docstring or comment, no declaration changed; *Delete*, a declaration removed
after `CLEANUP.md` §B's check (a trial deletion and a full build); *PI*, a choice the report
cannot make.

### 2.1 What the `L` group shows

1. **The bar for notice set the coverage.** Each `L` entry was met while a slice read its pins
   (the ledger's *bar for "notice"*); no slice ran a Lean audit. So the group covers the files the
   blueprint pins, unevenly, and says nothing of the rest of the library. Its systematic
   companions are the ledger's two Lean baselines (the smell counts and the twenty longest proofs,
   round 1's task 2), inputs for a Lean round that are not entries.
2. **Most entries are docstrings.** Of the 76, 53 have a false or stale docstring as their main
   content (kinds LB, LC and LF), 13 a hypothesis (LD), 8 dead or repeated code (LE), and 2 the
   executable pebble game (LA). Most docstring entries mix several faults: a label, a claim, a
   credit, and process narration (phase numbers, design codes, "brick", "producer").
3. **Each move of a pin makes docstrings stale.** The project's docstrings name the blueprint
   label they serve, and nothing checks the name. Round 5's node-shape tasks moved or unpinned
   pins in every chapter, and its 15 entries (`F-230`–`F-250`) are the docstrings that now name
   the node a pin left, a label that no longer exists, or none. Rounds 1–4 found the same after
   the phases' moves (`F-040`, `F-064`, `F-069`, `F-153`, `F-194`).
4. **A docstring written beside the proof can carry the blueprint's error.** Eleven entries state
   false mathematics (L4), and eight repeat a divergence that Part 1 records for the node's
   statement (L3).
5. **An underscore hides an unused hypothesis.** Lean's unused-variables linter and the
   `unusedArguments` linter of `lake lint` both exempt a binder whose name starts with `_`. Five
   entries are such hypotheses (`_hinj`, `_hdeg2`, `_hV3` twice, `_hSimple`, and three in
   `chainWalk_charging`), and `F-024` an unused argument under a `@[nolint unusedArguments]` whose
   comment calls the report a false positive. Seven more are derivable from the other hypotheses.
6. **One entry is a behaviour, not a text.** The depth-first search under the executable pebble
   game marks only the current walk, so it is exponential where its docstrings, `DESIGN.md` and
   `Main.lean` call the game polynomial-time (L1).

**Checks the kinds suggest**, for Part 3:
- a script that reads each blueprint label a Lean docstring names and checks that it exists and
  that the declaration is among its pins (L10–L11; run on the commit that moves a pin, it would
  have caught round 5's 15 entries there);
- a `grep` of the signatures for underscore-prefixed hypotheses and for `nolint unusedArguments`
  (L6);
- the dead-pin screen (`scripts/blueprint-deps.py`'s report 2) beside a `grep` for callers, to
  find dead declarations (L9), with §B's trial deletion before any deletion.

### 2.2 The `L` kinds, ranked

As in Part 1: a user-facing behaviour or a false text a reader trusts ranks first, then a
signature, then code that only costs maintenance, then a text that only misleads navigation.

| Kind | What | Entries | Items |
|---|---|---|---|
| LA | Code whose behaviour contradicts its documentation | 2 | L1–L2 |
| LB | A docstring states false mathematics | 19 | L3–L4 |
| LC | A docstring misattributes or miscites | 9 | L5 |
| LD | A hypothesis unused, derivable, or stronger than the proof needs | 13 | L6–L7 |
| LE | A derivation repeated, or a declaration dead | 8 | L8–L9 |
| LF | A docstring stale: a label, a status, process narration | 25 | L10–L12 |

### 2.3 The `L` items

#### LA. Code whose behaviour contradicts its documentation

- **L1. The pebble game's search is exponential** (`F-033`; `Search/DFS.lean`). The search
  `reachableFindingAux` passes `insert v visited` to every recursive call from `v`, so sibling
  calls do not share their marks, and when no vertex satisfies `P` it follows every simple walk
  from `v`. On a chain of $n$ diamonds ($2^n$ simple walks end to end) a timing grew from 2 ms at
  $n = 8$ to 3071 ms at $n = 18$, about five times per two diamonds; `reachClosureComputable` runs
  the search once per vertex. The section docstring calls this "$O(n)$ DFS invocations — quadratic
  in the worst case". Lee and Streinu's $O(m_a n)$ bound for the basic game (§3, p. 1430) counts
  each search as linear, as a search keeping one marked set across siblings would be. `dfs.tex`
  describes the per-walk marking since round 1 (task 5.12); `executable.tex` claims no bound.
  *Evidence:* ledger (read: the body; measured, script not retained). Re-checked from the body
  (`Search/DFS.lean`, the recursive call at line 588).
  *Suggested:* docs and Lean (text) first: the docstrings, `DESIGN.md` and `Main.lean` say what
  the search does (exponential in the worst case, no bound proved; L2). Then Lean±: one visited
  set threaded through the siblings, with `reachableFinding_sound` and `_complete` re-proved; a
  recon first, as the completeness proof inducts along the walk (`dropUntilBundle`).
  *Estimate:* within L2's commits; a recon, then 2–4 commits.
- **L2. The `decide`, running-time and input claims** (`F-047`; `DESIGN.md` *One `Decidable`
  instance per project predicate*, `Main.lean`, `PebbleGame/Examples.lean`, `lakefile.toml`).
  `DESIGN.md` says that the pebble-game instances' bodies are what `decide` unfolds, and that they
  run in polynomial time. `reachableFindingAux` and `tryAddEdgeWith` are defined by well-founded
  recursion and are irreducible: `by decide` fails on `(⊤ : SimpleGraph (Fin 2)).IsLaman` and on
  `k4MinusE.IsLaman`, `decide +kernel` proves only the first, and `native_decide` proves both. The
  docstrings of `Main.lean` and `Examples.lean` and the `lakefile.toml` comment claim polynomial
  time and "a sub-second bytecode-interpreter run". `Main.lean` and the comment call the input
  "whitespace-separated", where `parsePair` splits on spaces only (`String.splitOn`'s default), so a
  tab makes a line malformed; the comment routes the classification through the `Decidable`
  instances, where `classify` calls `runPebbleGameExec`; and `Main.lean` points at a "three-row
  matrix" in `executable.tex` that round 1 made a list.
  *Evidence:* ledger (read; measured, script not retained). Re-checked: `DESIGN.md`'s section, which
  still says both, and `parsePair` (`Main.lean`, line 100).
  *Suggested:* docs: `DESIGN.md`'s section, with L1's sentence. Lean (text): the docstrings and the
  comment; and `parsePair` split on any whitespace, or the texts say spaces.
  *Estimate:* 1 docs commit; 1 Lean commit.

#### LB. A docstring states false mathematics

- **L3. Docstrings that repeat a divergence of Part 1** (`F-123`, `F-133`, `F-135`, `F-148`,
  `F-153`, `F-161`, `F-164`, `F-215`). Each states beside the formal proof the reading from which
  Part 1 finds the node's statement to diverge: the field `ends` as "the two bodies `e` joins",
  and the hinges of `P.withGraph G'` in their bodies' panels, which nothing enforces (S2; `F-123`,
  `F-133`); `rigidityMatrix_prop11` "for a generic panel-hinge realization" (S18; `F-123`); KT
  Lemma 5.4 for $3 \le m \le D$ (S15; `F-135`); `hspan` at the normals of KT Claim 6.9 (S4;
  `F-148`); `Gv` as the splitting-off (S3; `F-153`); the candidate row lifting the rank at normals
  where the block is singular (S20; `F-161`); each omit-two extensor as "the join $p_i \vee p_j$"
  (S9; `F-164`); a polynomial "in the `2n|E(G)|` endpoint coordinates" (S13; `F-215`). The same
  entries also name stale roles, which L12 sweeps.
  *Evidence:* ledger (read: the docstrings and bodies).
  *Suggested:* Lean (text), with each `S` item: the fix of the statement decides the docstring.
  *Estimate:* within the `S` items' commits, or the docstring sweep (Part 3).
- **L4. Docstrings with false mathematics of their own** (`F-018`, `F-022`, `F-032`, `F-057`,
  `F-061`, `F-074`, `F-130`, `F-168`, `F-182`, `F-190`, `F-210`).
  - `molecular_conjecture`'s says that dropping the nonzero-hinge conjunct "makes the statement
    false"; dropped from both sides, each side holds exactly when $G$ is connected, as a zero hinge
    welds its ends, so the equivalence still holds (`F-130`).
  - `countMatroid`'s says that the augmentation axiom can fail at $(3, 6)$; every
    $(3,6)$-sparse graph has no edges, and those edge sets form a matroid (`F-032`, a `lake lean`
    witness).
  - `matroidMG`'s places the $(D,D)$ count in "the boundary regime `ℓ = 2k = D`"; it has
    $\ell = k < 2k$, and `countMatroid`, on `Sym2 V`, does not apply because it has no parallel
    edges (`F-074`).
  - `ScrewVelocity.lean`'s header swaps $\omega_S$ and $t_S$, and `screwComplementIso`'s says that
    the polarity never preserves nondegeneracy, which `supportExtensor_mapExtensor_ne_zero`
    contradicts (`F-182`).
  - `Carrier.lean`'s header: the labels `Sym2 V` are too few exactly when $2 \le |V| \le 9$, not
    "e.g. for `Nat.card V ≤ 10`" (`F-190`).
  - `IsGenericNormals` "subsumes" Jackson and Jordán's maximum-rank condition only over
    nondegenerate hinges; "`G̃ = G.shadowGraph`" names $G'$, where $\tilde G = 5 G'$ (`F-210`).
  - KT's frameworks $(G, p_2)$ and $(G, p_3)$ described as other splittings-off, a conjunct
    transported that the statement lacks, and a branch `hsplitZero` that does not exist (`F-168`).
  - The standard-basis vectors called "degenerate two-extensors" on the Plücker variety
    "vacuously" (they are the Plücker vectors of lines, Whiteley 1988 p. 243), and a docstring
    assuming a spanning-tree packing where the statement assumes tightness (`F-057`).
  - `linearIndependent_hingeRow_forest` and `exists_independent_rigidityRows_of_forest` named and
    documented for spanning forests, where their hypothesis `hsep` holds only when every component
    is a star; the rows of any forest of nondegenerate hinges are independent, and no declaration
    states it (`F-061`).
  - "distinct vertices `x, y`" for a statement that does not assume it (`F-018`), and a hypothesis
    listed that the statement does not take (`F-022`).
  *Evidence:* ledger (read: the docstrings against the bodies; two `lake lean` witnesses).
  Re-checked: `molecular_conjecture`'s docstring and statement (`Theorem55.lean`).
  *Suggested:* Lean (text). `F-061`: Lean±, a rename with its callers (both outside every main
  result's closure, `F-233`), and optionally Lean+, the forest lemma.
  *Estimate:* within the docstring sweep; `F-061` 1 commit, its lemma 1–2.

#### LC. A docstring misattributes or miscites

- **L5. Credits, sections, pages and equation numbers** (`F-023`, `F-094`, `F-156`, `F-172`,
  `F-186`, `F-194`, `F-205`, `F-220`, `F-225`; also parts of `F-057`, `F-088`, `F-108`, `F-126`,
  `F-140`, `F-153`, `F-161`, `F-190`, `F-198`, `F-210` and `F-215`, and the docstrings of M2 and
  M4). Rounds 1–4 corrected the blueprint's credits; the docstrings keep the old ones.
  - Jackson and Jordán 2010: "§6" for constructions JJ do not make (six docstrings each in `F-220`
    and `F-225`), their Lemma 7.1 placed in §6 (`F-225`), the formula "due to" JJ, who conjectured
    it and proved one inequality and its equivalence to the Molecular Conjecture (`F-190`), their
    Lemma 3.2 taken from "their companion paper" (`F-194`), `twoCore` credited to their Lemma 4.2,
    defined before it (`F-205`), $d_G(P)$ for their $e_G(P)$ (`F-198`), $c_0$ for $p_0$ and the
    signs of their entry table (`F-215`), and the year 2009 in three files (`F-210`).
  - Katoh and Tanigawa: Lemmas 4.3–4.5 for 4.3(i) with 4.4 (`F-094`); p. 660 for p. 661 (`F-156`);
    §6.4.1 and Lemma 6.10 for Lemma 6.13, "§6.4 §1.48(1)", and p. 659 for p. 677 (`F-172`);
    eq. (6.46) for KT Lemma 4.6's chain (`F-108`); p. 669 for p. 670 (`F-126`); Claims 6.4 and 6.9
    for the genericity device (`F-153`); eq. (6.26) for (6.13), and (6.16) for the shear identity
    (`F-161`); `hglue` as Claim 6.4 (`F-140`).
  - Others: Asimow–Roth for a count that `trivial-motions.tex` dropped as unverified (`F-023`);
    Whiteley 1988 Theorem 13, which is about frameworks on the flat torus (`F-057`); the modelling
    equivalence of Whiteley and Jackson–Jordán for the projective duality (`F-186`).
  *Evidence:* ledger (read: the docstrings; the sources in `.refs/` at the pages named).
  *Suggested:* Lean (text), with the chapters' credits as the reference.
  *Estimate:* within the docstring sweep.

#### LD. A hypothesis unused, derivable, or stronger than the proof needs

- **L6. Unused hypotheses** (`F-024`, `F-075`, `F-077`, `F-092`, `F-104`, `F-140`; also `F-094`'s
  `heab`, `F-108`'s three in `chainWalk_charging` and `F-126`'s `_hSimple`). The body never uses
  `[Finite V]` in `trivialMotionFamily_linearIndependent`, under a `@[nolint unusedArguments]`
  whose comment calls the report a false positive (`F-024`, a `lake lean` witness); `hD` in
  `deficiency_eq_of_cutEdges_ncard_le_one`, which two callers take only to pass on (`F-075`);
  `_hinj` (`F-077`); `_hdeg2` in the two `splitOff_indep_extend` lemmas (`F-092`); `_hV3` in
  `case_cut_edge_realization_gen` and `_gp_gen`, with the second conjunct of the latter's
  hypothesis (S17; `F-104`); and the three hypotheses of
  `rigidContract_exterior_rank_transport_htransport`'s conclusion, discarded by `intro _ _ _ _`
  (`F-140`).
  *Evidence:* ledger (read: the statements and bodies).
  *Suggested:* Lean±: drop each with its callers; where a blueprint statement names one, restate
  it with S17 (`lem:cut-edge-decomposition` already states its parts without `hD`).
  *Estimate:* 2–3 commits.
- **L7. Hypotheses derivable from the others, or stronger than the proof needs** (`F-013`,
  `F-017`, `F-021`, `F-039`, `F-063`, `F-070`, `F-108`). `hab` beside `G.Adj a b` (`F-013`) and
  beside the independence of $p(b) - p(a)$ and $p(c) - p(a)$ (`F-021`); `hF_finite` from `hF_sub`
  (`F-017`); `hloops` from `himg` in three pebble-game theorems (`F-039`, a `lake lean`
  witness); `hcLoop` from minimality (`F-070`); `hV3` beside `hV4`, and `[G.Simple]` by
  `simple_of_isMinimalKDof_of_noRigid` (`F-108`). `F-063`'s nonzero extensor at every label, where
  the relative bound in the same file asks it only at the edges, is stronger than needed.
  `F-097`'s `hV3` rides with L8.
  *Evidence:* ledger (read: the statements, bodies and callers).
  *Suggested:* Lean±: derive each in the body, or ask `F-063`'s at the edges only; the blueprint
  statements already omit most of them.
  *Estimate:* 2–3 commits.

#### LE. A derivation repeated, or a declaration dead

- **L8. A derivation repeated, or longer than it needs** (`F-055`, `F-088`, `F-097`; also
  `F-108`'s triangle). `exists_forestPacking_cover_of_isSparse_restrict` derives the forward half
  of `tutte_nash_williams` again, and both its callers then make the cover disjoint in the five
  lines that the theorem's proof uses (`F-055`). `exists_balanced_forest_packing` makes inline the
  move of `exists_packing_move_of_not_inc`, while its docstring says it uses it (`F-088`; the node
  is `F-087`'s, G5). In `splitOff_isMinimalKDof_of_pos`, the case $e = e_0$ applies KT Lemma 4.7,
  but the criterion step of the other case settles it, so the proof needs neither KT Lemma 4.7 nor
  `lem:edge-set-indep-pos` and holds for $D \ge 2$ (`F-097`). `isKDof_zero_of_triangle` proves
  again the case $m = 3$ of `isKDof_zero_of_cycle` (`F-108`).
  *Evidence:* ledger (read: the bodies).
  *Suggested:* Lean±: one lemma giving a disjoint cover; the descent calling the move, which makes
  `lem:packing-move`'s pin live; the shorter case, its node's edges re-read; the triangle as an
  instance of the cycle.
  *Estimate:* 3–4 commits.
- **L9. Dead declarations** (`F-114`, `F-144`, `F-232`, `F-237`, `F-238`; also parts of `F-104`,
  `F-233`, `F-236` and `F-242`). With no caller outside themselves, and outside every main
  result's closure: the five $d = 3$ base wrappers `theorem_55_base_producer_*` (`F-237`), the
  three Case I wrappers `case_I_realization_nonsimple`, `_all_k` and `_h65` (`F-144`, `F-238`),
  the three `Fin m` cycle forms (`F-238`), six of the eight declarations unpinned from the $d = 3$
  meet lemma, `case_III_realization_of_line` among them, and `blockPiSpan` with two lemmas
  (`F-232`), the lemmas of `meet.tex`'s route through $\bigwedge^2 W$ (`F-114`), and
  `CycleData.vertexSet_ncard` (`F-236`). Four forest-row lemmas have callers only in dead
  `CaseI.lean` code (`F-233`), and `exists_homogeneousIncidence_of_normals` one, the dead $d = 3$
  dispatch (`F-242`). Round 5 unpinned all of these but `meet.tex`'s lemmas, which pin its dead
  step nodes (G4), and three of `F-233`'s, which pin the dead `lem:own-end-rows-independent`
  (`F-061`). `minimal_kdof_reduction` has no caller and pins KT Theorem 4.9 (`F-104`): it stays.
  *Evidence:* ledger (read: a `grep` for each name's callers; measured, the dead-pin report).
  *Suggested:* Delete the unpinned ones; a pinned one goes with its node (G3–G4).
  *Estimate:* 2–3 commits.

#### LF. A docstring stale: a label, a status, process narration

- **L10. Labels that do not exist, or name another node, from rounds 1–4** (`F-040`, `F-064`,
  `F-069`, `F-085`, `F-132`, `F-198`; also parts of `F-077`, `F-080`, `F-088`, `F-092`, `F-097`,
  `F-130`, `F-144`, `F-148`, `F-153`, `F-164`, `F-168`, `F-194` and `F-225`). Labels that do not
  exist: three in the pebble game, with two consumers (`F-040`), `lem:rigidityRows-cut-rank-add`
  (`F-064`), `lem:case-I-realization-all-k` (`F-069`), `lem:case-I-splice-placement` (`F-153`),
  `lem:tight-partition-cross-pair` (`F-194`). Elsewhere the label of another node, mostly one the
  declaration served before a phase or round 2 split it.
  *Evidence:* ledger (read: the docstrings; a `grep` for each label in `blueprint/src`).
  *Suggested:* Lean (text); then §2.1's label check keeps them current.
  *Estimate:* within the docstring sweep.
- **L11. Docstrings that name a node their pin left in round 5** (`F-230`, `F-233`, `F-235`,
  `F-236`, `F-240`–`F-246`, `F-250`; also `F-232`, `F-237` and `F-238`). Each of round 5's
  node-shape tasks 3.1–3.14 and its task 5.3 has an entry: the docstrings of the declarations it
  moved, pinned or unpinned name the node they left, a label the blueprint lacks
  (`lem:case-III-claim612-r`, `lem:pencil-nondegenerate`, "`lem:case-III general-d`"), or no
  node, and two of task 5.3's place a node in its old chapter. Each entry lists its declarations
  and their nodes now.
  *Suggested:* Lean (text), from each entry's list.
  *Estimate:* 2–3 commits by chapter group, or within the sweep.
- **L12. Status, roles and process narration** (`F-030`, `F-035`, `F-045`, `F-080`, `F-126`,
  `F-176`, `F-200`; also most entries of rounds 3–4). Docstrings that describe an earlier state of
  the code: a result called "the eventual Phase 8 target" in the file that proves it, and an
  induction on edges that inducts on vertices (`F-030`); lemmas that "follow in a subsequent
  commit" and are there (`F-035`); a body described as calling a lemma it does not call, the one
  whose step uses $\ell < 2k$ (`F-045`, S40); results "deferred" or "remaining" that are proved
  (`F-080`); `HasFullRankRealization` as the motive of KT Theorem 5.5's induction, which runs on
  other predicates (`F-126`); and phase numbers, design codes and words such as "brick",
  "producer", "seed" and "genuine" across `Molecular/` (each entry of rounds 3–4 lists its file's).
  *Evidence:* ledger (read: the docstrings against the bodies).
  *Suggested:* Lean (text): a sweep by directory, each docstring read against its body, which
  takes L3–L5 and L10–L12 together.
  *Estimate:* the sweep: 8–12 commits (Part 3).

### 2.4 The `M` group

The six entries are attributions and the presentation of the route; ranked as the kinds are.

- **M1. A body-hinge corollary cited for multigraphs** (`F-222`; `body-hinge.tex`). After
  `thm:body-hinge-tay` the chapter says that for frameworks "with hinges in general position", KT
  Proposition 1.1's form (a multigraph $G$ has an infinitesimally rigid body-hinge framework if and
  only if $\tilde G$ contains $D$ edge-disjoint spanning trees) "is"
  `cor:bodyhinge-generic-tree-packing`, and the note after `def:body-hinge-framework` calls the
  corollary the rigidity statement for frameworks with hinges. The corollary and its pin are for
  simple graphs with $|V| \ge 2$, $d \ge 2$ and an infinite field, at generic hinge points, and S1
  finds them vacuous at minimal graphs; for multigraphs the formalization has only the form for
  bundles of bars (S11).
  *Evidence:* ledger (read: the chapter, the pin's statement; JJ 2010 §6, p. 582).
  *State:* unchanged (`body-hinge.tex`, lines 70–79 and 144–152).
  *Suggested:* blueprint prose: "for simple graphs", and S1's scope once settled; or Lean+, the
  multigraph form (JJ Theorem 6.1 holds for multigraphs), with S1's refactor.
  *Estimate:* 1 commit; a phase's work for the multigraph form.
- **M2. The planar characterization credited to Lovász and Yemini** (`F-025`;
  `formalization.yaml`, Lean docstrings). Jordán (2016) credits the characterization of
  generically rigid graphs in the plane, and so the identification of row-independence with
  $(2,3)$-sparsity, to Laman (Theorem 2.2.1, p. 45), and credits Lovász and Yemini with the rank
  formula (Theorem 2.3.2, p. 49) and the rigidity of 6-connected graphs (Theorem 2.4.1, p. 51).
  Rounds 1 and 4 moved the blueprint's credit to Laman, and round 1's close
  `notes/BlueprintExposition.md`'s. `formalization.yaml` still lists Lovász–Yemini 1982 as a
  reference that the project "formalizes" at its "main theorem (rigidity matroid = (2,3)-count
  matroid)", and credits them in its scope, in the description of
  `linearRigidityMatroid_eq_rigidityMatroid` and in its statements' list; task 7 left these lines
  for this report. Docstrings in `RigidityMatroid.lean`, `LamanTheorem.lean`,
  `MatroidIdentification.lean`, `LinearRigidityMatroid.lean` and `CountMatroid.lean` give the same
  credit, and `Sparsity.lean`'s the pendant attachment that round 1 dropped from the chapter.
  *Evidence:* ledger (read: Jordán 2016 pp. 45, 49, 51, in `.refs/`). Lovász–Yemini 1982 is not
  in `.refs/`. Re-checked: `formalization.yaml`'s four lines at this commit, and a `grep` of the
  Lean for the names (the blueprint has none).
  *Suggested:* docs: credit Laman on the four lines, and keep the 1982 reference only for what it
  proves (*PI*: it formalizes neither the rank formula nor the 6-connected theorem); Lean (text),
  the docstrings.
  *Estimate:* 1 docs commit; within the docstring sweep.
- **M3. Off-route nodes in Cases I–III** (`F-118`; `algebraic-induction/`). The chapters present as
  steps of the induction several nodes that no main result's proof takes: the genericity device
  (`lem:genericity-device`, S7), KT Claim 6.4's point form (`lem:claim-6-4`), the splice seed, Case
  II's accounting (`lem:case-II`, S4), the eq. (6.12) placement
  (`lem:case-II-realization-placement`, S3), the relabel lemmas and Case III's candidate completion
  (S20). Round 5's edge policy took their `\uses` off the live nodes (tasks 4.4–4.5 removed the
  realizations' edges to the genericity device, and task 3.7's repin made
  `lem:case-I-realization-nonsimple` live): their users now are dead nodes,
  `lem:case-III-chain-dispatch`'s proof edge to `lem:case-III-claim612-p2-placement`, and
  `lem:theorem-56-general-position`'s proof edge to `lem:genericity-device`, which task 4.7 kept for
  a step the proof cites and the script finds with no Lean basis. The proofs keep eleven `\cref`s of
  `lem:genericity-device`, most as "the argument of".
  *Evidence:* ledger (measured); re-checked from the dump's `## uses:` section at `f6ddebb5` and a
  `grep` for the `\cref`s.
  *Suggested:* *PI*: how the chapters present KT's route beside the formal one. Keep KT's exposition
  with the notes (round 5's default), collapse each off-route group into a remark
  (`blueprint/CLAUDE.md`'s pattern for a whole dead route), or retire it (G4).
  *Estimate:* G4's.
- **M4. Two credits left in docstrings** (`F-053`, `F-081`). The blueprint and
  `formalization.yaml` carry the corrected credits: the matroid of a submodular function to
  Edmonds and Rota, the union's rank to Nash-Williams and Edmonds, Edmonds 1965's Theorem 1 as the
  partition criterion (`F-053`), and KT eq. (2.4) as JJ's Theorem 4.1(a) at $\tilde G$ (`F-081`).
  The docstrings of `Submodular.lean` and `Union.lean`, and of `rank_add_deficiency_eq`,
  `isBase_ncard_add_deficiency_eq`, `le_rank_add_deficiency` and
  `deficiency_eq_zero_iff_exists_spanningTrees`, keep the old ones.
  *Evidence:* ledger (read: Oxley 2011 pp. 404–430, Schrijver pp. 725–726, 775, Edmonds 1965
  p. 69, JJ 2010 pp. 580–583, KT 2011 pp. 655–656, all in `.refs/`). Re-checked:
  `formalization.yaml`'s rows for both.
  *Suggested:* Lean (text), with L5.
  *Estimate:* within the docstring sweep.
- **M5. Pollaczek-Geiringer 1927** (`F-228`). The blueprint, README and the home page credit the
  planar characterization to Laman 1970 alone, as Jordán does (2016, p. 45). Recent literature
  also credits H. Pollaczek-Geiringer, *Über die Gliederung ebener Fachwerke*, ZAMM 7(1) (1927),
  58–72 (DOI `10.1002/zamm.19270070107`, Crossref checked). The paper is not in `.refs/`, and its
  content was not read.
  *Suggested:* *PI*: obtain and read it; if it states the characterization, credit both where the
  blueprint names the theorem's originator.
  *Estimate:* 0, or 1 commit after the reading.

### 2.5 The graph findings the round left

Principle D's fixes are a split, an unpinning and a leave, so round 5 left a merge, a retirement and
any change to the Lean (*Scope*), and task 4 filed three pin changes after task 3 closed. Of the 28
`E` and `N` entries left wholly or in part, 19 are here, with `F-012`. The other nine were left with
a reason that needs no follow-up: nodes kept with a role map (`F-009`, `F-010`), the order of two
chapters (`F-029`), exposition (`F-065`, `F-068`), an edge the pins use (`F-129`), a statement at
its pin's strength (`F-131`'s `lem:extensor-pair-in-panel`, `F-197`'s
`lem:singleton-part-converse`), and an edge that the definition's one pin backs (`F-219`).

- **G1. Three pin changes that task 4 filed** (`F-247`, `F-248`, `F-249`). `thm:pencil-x0-bridge`
  pins the rank that a path of bridges adds, a step of its proof, which `lem:block-rank-path`'s pin
  applies, so a `\uses` runs from `rigidity-matrix.tex` into the last chapter (`F-247`).
  `lem:case-III-claim612-block-iff-perp` pins `mem_hingeRowBlock_iff`, a fact about
  `def:hinge-row-block` that `lem:screw-map-rows` uses (`F-248`). `def:pencil-x0-reduces` pins
  `Graph.IsOpenEar`, the open ears that *Ears and cycles* defines in prose, so every node whose
  pins take an ear reaches the definition of a reduction (`F-249`).
  *Suggested:* repin: a node for the rank lemma in `rigidity-matrix.tex`, or its unpinning; the
  pin on `def:hinge-row-block`; a definition node for ears in *Ears and cycles*. Blueprint only,
  under round 5's expected-diff gate.
  *Estimate:* 2–3 commits.
- **G2. Pins two nodes share** (`F-120`, `F-096`; S30). Ten declarations are pinned twice.
  `Graph.contraction_isMinimalKDof` proves `lem:reduction-step`'s part (ii), KT Lemma 3.5 at
  $k = 0$, the narrowing the PI kept (2026-10-12), and `lem:contraction-minimality`'s claim. In
  `case-iii.tex`, `lem:case-III-claim-6-11-base` restates on its one pin the forward half of
  `lem:splitoff-kdof-criterion` and does not use it, and
  `lem:case-III-claim612-points-affineIndep-witness` and `lem:case-III-claim612-points-affineIndep`
  state one claim on one dead pin. In `pencil.tex` and `main-component.tex`,
  `pencilPair_of_nonempty` is the claim of `thm:pencil-conditioned-pair-nonempty` and the general
  claim of `thm:pencil-realization-theorem`, a main result's node, and six pins, four of
  `thm:pencil-x0-main-component` and two of `thm:pencil-x0-generic-attains`, state lemmas their
  proofs cite. Each double leaves an edge that the script cannot back (task 3.14's decision).
  *Suggested:* merge `lem:case-III-claim-6-11-base` into `lem:splitoff-kdof-criterion`, and the
  two affine nodes into one (or retire both, G4); keep the pencil doubles, where a theorem
  restates the lemmas it assembles, and `lem:reduction-step`'s, which the PI kept.
  *Estimate:* 1–2 commits.
- **G3. A node that restates a general form** (`F-090`, `F-134`, `F-139`, `F-152`, `F-159`,
  `F-167`; S7, S20, S21). `cor:forest-surgery-deficiency` restates `lem:forest-surgery-split` on a
  `@[deprecated]` narrative-bridge shim with no caller (`F-090`). `lem:cycle-realization-base` is
  `lem:theorem-55-base` applied to `P.toBodyHinge` (`F-134`). `lem:claim-6-4` states at $k = 0$
  the claim of `lem:rank-polynomial-IH-relabel-proj` (S21; `F-139`). `lem:genericity-device`'s
  open-set form is `lem:rank-polynomial-of-le-finrank` (S7; `F-152`). Case III's three count nodes
  state KT's counts on a linear-algebra pin, where `lem:case-III-rank-certification` states the
  graph-level count (S20; `F-159`, `F-167`).
  *Suggested:* merge each into its general form, with the comparison as prose; Delete the shim.
  *Estimate:* 2–3 blueprint commits; the shim with L9.
- **G4. KT's route where the formal proof leaves it** (`F-134`, `F-139`, `F-147`, `F-152`,
  `F-159`, `F-163`, `F-167`, `F-171`, `F-111`, `F-091`; M3). Dead nodes round 5 kept as KT's
  exposition: Case I's `lem:cycle-realization-dim-bound`, `lem:exists-independent-panel-extensor`
  and the three `lem:pinned-motions-on-*` lemmas (`F-134`), `lem:case-I-splice-seed` and the two
  dead pins of `lem:case-I` (`F-139`); Case II's `lem:case-II-rank-lift` and `lem:case-II` (S4;
  `F-147`); `lem:relative-device-count`, `lem:realization-of-independent-rows`,
  `lem:case-II-placement-old-rows` and `lem:case-II-realization-placement` (S3; `F-152`); Case
  III's six row-operation nodes (`F-159`), its four affine nodes and
  `lem:case-III-claim612-r-nonzero` (`F-163`), its $d = 3$ placement and relabel nodes (`F-167`),
  and `lem:case-III`'s dead $d = 3$ pin `case_III_realization` (`F-171`); `meet.tex`'s two step
  lemmas through $\bigwedge^2 W$, with the dead pins of `def:meet` and `def:meet-pairing-dual`
  (`F-111`, L9's `F-114`); and `lem:forest-surgery-unsplit`, unfilled, whose forest form fails at
  $D = 1$ (S10; `F-091`).
  *Suggested:* *PI* (M3): per group, keep, collapse into a remark, or retire. Unpin
  `case_III_realization`, as tasks 3.6–3.7 unpinned such wrappers.
  *Estimate:* 3–6 blueprint commits by chapter, if retired; the Lean deletions with L9.
- **G5. Nodes that wait on the Lean** (`F-008`, `F-059`, `F-087`, `F-091`). `def:blockingWitness`
  and `def:dof-generic` are unfilled, as no declaration defines them (S33, S18).
  `def:plucker-coords`'s pins have no caller, and no declaration states the expansion that makes
  the Plücker vector an extensor's coordinates (`F-059`). `lem:packing-move`'s pin is dead because
  the descent repeats the move inline (`F-087`, L8). `lem:forest-surgery-unsplit` waits on a
  declaration of its forest form, or a restatement (S10).
  *Suggested:* Lean+: a declaration for each definition, or the node restated as prose; the
  expansion lemma; L8's descent.
  *Estimate:* 3–5 commits.
- **G6. Liveness, by `CLEANUP.md` §B's three outcomes** (`F-012`). At round 5's open, as at round
  1's audit, 202 pins at 153 nodes lay outside every main result's closure, every pin of 112 nodes.
  At this commit: **177 pins at 145 nodes, every pin of 109**; by group (pins / nodes / with every
  pin), round 1's chapters 33 / 32 / 28, round 2's 35 / 25 / 15, round 3's 68 / 54 / 43, round 4's
  22 / 17 / 14, `pencil` and `main-component` 19 / 17 / 9 (`scripts/blueprint-deps.py`, report 2).
  Round 5 unpinned the dead wrappers and helpers whose claims live pins now carry (tasks 3.6, 3.7,
  3.10, 3.13), and left the rest under *Scope*'s rule that deadness alone is no reason to unpin or
  retire.
  - *Keep as exposition*, dead by design: the executable surface (`executable.tex`'s nine nodes),
    side results and examples (`thm:typeII-isLaman`, the `top-fin` examples,
    `thm:degree-one-rank-tree`), the $d = 3$ instances (`thm:theorem-55-d3-instance`,
    `thm:theorem-55-6-d3`, `cor:theorem-55-d3-spanning`, `cor:theorem-55-6-multigraph-d3`,
    `lem:case-III-candidate-dispatch-d3`), an acceptance test (`cor:pencil-flat-x0`), and results
    of their own that no main result uses, such as `generic-lift.tex`'s panel form
    (`thm:panel-generic-rank`, `cor:panel-generic-rigid`), which `formalization.yaml` names in the
    body-hinge main result's row. Of these, `cor:theorem-55-d3-spanning`, whose pin a zero
    framework meets without its hypothesis (S2), is a candidate to retire.
  - *Retire or merge*: G3–G4's nodes, KT's route where the formal proof leaves it.
  - *Delete*: the unpinned dead declarations (L9), after §B's check.
  No dead pin is live-under-wired: task 4 added every missing edge, and a pin's liveness is its
  Lean call chain, which no `\uses` changes.
  *Suggested:* *PI*: G3–G4's choices, and whether a result of its own, such as the panel form,
  becomes a main result in `formalization.yaml`, which would make its pins live.
  *Estimate:* within G3–G4 and L9.

### 2.6 A stale example in `blueprint/CLAUDE.md`

The honesty gate's case (b) is a hypothesis that is the conclusion of a `\uses`'d node, and its
paragraph says: "`lem:case-I` is honestly green because its hypothesis *is*
`lem:genericity-device`, a `\uses`'d node that was red until discharged." That no longer holds.
`lem:case-I` does not `\uses` `lem:genericity-device`: task 4.4 removed the edge, which neither
the statement, the proof prose nor the pins used. Its pins' hypotheses are `hblock` (every motion
constant on $s$; `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`) and `hglue` (the bound
$\dim Z(G,p) \le D + \dim Z_s(G,p)$; the other two pins, both dead). Neither is the conclusion of
`lem:genericity-device`'s pins, which produce a realization (`exists_good_realization`), and for
a set $s$ of more than one body neither is the conclusion of a node that `lem:case-I` uses
(`lem:rank-delete-vertex` gives `hglue` at one body). `hglue` is the lower bound of KT eq. (6.3)
in motion form (`F-140`); S19 records that the node's statement is not what its pins state, and
S19's fix decides the node.
*Evidence:* read: the three pins' signatures (`Pinning.lean`, `PanelHinge.lean`), and
`lem:case-I`'s `\uses` in the dump at `f6ddebb5`.

**A replacement: `lem:case-III`.** Its first pin, `case_III_realization_all_k`, takes
`hSimple : G.Simple` beside `hG` (a minimal $0$-dof-graph), `hV3` ($|V(G)| \ge 3$) and `hnoRigid`
(no proper rigid subgraph). Simplicity is the conclusion of `lem:simple-minimal-noRigid` (pin
`simple_of_isMinimalKDof_of_noRigid`, from those three and $D \ge 2$), which `lem:case-III`'s
statement `\uses`, and `thm:theorem-55`'s pin discharges it by calling that lemma before Case III
(`theorem_55_minimalKDof_k_all_k`, `Theorem55.lean`, the branch for deficiency zero). The contrast
is case (a), `lem:case-II-realization`, whose pin derives simplicity in its body (`CaseII.lean`).
Two cautions for the sentence. The hypothesis is derivable from the pin's others, so a Lean round
that drops it (L7's kind) turns the example into case (a) and must move the manual's example with
it. And the script reads the edge as unbacked (the pin reaches the lemma only through
`lem:chain-data-extract`'s pin): a case (b) edge is backed by a hypothesis, which `--label` does
not read.
*Evidence:* read: the signatures of `case_III_realization_all_k` (`CaseIII/Realization.lean`)
and `simple_of_isMinimalKDof_of_noRigid` (`Induction/ReducibleVertex.lean`), the Case III branch
of `theorem_55_minimalKDof_k_all_k`, and `lem:case-III`'s `\uses`; `scripts/blueprint-deps.py
--label lem:case-III`.
*Suggested:* *PI*: sanction the edit, as no PROSE round edits an agent manual; then 1 commit
(Part 3, round 1).

### 2.7 Estimates

If the PI takes every suggestion, Part 2's items add up to:
- **docs**: `DESIGN.md`'s pebble-game section (L1–L2) and `formalization.yaml`'s credit (M2): 2
  commits; the honesty-gate example (§2.6): 1 commit;
- **blueprint**: M1's scope, G1's pin changes, G2–G3's merges, and G4's retirements if the PI
  retires: 6–15 commits, under the expected-diff gate; and M5's credit after the reading: 0–1;
- **Lean**: L1 after a recon (2–4), L2 (1), `F-061`'s rename (1), L6–L7 (4–6), L8 (3–4), L9 (2–3),
  G5 (3–5) and the docstring sweep, L3–L5 and L10–L12 with M2's and M4's docstrings (8–12): 24–36
  commits; 25–38 with `F-061`'s forest lemma;
- **no commit**: L3's docstrings ride with their `S` items when those come first; G6's keeps.

The smallest set that leaves no false text a reader trusts outside the Lean is the two docs
commits and M1's blueprint commit; §2.6's commit corrects the manual.

### 2.8 Entry → item

`L`: `F-013` L7 · `F-017` L7 · `F-018` L4 · `F-021` L7 · `F-022` L4 · `F-023` L5 · `F-024` L6 ·
`F-030` L12 · `F-032` L4 · `F-033` L1 · `F-035` L12 · `F-039` L7 · `F-040` L10 · `F-045` L12 ·
`F-047` L2 · `F-055` L8 · `F-057` L4 · `F-061` L4 · `F-063` L7 · `F-064` L10 · `F-069` L10 ·
`F-070` L7 · `F-074` L4 · `F-075` L6 · `F-077` L6 · `F-080` L12 · `F-085` L10 · `F-088` L8 ·
`F-092` L6 · `F-094` L5 · `F-097` L8 · `F-104` L6 · `F-108` L7 · `F-114` L9 · `F-123` L3 ·
`F-126` L12 · `F-130` L4 · `F-132` L10 · `F-133` L3 · `F-135` L3 · `F-140` L6 · `F-144` L9 ·
`F-148` L3 · `F-153` L3 · `F-156` L5 · `F-161` L3 · `F-164` L3 · `F-168` L4 · `F-172` L5 ·
`F-176` L12 · `F-182` L4 · `F-186` L5 · `F-190` L4 · `F-194` L5 · `F-198` L10 · `F-200` L12 ·
`F-205` L5 · `F-210` L4 · `F-215` L3 · `F-220` L5 · `F-225` L5 · `F-230` L11 · `F-232` L9 ·
`F-233` L11 · `F-235` L11 · `F-236` L11 · `F-237` L9 · `F-238` L9 · `F-240` L11 · `F-241` L11 ·
`F-242` L11 · `F-243` L11 · `F-244` L11 · `F-245` L11 · `F-246` L11 · `F-250` L11.

`M`: `F-025` M2 · `F-053` M4 · `F-081` M4 · `F-118` M3 · `F-222` M1 · `F-228` M5.

`E` and `N`, left wholly or in part: `F-008` G5 · `F-012` G6 · `F-059` G5 · `F-087` G5 ·
`F-090` G3 · `F-091` G4, G5 · `F-096` G2 · `F-111` G4 · `F-120` G2 · `F-134` G3, G4 ·
`F-139` G3, G4 · `F-147` G4 · `F-152` G3, G4 · `F-159` G3, G4 · `F-163` G4 · `F-167` G3, G4 ·
`F-171` G4 · `F-247` G1 · `F-248` G1 · `F-249` G1; no follow-up: `F-009`, `F-010`, `F-029`,
`F-065`, `F-068`, `F-129`, `F-131`, `F-197`, `F-219`.

## Part 3 — the follow-up program, proposed

The proposal is the ROADMAP bullet **RECONCILE** (*Queued post-program phases*). The PI queued it
next on 2026-10-15, ahead of ORIGAMI, and changed its shape: the plan as queued, with the PI's
decisions, is `notes/Reconcile.md`, which supersedes this Part where they differ. It takes Parts 1 and 2 as its input
and the ledger as each finding's home, as PROSE's rounds did.

- **First, the PI's decisions**, recorded in the program's planning note: Part 1's suggestions,
  S1's and S2's direction (a refactor, or the scope stated), M2's reference, M3 and G4 (keep,
  collapse or retire KT's route), M5's reading, whether the panel form becomes a main result
  (G6), and the edits to `DESIGN.md` and `blueprint/CLAUDE.md` (L1–L2, §2.6). Part 1's §1.1
  frames the discussion of what the `S` group shows.
- **Round 1, the texts** (docs and blueprint prose; no node, edge or pin change, so PROSE rounds
  1–4's invariance check): the scope of S1 and S2 on `formalization.yaml` and README (§1.4), M1's
  "for simple graphs", M2's four lines, `DESIGN.md`'s pebble-game section (L1–L2), and the
  honesty-gate example (§2.6). About 6 commits.
- **Round 2, the blueprint's statements and pins** (round 5's expected-diff gate and honesty
  gate; the hygiene rule lifted for exactly the items the PI sanctions): S6–S9 first, the four
  `\leanok` statements that are false as written (§1.4's smallest set); then §1.4's other
  restatements and repins, G1's pin changes, and the merges and retirements the PI chose (G2–G4).
  About 15–25 commits.
- **Round 3, the Lean** (`CLEANUP.md` §A–§C): §2.1's label check first, then L9's deletions after
  §B's check, L6–L8's signatures and repeated derivations (with the blueprint statements they
  touch, S17's among them), L1–L2's code after L1's recon, and the docstring sweep by directory
  (L3–L5, L10–L12, M2 and M4); the ledger's two Lean baselines feed §B and §C. About 22–32
  commits. In the files that S1 and S2 change (`GenericLift/`, `AlgebraicInduction/Theorem55.lean`,
  `PanelHinge.lean`) the sweep waits for the phase, so their docstrings are written once.
- **A phase** (new formalization; a number minted on open): S1 and S2 after a recon each (the
  families indexed by $E(G)$; the endpoint selector tied to the links), the Lean+ items (S22–S25,
  S31; optionally S3, S16 and S19), G5's declarations, `F-061`'s forest lemma, and optionally M1's
  multigraph form. About 16–26 commits with the recons, more with the optional items or if S2
  takes a structure field.

Rounds 1–2 need no Lean and can run first under autopilot once the decisions are recorded;
round 3 can too. The phase is new mathematics, so it is attended. Every round adds to the ledger
what it finds, under the ledger's rules, and sets the dispositions of what it acts on.
