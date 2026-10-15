# PROSE findings report (round 5, tasks 8.1–8.2)

The report on the `S`, `L` and `M` entries of the ledger `notes/Prose-findings.md`, for the PI
(`notes/Prose.md` §3 *R*). The ledger holds each finding, its evidence and its disposition; this
report groups the entries by the kind of divergence, merges the entries that record one
divergence, ranks the groups, and suggests a disposition and a commit estimate for each. Part 1,
the `S` group, is task 8.1's (2026-10-15). Part 2, the `L` and `M` groups, the graph findings the
round left, and the proposed follow-up program, is task 8.2's. The report is not a stop
(`notes/Prose-graph-cleanup.md` *Autopilot: for the PI*).

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
first. *Merge/retire*: not among principle D's fixes, so on task 8.2's list.

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

**Checks the kinds suggest**, for the follow-up that task 8.2 proposes:
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
  conclusions as additive successors. Retiring the dead $d = 3$ corollary is task 8.2's.
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
  `lem:case-II-realization`'s proof gives) and repin. Retiring the node is task 8.2's (`F-152`).
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
  *Suggested:* restate: drop the vacuous assertion. Retiring the dead nodes is task 8.2's.
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
  result's proof takes (`F-118`, `M`, task 8.2).
  *Suggested:* restate with nondegenerate hinges (KT §5.1's nonparallel realizations) and repin on
  `exists_rankPolynomial_of_le_finrank_linking`; or join the node to
  `lem:rank-polynomial-of-le-finrank` (a merge, task 8.2's).
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
  *Suggested:* restate in the pin's form and fill it, or retire the node (`F-091`, task 8.2's).
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
  `lem:case-III-rank-certification` (task 8.2's).
  *Estimate:* 1 commit.
- **S21. KT Claim 6.4 as a polynomial, pinned on a point** (`F-138`; `lem:claim-6-4`). The
  statement gives a nonzero polynomial off whose zeros the rows of $G \setminus E(H)$ have rank
  $D(|s_c| - 1)$. The pin `rigidContract_exterior_rank_transport_htransport` gives one point (KT's
  choice in the proof of the claim) and assumes $G/E(H)$ simple, of deficiency zero, which the
  statement's hypotheses do not give (the proof needs only that it has no loops). The open-set
  form for every $k$ is `lem:rank-polynomial-IH-relabel-proj`'s, which the formal Case I reaches.
  *Evidence:* ledger (read; KT p. 675; measured).
  *State:* kept, with a note; the pin is dead (`F-139`).
  *Suggested:* merge into `lem:rank-polynomial-IH-relabel-proj` (task 8.2's), or restate at the
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
  *Suggested:* keep. The double pin of `lem:reduction-step` is task 8.2's (`F-096`, `F-120`).
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
