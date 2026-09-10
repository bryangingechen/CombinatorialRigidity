## §(K-bare-ext) — continuation (direction BATTAIN): the seed-free direct-attainment shape, an **exact characterization** of `HasPencilRealization` off the Lean bodies, bare realizability proved **unconditional**, an exact **cone rank law** `6(|V|−1) − def₂(G)` that turns the standing "no T2 is producible by this harness" into a **decidable criterion**, and **774/774** attainment certificates with **no** shortfall anywhere

Direction **BATTAIN** (`notes/Pencil-fanout.md` §"BATTAIN", ordinal 39) — the
arc's **first** direction aimed at `hbareSplit`. Read against §(K-bare-ext)
*Steps BE1–BE8* (probe KBARE-FALSIFY, whose figures are cited, not re-run) and
`notes/Phase39-design.md` §"(K-bare) extension-route recon". Driver
`notes/scripts/w4/battain.py`
(`model|cone|attain|indep|census|hunt|probe|decide|necklace|localcone|t2`);
all exact ℚ, every rng seeded.

**Status, stated before the mathematics.**

- **The kernel's motive is now characterized exactly, and the W-clause is
  free.** `HasPencilPanelRealization G F n p` is satisfiable for *some* `F`
  **iff** `n_v, p_v ≠ 0` and `n_w ⬝ᵥ p_v = 0` for every `w ∈ closedNbhd(v)` —
  a purely bilinear point/plane incidence condition on the **closed
  neighbourhood relation**, with the supporting extensor `W_e` always
  constructible. **(BE-10)**, derived from the Lean bodies (`Statement.lean`
  88/103, `Theorem55.lean:3059`, `Basic.lean` 291/435/654), not from prose.
- **Bare pencil realizability is UNCONDITIONAL.** Put every normal in a common
  3-space `N ⊂ (K⁴)*` and every point at `q = N^⊥`: legal at **every** graph.
  So `HasPencilRealization K 3 G` carries **no existence content at all** — all
  of it is the **rank**. **(BE-11)**.
- **The pencil condition is carried entirely by the hubs**, as one determinant
  each: `PENCIL ⟺ span{n_w : w ∈ closedNbhd(v)} ≤ 3` for every `v`, which is
  **vacuous at `deg(v) ≤ 2`** (three vectors in `K⁴`) and at a degree-3 hub is
  exactly `det₄(n_v, n_{u₁}, n_{u₂}, n_{u₃}) = 0`. Corollary, and it upgrades
  a recorded *sample* to a **theorem**: `|closedHubNbhd(v)| ≥ 4` forces those
  normals dependent, while `IsNondegPencilRealization`'s third conjunct forces
  them independent — so **`¬ PencilNondegFeasible K G`**, the arc's "only known
  certificate", is a one-line consequence of the model. **(BE-12)**.
- **The cone stratum has an EXACT combinatorial rank law**: `rank(cone) =
  6(|V| − 1) − def₂(G)` with `def₂ = max_P 3(|P|−1) − 2 d(P)` the **planar**
  (`D = 3`) deficiency — the 3D pencil cone *is* a planar panel-and-pin
  framework. Verified at **68/68** shapes (4 named + 61 in the sweep + 3 necklaces),
  exactly, including DZ's `103 = 114 − 11`. It makes a T2 criterion: **if a graph's
  pencil conditions FORCE the cone, then T2 ⟺ `def₂(G) > def₃(G)`**.
  **(BE-13)**.
- **This is the first rank cap over a whole pencil stratum ever produced in the
  arc by an ARGUMENT** — which is exactly what (BE-9) said was needed and said
  was unavailable. (BE-9)'s *other* objection (the harness's witness class is a
  proper subclass) is **confirmed real** — the cone is a legal member the
  affine-point sampler rejects outright — and then shown **inert**: the affine
  class is Zariski-**dense** in the main component of the pencil variety.
- **No T2 candidate survives anywhere, and now with certificates rather than a
  cap report.** `rank ≤ target` holds for *every* framework, so one exact
  witness at the target **proves** attainment. **774 shapes** carry one: the
  **entire 216-member index-1 habitat census** (`breakhunt.py arith`'s family,
  every member, not a sample), DZ, the Q3 index-2 gadget, three
  count-independent `theta+centre` habitat members, a 545-shape sweep of
  subdivided cubic skeletons spanning indices **−6 … 12**, and the constructed
  T2 candidate below. **Zero shortfalls.** **(BE-14)**.
- **The forced-cone criterion was tested with a CONSTRUCTED candidate, not a
  search — and it died.** The *necklace* of `k` `K₄`-minus-an-edge blobs has
  `def₂ = k − 3`, `def₃ = max(0, k − 6)`, so it meets the arithmetic half from
  `k = 4`; the global cone there falls short by exactly `def₂ − def₃`. Its own
  derived stratum (one concurrency point **per blob**) **attains at every
  `k = 3…7`**. So the criterion's two halves have never been met by one graph.
- **Why the habitat cannot meet them, as an argument.** Forcing the cone needs
  the `span ≤ 3` closure to propagate along an edge, which needs three
  *independent* shared closed-star normals; `closedNbhd(v) ∩ closedNbhd(w) =
  {v, w} ∪ (N(v) ∩ N(w))`, so a third shared body is a **common neighbour**,
  i.e. a **triangle** — and the habitat is **triangle-free**, by `hnoRigid`
  through `Graph.triangle_isProperRigidSubgraph`, which is literally the `htf`
  step of `pencilPair_of_splitOff_of_habitat` (`Escape.lean:411–418`).
- **Verdict: direct attainment is OPEN, with the hard step isolated to one
  sentence, and it is a standalone theorem rather than a lemma.** See *Step
  BE13*. `hbareSplit` **unchanged**, carried as pinned; **no gap-map status
  moves except the (K-bare)/(K-bare-ext) row's development column**.

### Standing notation

`G` a habitat member of `hbareSplit` (`Escape.lean:351`), as in *Step BE1*.
`n := normal`, `p := point`, `W_e :=` the 2-dimensional span of the (unique,
for a nonzero 2-extensor) decomposition of `F.supportExtensor e`;
`closedNbhd(v) = {v} ∪ N(v)` (`Motive.lean:95`); a **hub** is a body of degree
`≥ 3` (`Graph.PencilHub`, `Motive.lean:71`). `target(G) := 6(|V|−1) − def₃(G)`,
`def₃ = max_P 6(|P|−1) − 5 d(P)` (`Deficiency.lean:273`, `D = bodyBarDim 3 =
6`); **`def₂ := max_P 3(|P|−1) − 2 d(P)`** is its planar (`D = 3`) sibling,
minted here. `Y(G)` is the **pencil variety**: the set of normal assignments
satisfying every hub determinant. Every rank is exact ℚ; GF(p) only as a
certified lower bound, which is all the certification needs.

### Step BE9 — the motive, characterized off the Lean bodies

`HasPencilPanelRealization G F n p` (`Statement.lean:88`) unfolds through
`HasCoplanarPanelRealization` (`Theorem55.lean:3059`), `ExtensorInPanel` and
`ExtensorThroughPoint` (`Basic.lean:291`, `Statement.lean:75`). For a **nonzero
decomposable** 2-extensor the decomposition's span is unique, so
`ExtensorInPanel C_e n_u ⟺ W_e ⊆ n_u^⊥` and `ExtensorThroughPoint C_e p_u ⟺
p_u ∈ W_e`. The conjunct list is therefore, verbatim:

> `n_v ≠ 0`, `p_v ≠ 0`, `p_v ⬝ᵥ n_v = 0` on `V(G)`; and for each link `e = uv`,
> `p_u, p_v ∈ W_e ⊆ n_u^⊥ ∩ n_v^⊥` with `W_e` 2-dimensional.

> **(BE-10)** *(proven; exact, no genericity)* The `W_e` clause is **free**.
> Given the rest, `p_u` and `p_v` both lie in `n_u^⊥ ∩ n_v^⊥`, which has
> dimension `≥ 2` in `K⁴`; take `W_e = span(p_u, p_v)` when they are
> independent and any 2-plane of the meet containing `p_u` when they are not.
> Hence
>
> **`∃ F, HasPencilPanelRealization G F n p ⟺ n_v ≠ 0 ∧ p_v ≠ 0 ∧
> n_w ⬝ᵥ p_v = 0 for every w ∈ closedNbhd(v)`** — a bilinear incidence
> condition on the closed-neighbourhood relation, symmetric in `(p, n)`,
> matching the landed self-duality `hasPencilPanelRealization_mapExtensor_
> screwComplementIso` on the nose.
>
> Two consequences fix what the arc's evidence means. **(i)** This is the
> **full** class `HasPencilRealization` quantifies over. **(ii)** The harness's
> standing witness class (`kbare_common.build_rigidity`: affine points
> `hat(p)`, `C_e := hat(p_u) ∧ hat(p_v)`) is a **proper subclass** — it asserts
> `pt[u] != pt[w]` and admits no point at infinity — exactly as (BE-9) warned.

> **(BE-11)** *(proven; a construction, every graph, no hypothesis)* Bare
> pencil realizability is **unconditional**. Take any 3-dimensional `N ⊂ (K⁴)*`,
> pairwise non-proportional normals `n_v ∈ N`, and `p_v := q` for the single
> `q` with `N = q^⊥`. Every closed-neighbourhood incidence holds because *every*
> normal is `⊥ q`. So `HasPencilRealization K 3 G`'s existential half is free
> and **its entire content is the rank equality** — which is why route A's
> antecedent supplies an object that is easy to have and hard to use.

**Machine validation** (`battain.py model`, 1 s). At DZ, drawn through the
landed affine sampler `danger.sample_dz_pencil`: the (BE-10) orthogonality
holds at **66/66** closed-neighbourhood pairs; the `(p, n, W)` carrier built
here and `kbare_common.build_rigidity` return the **same exact rank 114** at
the same configuration (the dictionary check), with the `W_e` freedom used at
`0/23` edges as the affine class predicts; and `¬PencilNondegFeasible` is
re-derived at `h0` from `|closedHubNbhd| = 4` rather than sampled.

### Step BE10 — the normals form, and what the pencil variety `Y` is

Eliminating `p` from (BE-10): a legal `p_v` exists iff the closed-star normals
fail to span `K⁴`.

> **(BE-12)** *(proven; exact)* **`∃ p` compatible with `n` ⟺ for every
> `v ∈ V(G)`, `dim span{n_w : w ∈ closedNbhd(v)} ≤ 3`.** At `deg(v) ≤ 2` the
> set has at most three members, so the condition is **vacuous**: the pencil
> condition is carried **entirely by the hubs**, one condition per hub, and at
> a degree-3 hub it is the single determinant
> `det₄(n_v, n_{u₁}, n_{u₂}, n_{u₃}) = 0`. Equivalently `n_v ∈
> span(n_{u₁}, n_{u₂}, n_{u₃})`.
>
> Three corollaries. **(i)** *(the certificate, as a theorem)* If
> `closedHubNbhd(v)` has `4` members, its normals are pencil-forced **dependent**
> and `IsNondegPencilRealization`'s third conjunct forces them **independent**;
> hence `¬ PencilNondegFeasible K G`. This reproves `K4`'s verdict-1 refutation
> and DZ's apex certificate in one line, from the model rather than from a
> sample. **(ii)** *(dimension)* `dim Y(G) = 3|V| − Σ_{hubs}(deg v − 2)`; at DZ
> `60 − 6 = 54`, which is also `5|V| − 2|E|` from the `(p, n)` count — the two
> counts agree. **(iii)** *(structure)* Each hub determinant is **linear in each
> normal separately**, so whenever the hubs admit a *private-variable tower*
> (an order `h₁…h_k` with representatives `x_i ∈ closedNbhd(h_i)`,
> `x_i ∉ closedNbhd(h_j)` for `j < i`), `Y` has a component `Y°` that is a
> **tower of linear fibrations over an irreducible rational base** — hence
> irreducible and rational, with a well-defined generic rank.

**Consequence for (BE-9), and it is a correction.** (BE-9)'s subclass objection
is **real** — (BE-11)'s cone is a legal member the affine sampler rejects — but
**inert**: the affine class is the complement inside `Y°` of the proper closed
subset `{p_v at infinity} ∪ {p_u ∼ p_v}`, hence **Zariski-dense** in `Y°`. So
the arc's recorded attainment figures were never subclass-limited, and a
universal non-attainment *within the class* over `Y°` would after all be a
statement about `Y°`.

### Step BE11 — the cone rank law, and a decidable T2 criterion

On the cone every supporting extensor passes through `q`, so every `C_e` lies
in the 3-dimensional `S := q ∧ K⁴`. Splitting the motion space `M = {m : V →
Λ²K⁴ : m_u − m_v ∈ ⟨C_e⟩}` by `S`: `m mod S` is constant (3 parameters), and
the `S`-part is `{s : V → S : s_u − s_v ∈ ⟨C_e⟩}` — which, under `S ≅ K⁴/⟨q⟩ ≅
K³`, is precisely the **planar panel-and-pin** system of `G` (body `v` ↦ the
line `n_v` in `P²`, link `uv` ↦ the pin `n_u × n_v`). Hence
`dim M = 3 + 3|V| − rank₂`, and with `rank₂ = 3(|V|−1) − def₂(G)`:

> **(BE-13)** *(proven-informally; exact, and measured 65/65)*
> **`rank(cone) = 6(|V| − 1) − def₂(G)`**, so **the cone attains iff
> `def₂(G) = def₃(G)`**. Consequently, **if a graph's pencil conditions FORCE
> the cone, then `HasPencilRealization K 3 G` fails — a T2 witness — exactly
> when `def₂(G) > def₃(G)`**, a purely combinatorial test.

**Machine validation** (`battain.py cone`, 1 s; and 61 further shapes inside
`hunt`). `K4`: `def₂ = def₃ = 0`, cone rank `18 = target`. `K5 − e`: `24 = 24`.
`K_{2,3}`: `24 = 24`. **DZ**: `def₂ = 11`, `def₃ = 0`, cone rank
**`103 = 114 − 11`**, predicted before it was measured. Inside the sweep the
law holds at **61/61** further shapes, and at `54/61` of them the cone alone
already attains.

**This is the arc's first universal rank cap over a pencil stratum obtained by
an argument** rather than by exhausting a sampler. It is what (BE-9) named as
the missing shape ("*a rank upper bound valid for all pencil configurations —
an argument, not a search*"); the cone stratum is not all of `Y`, but the
mechanism is now exhibited and its criterion is decidable.

**The criterion is not vacuous, and was tested by construction.** Let the
**necklace** `Nk_k` be `k` copies of `K₄` minus an edge (bodies `a,b,c,d`, all
edges but `cd`) joined in a cycle by `c_i — d_{i+1}`: cubic, simple, 2EC,
`|V| = 4k`, `|E| = 6k`, each blob a proper part with `f₂ = 1` and `f₃ = 7`, so
`def₂ = k − 3` and `def₃ = max(0, k − 6)` — the criterion's arithmetic half
holds from `k = 4`. Measured (`battain.py necklace`, 36 s): cone rank
`66 = target` at `k = 3`, `89 = target − 1` at `k = 4`, `112 = target − 2` at
`k = 5`, each exactly the law. The private-variable tower reaches **no** `Y`
point there (every vertex is a hub), so that mode sees only the cone — a T2
**candidate**, not a verdict. `battain.py localcone` (0.4 s) settles it from
the necklace's own conditions: give blob `i` its **own** concurrency point
`q_i` and put `n_{a_i}, n_{b_i} ∈ q_i^⊥`, `n_{c_i} ∈ ⟨q_i, q_{i+1}⟩^⊥`,
`n_{d_i} ∈ ⟨q_{i-1}, q_i⟩^⊥`; every closed star of blob `i` is then `⊥ q_i`, so
every pencil condition holds, and the `q_i` are distinct. That stratum
**ATTAINS at `k = 3, 4, 5, 6, 7`** (`66, 90, 114, 138, 161`), global normal
span `4/4` at each. **The candidate is dead.**

**Why the habitat cannot meet the forcing half.** `S_v = S_w` at adjacent
`v, w` needs three independent shared closed-star normals; the shared bodies
are `{v, w} ∪ (N(v) ∩ N(w))`, so a third one is a **common neighbour of two
adjacent bodies** — a triangle. The habitat is **triangle-free**: `hnoRigid`
kills every triangle through `Graph.triangle_isProperRigidSubgraph`, and that
is not an inference of this pass but the `htf` step inside
`pencilPair_of_splitOff_of_habitat` itself (`Escape.lean:411–418`). Witness at
the two named gadgets: a sampled `Y` point has global normal span **4/4** at
DZ and at the Q3 index-2 gadget, so the cone is a proper sub-stratum there.

### Step BE12 — direct attainment, measured: 774 certificates, no shortfall

**The certification is deterministic, not a cap report.** For every framework
and every partition `P`, `rank ≤ 6(|V|−1) − partitionDef(P)`, hence
`rank ≤ target(G)` always (`kbare_common`, re-derived this pass). GF(p) rank is
a lower bound for the rational rank. So **`rank_modp = target` proves
`HasPencilRealization K 3 G`** — an existential, settled by one witness. This
is the asymmetry that governs everything below.

| battery | shapes | attaining | mode | cost |
|---|---|---|---|---|
| the **whole** index-1 habitat census (`breakhunt.py arith`'s 216-member family, `≤ 6`-hub cubic skeletons) | **216** | **216** | `census` | 9 s |
| DZ (index 1) and the Q3 index-2 gadget, exact ℚ | 2 | 2 | `attain` | 5 s |
| `theta(l,l,l)+centre`, `l = 4,5,6` — `l = 5,6` **certified habitat members** (2EC, `max f(W) = −1` over proper `|W| ≥ 2`, `closedHubNbhd = 4`), `l = 4` is not (`max f = 1`) | 3 | 3 | `indep` | 1 s |
| subdivided cubic skeletons, `Y`-generic, indices **−6 … 12** | **484** | **484** | `hunt` | 14 s |
| the same sweep's schedule-unreachable shapes: 54 attain on the **cone**, and the residual **7** on a **tie** plan (`n_x := n_h` kills a hub's determinant identically) | 61 | 61 | `hunt` + `decide` | — + 2 s |
| the necklace `Nk_k`, `k = 3…7`, on its own derived stratum | 5 | 5 | `localcone` | 0.4 s |
| `K4`, `K5 − e`, `K_{2,3}` on the cone | 3 | 3 | `cone` | 1 s |
| **total** | **774** | **774** | | |

**Every shape reached carries an attainment certificate; there is no shortfall
anywhere.**

> **(BE-14)** *(measured; the direct-attainment statement, OPEN as a theorem)*
> Every habitat member the arc can construct — the whole census, both named
> danger gadgets, both count strata — satisfies `HasPencilRealization K 3 G`,
> each by an exact-ℚ certificate rather than a cap report. The statement the
> evidence supports is a **pencil analogue of the Molecular Theorem**:
>
> > *For every graph `G`, the pencil stratum of the panel-hinge realization
> > space attains the body-hinge target `6(|V|−1) − def₃(G)`.*
>
> Katoh–Tanigawa give the **panel-hinge** (coplanar) half; the pencil stratum
> adds **concurrency**, one determinant per hub, cutting a subvariety of
> codimension `Σ_{hubs}(deg v − 2)` out of `(P³*)^{V}`. **The hard step is
> exactly one sentence:** *the hub concurrency conditions do not force the
> configuration into the rank-drop locus* — `Y° ⊄ Z(G)`, where `Z(G)` is the
> locus whose complement KT's theorem certifies nonempty. Nothing in the arc's
> apparatus bounds `Z(G)`: §(K-tight)'s boundary-load calculus is a
> **split-local** device and does not see the whole-graph locus, and the
> chart/reseed/engine apparatus is unavailable by hypothesis
> (`¬ PencilNondegFeasible`).

**A methodological correction worth carrying.** The first `hunt` pass, drawing
**one** seed per shape, reported **three** shortfalls. Rank is lower
semicontinuous, so one draw is only a **lower bound** on the generic rank: all
three attain on another seed (`battain.py probe`, with the affine-class sampler
agreeing at each — `84`, `120`, `117`). The mode is retained as the driver's own
regression against reading a single draw as generic. This is the same shape as
option-C C3's `0/179` (*Step BE5*) with the inequality pointing the other way.

### Step BE13 — the verdict, and the price

**Which HIT shape this is: 1 and 2 together, both graded.**

**Shape 2 (report first).** *Is there a habitat `G` where
`HasPencilRealization K 3 G` fails?* **None found, and the standing reading is
now tested rather than inherited.** Precisely:

- **What a T2 witness must exhibit:** a habitat `G` and a rank cap valid over
  the **whole** class of (BE-10) — i.e. over `Y(G)` — not over a sampler's
  orbit.
- **The positive direction is DECIDED, per graph, deterministically.** One
  exact-ℚ point of `Y` at the target proves non-T2, because `rank ≤ target`
  universally. Every graph this pass touched is settled that way. So "no T2
  candidate found under cap" (*Step BE7*) is upgraded to **"774 shapes proven
  not to be T2 witnesses"**.
- **The negative direction is decidable per graph up to randomization, and only
  that.** On `Y°` the generic rank is well defined (BE-12)(iii); a random exact
  sample is a one-sided Schwartz–Zippel test. Deciding it symbolically means
  the rank of a `5|E| × 6|V|` matrix over `ℚ(t)` in `3|V| − #hubs` parameters —
  at DZ, `115 × 120` in **54** parameters, against
  `notes/Pencil-strategy.md` §5.3's measured death of a **28**-coordinate
  degree-52 expansion at 600 s. **Out of reach, and now with the exact number
  saying why.**
- **But (BE-9)'s "not producible by this harness" is too strong as stated, and
  this is the finding.** A universal cap over a pencil stratum **is**
  producible by argument: (BE-13) is one, exact and combinatorial. What blocks
  T2 is not that caps are unreachable — it is that the only known cap mechanism
  needs the cone **forced**, and forcing needs a **triangle**, which `hnoRigid`
  forbids on the habitat. That is a structural obstruction with a Lean-level
  citation, not a cap report.

**Shape 1.** *Direct attainment, proven or reduced.* **Reduced, with the hard
step isolated** — see (BE-14). Delivered along the way, and each is
self-contained: the exact characterization (BE-10), unconditional existence
(BE-11), the hub-determinant form and the `¬Feasible` certificate as a theorem
(BE-12), and the cone law (BE-13).

**Shape 3.** *The price, against the `∃`-seed + deformation-repair
alternative.*

- **Direct attainment is DEARER in absolute terms and CHEAPER in structure.**
  Dearer: it is a whole-graph statement about a `54`-dimensional variety with
  no induction to lean on, and it needs new mathematics (a genericity argument
  for `Y° ⊄ Z`). Cheaper: it is **seed-free**, **induction-free**, and
  **`hcontract`/`hK`-free — it does not use `¬ PencilNondegFeasible` at all**,
  so it discharges `hbareSplit` *and* `PencilPair`'s unconditional second
  conjunct on the whole habitat in one move, and its statement does not mention
  a split.
- **It is a standalone theorem, not an auxiliary lemma** — which is exactly the
  phase's 2026-08-05 bar (*standalone-significant*, not merely
  progress-toward-(K)). "The pencil stratum of a molecular graph attains the
  molecular rank" is a pencil analogue of the Molecular Theorem and would be
  publishable independently of PENCIL.
- **The `∃`-seed + repair alternative is cheaper per step and dearer in kind**:
  it stays inside the induction, but *Step BE8*'s shape 1 needs a deformation
  statement inside `HasPencilRealization K 3 G′`'s attainment locus **with no
  chart** (the habitat is infeasible), which is §(K-tight) *Step 5*'s wall one
  level up. Nothing this pass found makes that wall lower.
- **What the direct route now has that the arc did not have before this pass:**
  an exact parametrization of the object to be deformed (BE-10)/(BE-12), a
  proof that the existence half is free (BE-11), a worked example of a
  universal cap over a stratum (BE-13), and 774 certificates saying the
  statement is not false at anything constructible.

**The smallest next slice, if the coordinator wants one.** Prove
**(BE-14) restricted to `def₂(G) = def₃(G)`** — there the **cone itself**
attains by (BE-13), so the theorem holds with a *closed-form* realization and
no genericity argument at all. That is a complete, self-contained proof of
direct attainment on a named combinatorial subclass, and the first
`HasPencilRealization` result in the arc proved rather than measured. The
habitat is *not* inside it (DZ has `def₂ = 11 > 0 = def₃`), so it does not
discharge `hbareSplit` — it is a proof-of-concept for the shape.

### Verification

`python3 notes/scripts/w4/battain.py model` (1 s, (BE-10)/(BE-12): 66/66
closed-neighbourhood pairs, the two carriers agreeing at exact rank 114, the
certificate at `h0`); `cone` (1 s, (BE-11)/(BE-13): the law at `K4`, `K5 − e`,
`K_{2,3}` and DZ's `103 = 114 − 11`, plus the subclass witness); `attain` (5 s,
DZ `114/114` and Q3 `138/138`, exact ℚ, normal span 4/4); `indep` (1 s, the
three `theta+centre` shapes at `105/105`, `90/90`, `72/72`, with the habitat
audit certifying `l = 5, 6` as members and rejecting `l = 4`);
`census` (9 s, **216/216**, exact-ℚ confirms at the first five); `hunt` (14 s,
484 `Y`-generic shapes over indices −6…12, 0 shortfalls at 8 seeds each, cone
law 61/61, cone attains 54/61, 7 undecided); `probe` (3 s, the three
single-seed shortfalls all attaining, affine sampler agreeing); `decide` (2 s,
7/7 by tie plans); `necklace` (36 s, the constructed criterion candidate);
`localcone` (0.4 s, `k = 3…7` all attaining); `t2` (1 s, the reading).
`validate` runs all eleven in ~72 s.

### Caps, disclosed rather than smoothed

1. **The `Y` sampler needs a private-variable tower.** It reaches a generic `Y`
   point only when `solve_schedule` succeeds; failures cluster where hubs are
   densely adjacent. It succeeded at **216/216** census members, DZ, Q3 and the
   three `theta+centre`s, and at 484 of 545 sweep shapes; the other 61 were read
   on the cone (54 attaining) and the residual 7 by tie plans.
2. **Hub degree.** `solve_schedule` handles degree-**3** hubs only. Every
   census member and every swept shape is a subdivided cubic skeleton, so this
   is exact there; a habitat member with a degree-`≥ 4` hub is **unprobed**.
   (BE-12) itself is degree-free.
3. **The census is the arc's census, and inherits its cap.** 216 members at
   index 1 on `≤ 6`-hub cubic skeletons; index 2 is covered by the Q3 gadget
   only, and the 8/10-hub index-2 families (360 / 34 320 arithmetic candidates,
   *Step BE4*) are **not** swept.
4. **Sweep entries are drawn, not de-duplicated.** The 484 `hunt` entries are
   random length vectors at each `(skeleton, total length)`; repeats are
   possible, so "484 shapes" is an upper bound on distinct graphs.
5. **Deficiency oracles.** `def₂` uses the `2^{|V|}` partition oracle only up
   to `|V| ≤ 16` in the necklace mode; above that the closed form `k − 3` is
   used, derived not measured. `def₃` in `hunt`/`necklace`/`localcone` comes
   from the polynomial pebble oracle (`nogood_subdiv.deficiency`),
   cross-checked against the exact partition oracle at DZ and at the three
   `probe` shapes. In `census`, `def₃ = 0` is **assumed** from the count
   dichotomy (index `≥ 1` + `hnoRigid` ⟹ a spanning circuit ⟹ `def = 0`,
   `danger.py`'s preamble) and **asserted** against the exact `2^{20}` oracle
   at the first three members only — the oracle at all 216 would dominate the
   mode's 9 s cost.
6. **(BE-13) is proven-informally, not formally.** The splitting argument uses
   `rank₂ = 3(|V|−1) − def₂` for the planar panel-and-pin system, i.e. the
   `d = 2` molecular theorem; it is *measured* at 68/68 shapes here, not
   re-derived.
7. **No shortfall means no shortfall was reached**, not that none exists: the
   negative direction of T2 remains one-sided (see *Step BE13*).

### Harness note — the `kbare/` sibling-import set gains a `w4/` consumer

`notes/scripts/README.md` *Harness debt* → *New item (2026-08-20, probe
KBARE-FALSIFY) — the `kbare/` sibling imports; **UNPAID***. This driver is the
**first `w4/` consumer** of that set, so the recorded consumer list extends:

| name | current home | consumers |
|---|---|---|
| `dz_gadget`, `sample_dz_pencil` | `danger` | `optc`, `breakhunt`, **`w4/battain`** (3) |
| `SKELETONS` | `optc` | `breakhunt`, **`w4/battain`** (2) |
| `index_of`, `hub_set`, `q3_gadget`, `enumerate_family`, `build_multi`, `sample_pencil_bfs`, `skel_ok_multi` | `breakhunt` | **`w4/battain`** (1 — first external consumer of any `breakhunt` device) |

It is also the first import edge from the **`w4/` driver stack into `kbare/`
drivers** (previous `w4/` consumers reached only the `kbare_common` **model**
layer). **No move made**, per the rule that a dispatch may not edit a landed
driver another direction may be importing in flight. If the eventual move-down
happens, `battain.py` joins the acceptance test.

### TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator re-runs it

- **(E1) NO.** No `g`-flank. This direction is on **(K-bare)**, not the
  §(K-grid) ledger; it computes ranks, but of the *pencil* rigidity matrix on
  `hbareSplit`'s habitat, and touches no colouring, matching, or `d_adm`
  object. Clauses (i)–(v) have nothing here to fire on.
- **(E2) NO.** No ledger entry is refuted or shown unprovable-as-posed. The one
  landed claim this pass **corrects** is (BE-9)'s "no rank cap is producible by
  this harness", and it is corrected **with a successor in hand** — (BE-13) is
  the cap, and (BE-14) names the residual. `hbareSplit` is unchanged.
- **(E3) ARMED by GBAL, DOES NOT FIRE, and this direction does not fire it.**
  E3 fires only on a HIT completing **entry 1 / (a′)**; this pass is on
  (K-bare) and does not touch (a′).

### Confidence verdict

- **(BE-10), (BE-11), (BE-12): proven** — exact, derived from the Lean bodies,
  no genericity, no cap, and each machine-cross-checked against the landed
  carrier.
- **(BE-13): proven-informally**, measured exact at **68/68** shapes; the one
  imported ingredient is the planar (`d = 2`) molecular rank formula.
- **(BE-14): OPEN**, measured **774/774**, with the hard step isolated to a
  single sentence and a named, self-contained first slice (`def₂ = def₃`).
- **`hbareSplit`: OPEN and unchanged, carried as pinned.**

**What would change this.** For (BE-10)/(BE-12), an error in the reading of
`ExtensorInPanel`/`ExtensorThroughPoint` at a **degenerate** `C_e` — the
characterization assumes `C_e ≠ 0`, which `HasCoplanarPanelRealization`'s
total-over-`β` conjunct supplies, and a change there moves everything. For
(BE-13), a failure of the planar molecular formula on the *specific* line
arrangements the cone produces (it is measured, not proved, here). For
(BE-14), either a proof of `Y° ⊄ Z` — the theorem — or a habitat member whose
`Y` is forced into a degeneration with `def₂ > def₃`, which by *Step BE11*
would need a triangle and hence a violation of `hnoRigid`. **Superseded
2026-08-26 by (BE-15) (direction BZAVOID), and in the strengthening direction:**
that second disjunct is **empty at every graph**, on or off the habitat — a
forced degeneration confines each class to a local cone, which forces
`def₂ = 0` there, and the resulting cap's deficiency is exactly
`partitionDef₃(π(G))`, a value `def₃`'s own maximand already takes. So the
`hnoRigid` appeal is a **special case, not the load-bearing step**, and no
forced-degeneration cap can ever refute (BE-14). Read *Step BE14*.
