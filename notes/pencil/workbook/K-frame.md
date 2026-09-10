## §(K-frame) — the shared chart-to-frame dominance residue: the lemma shape delivered in its honest minimal form, both bad divisors made **combinatorial** at grid points, the **(ANH-14) residue discharged at every enumerated bare-cycle site by a colouring recipe** (1904/1904 + 30 exact certificates), and the (OC-16) residue's non-containment half witnessed **by construction** at θ(3,4,5) — with the strict availability package measured **0/8** and its (AC-9) mechanism named

Answering `notes/Pencil-fanout-archive.md` §"Fourth fan-out" → Direction J, i.e.
§(K-grid) *Step G13*'s candidate lemma shape, aimed at the two terminal
residues of the third fan-out: §(K-out) (OC-16)'s (at degree-3 hubs,
availability ⟺ the hard-stratum target-rank locus `⊄ {pt(b) ∈ C₀}`) and
§(K-ann) (ANH-14)'s (the universal irreducible degree-12 polynomial `C`
nonzero somewhere on the frame's reachable locus). Read against §(K-grid)
*Step G6* ((GR-5)) and *Step G13*; §(K-ann) *Steps A10/A14–A17* ((ANH-9),
(ANH-13), (ANH-14)); §(K-out) *Steps O11–O12* ((OC-12)/(OC-13)/(OC-15)/
(OC-16)); §(K-clos) (AC-2)/(AC-4)/(AC-9). Drivers:
`notes/scripts/w4/framedom.py` (imports the canonical layer plus `anhr1` /
`shrink` / `outerwide` / `grid` / `closure` read-only) and
`notes/scripts/m2/framedom.m2` (the M2 layer's fourth driver).

**Status, stated before the mathematics.**

- **The lemma shape *Step G13* names is delivered, and it is smaller than
  its name.** "Dominance" is never needed: both residues are
  *non-containment-in-one-hypersurface* questions, and those are settled by
  **one point off the divisor plus irreducibility of the stratum** ((FR-1),
  two lines of algebraic geometry). The content is entirely in the two
  ingredients — constructing the point, and owning the irreducibility — and
  the two residues differ exactly there: (ANH-14)'s stratum is the **whole
  pencil chart**, whose irreducibility §(K-ann) (ANH-9)(ii) already owns;
  (OC-16)'s is the **hard-stratum target-rank locus**, whose irreducibility
  nobody owns — and is needed *only* to combine separately-witnessed open
  conditions ((FR-7)).
- **The transport step — the unattempted one — works, and it lands on `G′`,
  not `G`.** The grid witnesses live at pencil placements; the residues'
  charts are the split graph `G′ = G − v + ab`'s (that is where
  `pt(a) ∈ M` comes from). Building the σ-fixed grid **at `G′`** makes
  `pt(a) ∈ M` *automatic* (alternation at the degree-2 body `a` forces its
  two edges into opposite rulings, so `pt(a)` is conjugate to both `pt(b)`
  and `pt(c)`), and `verify_pencil_witness` accepts the built ℚ(i)
  placement at every instance run.
- **At a grid point BOTH bad divisors are combinatorial.** Every hinge line
  of a σ-fixed grid configuration is a *ruling line* of the fixed quadric;
  the two ruling families span complementary 3-spaces (which are exactly
  the `⋆`-eigenspaces of §(K-clos) (AC-4)); so **any** 6×6 hinge-line
  determinant — (ANH-14)'s `C` and (OC-16)'s `Δ` in particular — is nonzero
  **iff** its six edges are coloured 3–3 with the three lines per family
  pairwise distinct, and "same line" is *same colouring-component*
  ((FR-2)/(FR-3), an identity over the function field: `framedom.m2`
  (FR-M1), `det = 128·Vdm(s)·Vdm(u)`).
- **The (ANH-14) residue is discharged at every enumerated bare-cycle site,
  by a recipe.** A *pattern colouring* — admissible on `G′`, the site's six
  frame edges 3–3 in pairwise-distinct components, plus two placement-free
  legality tests — exists at **1904 of 1904** bare-cycle sites of the full
  §(K-ann) pool (the census reproduces (ANH-13)'s 1904 exactly), and at 30
  sites (all 6 census sites + 24 sweep sites) the built ℚ(i) grid point was
  checked end-to-end: pencil witness green, `C ≠ 0` exact, with a
  criterion-violating colouring of the same site giving `C = 0` (negative
  control). Via §(K-ann) (ANH-9)(iii), each such point **proves** the
  (ANH-R1) β-clause at its site. What remains for class uniformity is
  **(FR-R1)**: pattern-existence at every class shape — a colouring
  question with **no rank, no count, no balance and no tree-triple in it**,
  strictly cheaper than §(K-grid) (GR-15)'s.
- **On the (OC-16) side the non-containment is witnessed by construction at
  θ(3,4,5), and the strict form hits a wall with a name.** Of the 8
  admissible `G′`-colourings, **4 land on the hard stratum at target rank**
  (`(rank, dim R_a) = (54, 1)` — the first constructed, non-sampled
  inhabitants of that locus), and each has `Δ ≠ 0` at exactly one end — so
  (OC-8)'s literal statement (a hard-stratum target-rank chart point with
  `L_b ⊄ R₁` or `L_c ⊄ R₄`) is **inhabited by an explicit combinatorial
  construction**. But the *strict* package — additionally `λ ≠ 0` at the
  same point — is **0/8**, and the mechanism is §(K-clos) (AC-9): a σ-fixed
  degree-3 hub always carries a coincident hinge pair, and at every
  on-stratum colouring the coincidence lands on the pair `{e₁, C(b,u)}` at
  the `Δ ≠ 0` end, killing `λ` there. Whether that anti-correlation is
  structural or θ(3,4,5)-specific is **open**.
- **Class uniformity is untouched. No gap-map status moves in this draft.**
  The (K-ann) row's residue changes *shape* (dominance → (FR-R1)
  pattern-existence) at the coordinator's hand, not its status.

### Standing notation (on top of §(K-clos) and §(K-ann))

`G` a class shape, `v` an eligible split with ends `b, c`,
`G′ = G − v + ab` (`outer.split_data`'s `Gp`), `H = G − v − a`. Grid data
per §(K-clos) (AC-2): a 2-colouring `col : E(G′) → {A, B}` assigns each
body the point `pt_w = s_w ⊗ u_w` on the fixed quadric, the `A`-parameter
`s` constant on components of `E_A` and injective across them (likewise
`B`); "admissible" = proper on the alternation constraint graph
(`closure.alternation_classes`). `W_A, W_B ⊂ Λ²K⁴` are the spans of the two
ruling families. A **bare-cycle site** is a (shape, split, length-4
companion, β) with `H/P − β` a bare 6-cycle (§(K-ann) (ANH-13)(iv)); its
**frame edges** are the six `H`-edges of that cycle. Everything is exact:
ℚ(i) points (`closure.Gauss`), `exactcore.rank`/`wedge2` throughout.

### Step FR0 — (FR-1): the lemma, in its honest minimal form

> **(FR-1)** *(proven-informally; standard)* Let `X` be an irreducible
> variety over a field `k ⊆ K̄` (or the image of an irreducible rational
> parametrization defined over `k`), `f : X → 𝔸^N` a morphism, and
> `D = {P = 0}` a hypersurface. If **one** point `x ∈ X(K)` (any extension
> `K`) has `P(f(x)) ≠ 0`, then `P ∘ f ≢ 0`, hence `f(x′) ∉ D` for `x′` in a
> dense open of `X` — in particular at the generic point, and at ℚ-rational
> points when `X`'s parameter space is rational over ℚ. Conversely
> `f(X) ⊆ D` iff `P ∘ f ≡ 0`.

Two remarks that do the strategic work. *(i)* **Dominance of `f` is never
needed** — *Step G13*'s phrase "gives dominance" over-asks; non-containment
in the *one named divisor* is all either residue consumes, and that is
one witness point + irreducibility of the *source*. *(ii)* The lemma
splits the two residues by who owns the irreducibility: for §(K-ann)
(ANH-14) the source is the whole chart of the triple and §(K-ann)
(ANH-9)(ii) owns it, so **the entire remaining content is the witness
point**; for §(K-out) (OC-16) the natural source is the hard-stratum
target-rank *sublocus*, un-owned — see *Step FR5*.

### Step FR1 — (FR-2): the ruling decomposition of `Λ²K⁴`

> **(FR-2)** *(proven; (FR-M1)–(FR-M3) are identities over the function
> field, the eigen identification measured exactly)* Under
> `Λ²(K² ⊗ K²) ≅ (Sym²K² ⊗ Λ²K²) ⊕ (Λ²K² ⊗ Sym²K²)`:
>
> (i) the Plücker images of the two ruling families of the fixed quadric
> span **complementary 3-spaces** `W_A ⊕ W_B = Λ²K⁴`, each family a
> **Veronese conic** in its own 3-space (`A(s)` is quadratic in `s`);
>
> (ii) any **3 distinct** same-family lines are linearly independent (3
> distinct points of a Veronese conic span its plane), and any **4** are
> dependent;
>
> (iii) `W_A` and `W_B` are exactly the `+1` and `−1` eigenspaces of the
> Hodge star (measured: `rank(x − ⋆x) = 0` on `W_A`, `rank(x + ⋆x) = 0` on
> `W_B`, driver `--rulings`) — so at a grid point the `⋆`-eigen decoupling
> of §(K-clos) (AC-4) *is* the family-block decomposition of any hinge-line
> matrix.

### Step FR2 — (FR-3): the determinant law — both bad divisors are combinatorial at grid points

> **(FR-3)** *(proven: the algebra is (FR-M1)/(FR-M2)/(FR-M3) over the
> function field; the hinge-line-is-a-ruling-line step is two lines below;
> driver-asserted in both directions at every built instance)* At a
> σ-fixed grid configuration with all bodies distinct:
>
> (i) **every hinge line is a ruling line** — an edge's endpoints are
> conjugate (§(K-clos) (AC-2)), and the restriction of the quadric to the
> line through two conjugate quadric points vanishes identically, so the
> line lies on the quadric; its family is the edge's colour, its *identity*
> is the edge's colouring-component (the family parameter is constant on
> components, injective across them);
>
> (ii) for any six edges `e₀…e₅`,
>
> `det₆[C_{e₀}, …, C_{e₅}] ≠ 0 ⟺` the colours split **3–3** and the three
> lines in each family are **pairwise distinct**;
>
> and on the nose, with `A(s)`/`B(u)` the ruling Plücker vectors,
>
> `det₆[A(s₁), A(s₂), A(s₃), B(u₁), B(u₂), B(u₃)] = 128 · Vdm(s₁,s₂,s₃) · Vdm(u₁,u₂,u₃)`
>
> — an identity over `ℚ(i)(s, u)` (`framedom.m2` (FR-M1); the constant is
> pinned cross-language at the instance `det[A(2),A(3),A(5),B(2),B(3),B(5)]
> = 4608`, asserted independently by `framedom.py --validate` and
> `framedom.m2` (FR-M0)).
>
> (iii) span membership is equally combinatorial: a further ruling line
> `C` lies in the span of a set `S` of ruling lines **iff** `C`'s family
> contributes ≥ 3 distinct lines to `S`, or `C`'s line is one of `S`'s (a
> conic meets a plane section in ≤ 2 points; `span S = (span S ∩ W_A) ⊕
> (span S ∩ W_B)`).

Both bad divisors are instances: §(K-ann) (ANH-14)'s `C` is the 6×6
Plücker determinant of a bare-cycle site's frame edges ((ANH-13)(iv));
§(K-out) (OC-16)'s `Δ` is `det₆[five chain hinge lines, C(b,a)]` — and at a
`G′`-grid point `C(b,a)` is itself a hinge line (of the split edge `ab`).
*Step G13*'s "evaluability battery" answer is therefore stronger than
evaluable-in-closed-form: **at grid points, evaluation is O(1) reading of
the colouring**, no algebra at all — with the exact ℚ(i) determinant kept
as the per-instance certificate.

An incidental with independent value: §(K-clos) (AC-9) becomes obvious in
this language — a σ-fixed body of degree ≥ 3 has two same-colour edges,
which share the body, hence share the component, hence **are the same
ruling line**: the coincident hinge pair, with its exact combinatorial
location (which pair coincides = which pair shares a colour).

### Step FR3 — (FR-4): the transport theorem, (ANH-14) side

> **(FR-4)** *(true-modulo-named-gap; the gap is the (GR-5)-at-`G′`
> chart-membership re-read, stated below and machine-checked per instance)*
> Let a bare-cycle site of a class triple be given, and let `col` be an
> admissible colouring of `G′` such that
>
> - **(pattern)** the six frame edges are coloured 3–3 with
>   pairwise-distinct components per family;
> - **(legality, placement-free)** all bodies distinct (the
>   `(comp_A, comp_B)` pairs injective) and no `closedHubNbhd` forced
>   collinear (no 3-member closed hub neighbourhood mono-component in
>   either family).
>
> Then the grid configuration of `G′` at `col` (generic injective family
> parameters, exact ℚ(i)) is a pencil chart point of the triple with
> `C ≠ 0` at its frame image; by §(K-ann) (ANH-9)(iii) — rank lower
> semicontinuity on the irreducible chart, never a genericity guard — this
> **proves the (ANH-R1) β-clause at the site**: `H/P − β` is independent at
> the generic pencil placement.

*Why `G′` and not `G`.* The §(K-ann)/§(K-out) charts place the split graph
`G′` (that is `dominance.base_seed`'s object, and where `pt(a) ∈ M` lives:
`a` is adjacent to both `b` and `c` in `G′`). At a `G`-grid the conjugacy
`pt(a) ⊥ pt(b)` is *not* forced (`a ~ b` fails in `G`); at a `G′`-grid it
is free: `a` has degree 2, alternation puts `(a,b)` and `(a,c)` in opposite
families, and both conjugacies hold — `pt(a) ∈ Π(b) ∩ Π(c) = M`
automatically. This settles the fan-out's "transport to the contracted
objects" question: the construction transports by **regridding at `G′`**,
after which the contracted objects' data (frame points, chain lines,
`C(b,a)`) are read off the one placement.

*Chart membership — the named gap, and what is checked.* §(K-grid) (GR-5)
proves grid configurations are pencil-chart points *for a class shape `G`
with `hcard`*; the object here is `G′`, not a class shape (its count
exceeds tightness by one). The proof of (GR-5) consumes no tightness — its
inputs are `hcard`, all-bodies-distinct, the closed-hub-neighbourhood LI
condition, isotropy/conjugacy, and degree-2 bodies having 3-member closed
neighbourhoods on a 2-edge-connected shape — and every one of those
hypotheses is **asserted per instance** by the driver (`hcard_ok(G′)` and
`is_2ec(G′)` hold at all 1540 splits carrying sites, 0 failures; the LI
ranks and distinctness exactly at every built point). Independently of the
(GR-5) reading, each built placement is certified as a pencil-panel
realization of `G′` by `kbare_common.verify_pencil_witness` — green at
every instance run. What is *not* re-proven here is the (GR-5) statement
restated at `G′` as a theorem; that two-line adaptation is the named gap,
and it is the only one. (The witness being ℚ(i) rather than ℚ is harmless:
the chart's parametrization is defined over ℚ and irreducible, so
independence at any extension-field point forces generic independence,
and (ANH-9)(iii)'s own ℚ-density argument then supplies rational points.)

### Step FR4 — (FR-5): the battery, and the residue's new shape (FR-R1)

> **(FR-5)** *(measured, with exact per-point certificates)* Over the full
> §(K-ann) triple pool (named inventory + `outer.sweep_shapes`; the site
> census **reproduces (ANH-13)'s 1904 exactly**, asserted):
>
> - **pattern availability 1904/1904** — every bare-cycle site admits a
>   pattern colouring meeting (FR-4)'s hypotheses; 0 splits hit the
>   colouring cap, 0 `G′` hypothesis failures (`--pattern`, 13 s);
> - **30/30 exact certificates** — at all 6 census-pool bare-cycle sites
>   (the (ANH-10) pool) and the first 24 sweep sites, the built ℚ(i) point
>   passes every gate (bodies distinct, isotropy + conjugacy per edge,
>   closedHubNbhd ranks, `verify_pencil_witness`) and has `C ≠ 0` by two
>   routes (`rank = 6` and `det₆ ≠ 0`), each with a **negative control**:
>   a criterion-violating colouring of the same site builds to a point
>   with `C = 0` exactly (`--transport`, 25 s).

So on the bare-cycle stratum the chart-to-frame residue is **discharged at
every site the arc can enumerate, and discharged by a recipe rather than a
sample** — the first time either side's dominance residue has moved by an
argument-shaped step. What is left for class uniformity is exactly:

> **(FR-R1)** *(open — the (ANH-14) residue's reduced form)* Every
> bare-cycle site of every `k = 4` class triple admits a pattern colouring
> ((FR-4)'s hypotheses). This is a **colouring-existence question with no
> rank, no counting, no balance and no tree-triple content**: the six-edge
> pattern forces alternation around the cycle (consecutive frame edges
> sharing a real body must differ — same-family adjacency is
> automatically the *same line*), and the remaining content is that the
> three same-family edges can be kept in **three distinct components**,
> plus the two placement-free legality clauses. Per shape it is decidable
> by the same finite scan the driver runs; measured, no shape needs more
> than the 8192-colouring budget and none misses. Compare §(K-grid)
> (GR-15): both are colouring-existence residues, but (FR-R1) carries no
> spline/rank side at all — it is strictly closer to pure graph theory,
> and Step G12's one-free-bit-per-branch structure applies verbatim.

The boundedness caveat transports from (ANH-14)(b) unchanged: the pool is
`outer.sweep_shapes` (`|V°| ≤ 5` families plus the named habitats), so
"every class shape" is **not** established — what is established is the
criterion, its per-site decidability, and a 1904/0 record over the sweep.

### Step FR5 — (FR-6): the (OC-16) side at θ(3,4,5) — constructed non-containment, and the (AC-9) wall

θ(3,4,5) is the `ℓ_min = 5` stratum's unique named class inhabitant
(§(K-out) *Step O12*: 8 of 5226 POOL-CW pairs; the theta remark of
(OC-10)). Its `G′` has 8 admissible colourings; both companion ends are
degree-3 hubs; per end the length-5 chain of `K = (H/X) − e₁` exists and
`R` at any placement satisfies (OC-15)'s pointwise containment
`R ⊆ span{chain lines}`.

> **(FR-6)** *(exact per point; the criterion equivalences asserted per
> colouring per end; `--outer`, 5 s)* At every one of the 8 colourings ×
> 2 ends:
>
> - `dim span{chain lines} = 5` (the alternating chain always splits 3–2
>   with distinct lines), and both `Δ = det₆[chain, C(h,a)]` and the outer
>   line's span membership match their combinatorial predictions ((FR-3)(ii)
>   applied to `Δ`; (FR-3)(iii) for membership) — **16/16, asserted**;
> - **4 of 8 colourings land on `(rank, dim R_a) = (54, 1)`** — target
>   rank, hard stratum, by `outer.stratum_at` at the dehomogenized ℚ(i)
>   placement; the other 4 are off target rank;
> - every on-stratum colouring has `Δ ≠ 0` at **exactly one** end — so
>   **(OC-8)'s literal statement is inhabited by construction**: an
>   explicit, combinatorially-specified, exact chart point of the
>   hard-stratum target-rank locus with `L_b ⊄ R₁` (or the `c`-mirror).
>   4/8 colourings are such witnesses;
> - the **strict availability package** — additionally `λ ≠ 0` at the same
>   point — is **0/8**, and the failure is exact and named: at a σ-fixed
>   degree-3 hub the (AC-9) coincidence must land on one of the three edge
>   pairs, and at every on-stratum colouring it lands on `{e₁, C(b,u)}` at
>   the `Δ ≠ 0` end (`λ = 0` by the coincidence, §(K-out) (OC-12)'s first
>   branch), while the colourings whose coincidence pair is `{e₁, C(b,a)}`
>   — which give `Δ ≠ 0 ∧ λ ≠ 0` — are exactly the off-target ones.

Three readings, kept apart. *(i)* For (OC-8) as recorded the constructed
points are already witnesses — non-containment needs no `λ`. Per shape
this adds nothing at θ(3,4,5) (POOL-G's sampled frames witness more), but
the witness is now **recipe-shaped**: its conditions are a colouring
pattern plus one measured rank pair, the ingredients a class-uniform
statement could quantify. *(ii)* For the *availability* consumer the
σ-fixed witnesses hit a genuine wall: (AC-9) makes *some* coincidence at
the hub unavoidable, and the measured anti-correlation (on-stratum ⟺ the
coincidence sits on the availability-killing pair) means **no σ-fixed
point of θ(3,4,5) is a strict witness**. Whether the anti-correlation is
structural (an interaction of the (AC-4) block ranks with the hub's colour
pattern) or shape-specific is **open** — it is this section's sharpest
open question, and a mechanism either way would be informative: structural
⟹ σ-fixed witnesses can never serve the strict form and the witness half
needs a non-σ-fixed deformation (e.g. (OC-14)'s slide launched *from* a
grid point); shape-specific ⟹ a wider `deg_H = 2` battery (item 2 of
*What would change this*) finds strict witnesses elsewhere. *(iii)* The
`dim R_a = 1` finding is independently valuable: it is the first evidence
that the σ-fixed locus **meets the hard stratum at target rank** — the
(K-tight) frame's habitat — constructively, not by sampling.

### Step FR6 — (FR-7): the irreducibility ingredient, located

> **(FR-7)** *(assessment; the (ANH-14) half is an argument, the (OC-16)
> half names an open object)* The fan-out asked where irreducibility must
> hold. The answer splits:
>
> - **(ANH-14) side: nothing new is needed.** The stratum is the whole
>   chart of the triple; §(K-ann) (ANH-9)(ii) supplies its irreducibility;
>   (FR-1) + one witness point finishes. This is why *Step FR4* could run
>   to completion with no new geometry.
> - **(OC-16) side: the smallest object is the hard-stratum target-rank
>   locus of the (shape, split) chart** — and it is needed **only** to
>   combine separately-witnessed open conditions (availability off `C₀`,
>   the coincidence off, (Λ0) clauses, …) without exhibiting one point
>   satisfying all simultaneously. A single simultaneous witness evades it
>   entirely — which is what POOL-G's sampled frames de facto are, and
>   what *Step FR5*'s constructed points are for the non-containment
>   conjunction. What would prove it: exhibit the locus as the image of an
>   irreducible parametrization, the same trick (ANH-9)(ii) uses for the
>   chart. A concrete foothold now exists: each on-stratum colouring's
>   grid family (one Fraction parameter per colouring component) is an
>   irreducible rational family whose sampled member lies on the locus; if
>   `dim R_a = 1` holds generically along it (one exact point off the
>   rank-drop divisor decides, per colouring), the locus contains a named
>   irreducible subvariety through each constructed witness — not the
>   whole locus, but enough to run (FR-1) *relative to that subvariety*
>   for any condition evaluable on it.
>
> **Struck as unnecessary (2026-08-19, direction OCON).** §(K-out) (OC-17)
> shows the (OC-16) side needs no dedicated irreducibility argument at all:
> the hard-stratum target-rank locus is Zariski **open** in the whole pencil
> chart (an intersection of two maximal-rank conditions), so its
> irreducibility is inherited from the chart's own — already owned by
> §(K-ann) (ANH-9)(ii) — and the foothold above is unnecessary rather than
> open. *What would change this* item (iii) below is struck on the same
> ground.

### Verdict — what this buys each residue, exactly

- **§(K-ann) (ANH-14) / the (K-ann) gap-map cell**: the chart-to-frame
  dominance residue on the bare-cycle stratum is **replaced by (FR-R1)**
  (pattern-existence), discharged at 1904/1904 enumerated sites with 30
  exact certificates. One named gap rides along ((GR-5) restated at `G′`).
  Coordinator action at landing: the (K-ann) row's residue sentence gains
  the (FR-R1) form; **status does not move** (class uniformity is exactly
  (FR-R1) + the sweep boundary).
- **§(K-out) (OC-16)/(OC-8) / the (K-out) row**: the evaluability battery
  is answered (combinatorial at grid points); (OC-8)'s non-containment is
  witnessed by construction at θ(3,4,5) with the witness on the hard
  stratum at target rank; the strict availability package is refuted for
  σ-fixed witnesses at θ(3,4,5) (0/8) with the (AC-9) mechanism named and
  its structurality open. **Status does not move.**
- **§(K-grid) *Step G13***: the convergence rider's assessment is now a
  theorem-shaped record: the candidate supplier works, the lemma shape is
  (FR-1), and the two cautions it carried (semicontinuity not guards;
  transport to contracted objects) are both discharged — the second by
  regridding at `G′`.

### Verification

`notes/scripts/w4/framedom.py` (new, untracked; exact ℚ/ℚ(i), stdlib only;
seeded rngs, seed 20260807 printed per mode; no `set` printed). Imports
only catalogued primitives and the owning drivers read-only: `exactcore`
(`rank`, `wedge2`, `dot`), `closure` (`colourings`, `components`,
`grid_point`, `ruling_A_line`/`ruling_B_line`, `Gauss`), `grid`
(`build_fixed_config_params`, `proportional`), `repin` (`span_basis`),
`outer` (`split_data`, `companions4`, `stratum_at`, `named_inventory`,
`sweep_shapes`), `annih` (`habitats4`, `path_edges`), `shrink`
(`hp_edge_rows`, `census_pool`), `anhr1` (`core_decompose`), `outerwide`
(`companion_sets`, `chain_to_weld`), `kbare_common` (`verts_of`, `is_2ec`,
`verify_pencil_witness`), `nogood_subdiv` (`hcard_ok`). Two local devices,
each named as such in its docstring: `det6` (no 6×6 determinant primitive
exists; always cross-checked against `exactcore.rank`) and `chn_sets` (the
*set-valued* closed hub neighbourhoods; the catalogued
`kbare_common.closed_hub_nbhds` returns cardinalities only — a candidate
*Divergences* row for the landing commit). `notes/scripts/m2/framedom.m2`
(new, untracked; the layer's fourth driver; version line `1.26.06` second,
`randomness: none`; convention-3 pin (FR-M0) ties `grid_point` / `wedge2` /
`PL` to their canonical Python homes through the shared instance value
4608). Nothing existing is modified
(`git diff --name-only -- '*.py' '*.m2'` empty), so the figure-invariance
gate discharges on that check alone. From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --rulings    #  2 s  (FR-2) + (FR-3) measured
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --pattern    # 13 s  (FR-5) availability, 1904/1904
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --transport  # 25 s  (FR-5) exact certificates, 30/30
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --outer      #  5 s  (FR-6) at theta(3,4,5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --validate   #  2 s  machinery + the cross-language pin
M2 --script notes/scripts/m2/framedom.m2                           #  1 s  (FR-M0)-(FR-M3)
```

All five Python modes byte-identical under `PYTHONHASHSEED` 0 and 999; the
M2 driver byte-identical across two runs; every invocation far inside the
600 s budget. No figure anywhere in this section is a
`place_pencil_general` rate; nothing gates on `repin.star_generic`
(σ-fixed points never pass it, (AC-9)); every claim is an existence
witness, an exact identity, or an exhaustive scan of a pinned finite pool.

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (FR-1) | — | **proof-level** (two lines of algebraic geometry); no driver can test a lemma statement |
| (FR-2)(i)/(ii) | `--rulings`, `(FR-M2)`/`(FR-M3)` | rank 3 per family over 8 params + all 3-subsets independent + all 4-subsets dependent; the function-field rank statements |
| (FR-2)(iii) | `--rulings` | `rank(x − ⋆x) = 0` on `W_A`, `rank(x + ⋆x) = 0` on `W_B` |
| (FR-3)(i) | `--validate` | hinge line of a conjugate pair ∝ the shared ruling line, both families |
| (FR-3)(ii) | `(FR-M1)` + `--rulings` + `--transport` | the identity over the function field; the constant at 20 draws; **both directions** at built sites (criterion ⟹ `det ≠ 0`; violation ⟹ `det = 0`, the negative controls) |
| (FR-3)(iii) | `--outer` | span-membership prediction == exact membership, 16/16 colouring-ends |
| (FR-4) | `--transport` | every hypothesis of the statement asserted at each of 30 built points (distinctness, LI, isotropy/conjugacy, `verify_pencil_witness`, `C ≠ 0` two routes) |
| (FR-4)'s named gap | — | **not driver-testable**: (GR-5) restated at `G′` is prose; its hypotheses are what `--pattern`/`--transport` assert per instance |
| (FR-5) | `--pattern` | the 1904-site scan, the census pin `== 1904`, 0 caps, 0 hypothesis failures |
| (FR-6) | `--outer` | the 8-colouring table: `stratum_at`, `Δ`, membership, and both criterion equivalences asserted per row |
| (FR-7) | — | **assessment**; its foothold's testable half (generic `dim R_a` along a colouring family) is *What would change this* item 3, not run |
| (FR-R1) | — | **still open, and still the point**: `--pattern` tests the pool, not the class |

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(FR-1)** | the minimal dominance lemma; "dominance" over-asks | **proven-informally** (standard) |
| **(FR-2)** | ruling decomposition, Veronese structure, ⋆-eigen identification | **proven** ((FR-M1)–(FR-M3) identities; eigen half measured exactly) |
| **(FR-3)** | at grid points every 6×6 hinge-line determinant — both bad divisors included — is the 3–3-distinct colouring criterion | **proven-informally** (conjugate-pair step + (FR-2) + (FR-M1); asserted both directions at every built instance) |
| **(FR-4)** | pattern colouring ⟹ exact chart witness ⟹ (ANH-R1) β-clause at the site | **true-modulo-named-gap** — the (GR-5)-at-`G′` restatement (hypotheses machine-checked per instance; `verify_pencil_witness` green throughout) |
| **(FR-5)** | availability 1904/1904; 30/30 exact certificates with negative controls | **measured** (exhaustive over the pinned pool; each certificate is itself a proof at its site via (ANH-9)(iii)) |
| **(FR-6)** | θ(3,4,5): 4/8 colourings on the hard stratum at target rank, each a literal (OC-8) witness; strict package 0/8 with the (AC-9) mechanism | **exact per point**; the anti-correlation's structurality **open** |
| **(FR-7)** | irreducibility located: un-needed on the (ANH-14) side, needed only for condition-combination on the (OC-16) side, smallest object named | **assessment** (argument, no driver) |
| **(FR-R1)** | class-uniform pattern-existence | **open** — the reduced residual this section leaves |

**Class uniformity is untouched. No gap-map status moves.**

### What would change this

*(i)* **A proof of (FR-R1)** — alternation around the cycle is nearly free
(forced at real degree-2 bodies, chosen at hubs); the content is keeping
the three same-family edges in distinct components. Step G12's
one-free-bit-per-branch structure plus girth 6 look sufficient for a
direct argument, and a refutation would need a shape whose *every*
admissible colouring merges two non-adjacent frame edges in both
families' component structures — none among 1904. This is the direction's
chief hand-off, and it would close the (ANH-14) residue on the whole
bare-cycle stratum *as an argument*.

*(ii)* **A `deg_H(h) = 2` battery beyond θ(3,4,5)** for the (OC-16) side:
(FR-6)'s machinery needs only a degree-3 hub end and the chain form of
`R`, i.e. §(K-out) (OC-15)'s `ℓ_min = 5` stratum — 8 POOL-CW pairs, all
reachable by the same driver pattern. It would decide whether the strict
package's 0/8 is θ(3,4,5)-specific or structural.

*(iii)* **The (FR-7) foothold — struck as unnecessary (2026-08-19, direction
OCON), not closed or delivered.** The original ask: per on-stratum colouring,
one more exact point of the same colouring family off the `dim R_a` rank-drop
divisor would certify generic `dim R_a = 1` along that irreducible family —
the first named irreducible subvariety inside the hard-stratum locus. §(K-out)
(OC-17) removes the need for it: the locus is already an open subset of the
(irreducible) whole chart, so no dedicated subvariety needs naming. This item
is one of the un-commissioned (FR-6) follow-ons; striking it as unnecessary is
the **opposite** of entering it — no bar was crossed.

*(iv)* **A structural account of the on-stratum ⟺ coincidence-pair
anti-correlation** ((FR-6)) — an (AC-4)-block-rank computation over the
colouring's class structure at `G′`, finite per shape. Either verdict
re-routes the strict-witness question.

*(v)* **The (GR-5)-at-`G′` restatement, written** — two lines of prose in
§(K-grid) or here, discharging (FR-4)'s named gap; a compiler spike is
not needed at the informal tier, but the Lean-side chart objects exist
(`Engine.lean`) if a later pass wants the pin exact.

*(vi)* **An (ANH-16)(ii)-style cost note is unnecessary here** — every
mode is seconds — but a *wider* pattern scan (lifting `sweep_shapes`'
`|V°| ≤ 5` cap) would move the (FR-5) boundary; a miss found there would
be a genuine (FR-R1) counterexample and would re-aim item (i) at repair.

**Continuation (2026-08-07, fifth fan-out direction PEX) — (FR-R1) is PROVEN: the bare-cycle stratum is *finite*, its frame has a normal form that makes the 3–3 split and the distinct-component clause automatic, the legality clauses are read exactly (one of them is a proper edge-2-colouring of the hub-hub graph, the *only* place a refutation could have lived), and the whole stratum is enumerated exhaustively (22 isomorphism classes, 76 sites, 1976 labelled instances, all pattern-available) — so (ANH-14)(b)'s boundedness caveat dissolves rather than widens, with the sweep's coverage measured at 14 of 22 classes and §(K-ann) *Step A14*'s `c′ ≤ 1` cells re-derived.**

Answering `notes/Pencil-fanout-archive.md` §"Fifth fan-out" → Direction PEX, i.e.
§(K-frame) *Step FR4*'s residual **(FR-R1)** and *What would change this*
item (i) — the section's own chief hand-off. Read against §(K-frame) *Steps
FR0–FR3* ((FR-1)/(FR-3)/(FR-4)); §(K-ann) *Steps A14/A15* ((ANH-13)(i)/(iv),
(ANH-14)(a)/(b)); §(K-grid) *Step G12*; and the *Shared dictionary*'s (R3)
`def(C_k) = max(0, k−6)`, (R4) `hcard`, (SD-6) branch length ≤ 5, §(K-ind)
*Step I2* (girth ≥ 7). Driver: `notes/scripts/w4/patexist.py` (new,
untracked; imports `framedom` / `closure` / `outer` / `shrink` / `annih` /
`nogood_subdiv` read-only). **No Macaulay2 leaf was opened** — the question
is combinatorial and stayed combinatorial; the reserved `m2/patexist.m2` is
returned unused.

**Status, stated before the mathematics.**

- **(FR-R1) is PROVEN on the bare-cycle stratum, and the proof is not a
  wider battery.** Two independent halves. *(i)* A **uniform structural
  argument** ((FR-9)–(FR-11)) that derives the 3–3 split and the
  distinct-component clause outright, with no case left over, and reads
  legality clause (ii) as an exact equivalence. *(ii)* An **exhaustive
  enumeration of the whole stratum** — because the stratum is **finite**:
  a bare-cycle site forces `c(G) = 3` ((ANH-13)(iv)), hence
  `(|V|,|E|) = (16,18)`, `n_hub ≤ 4`, and finitely many branch-length
  tuples. Four hub multigraphs; **22 isomorphism classes of shape carrying
  a bare-cycle site, 76 sites among them**; enumerated as 470 labelled
  shapes and **1976 labelled sites, 1976 pattern-available**, none scarcer
  than 16 pattern colourings out of 32 admissible.
- **(ANH-14)(b)'s boundedness caveat is not widened — it is discharged.**
  (FR-5)'s 1904 sites came from `outer.sweep_shapes` (`|V°| ≤ 5` plus named
  habitats). On this stratum the cap **cannot bind** (`n_hub ≤ 4`), and the
  sweep's *shape* coverage was nevertheless incomplete, and (FR-14)
  measures the shortfall at the only granularity that means anything —
  **isomorphism classes of shapes**. Of the four possible hub multigraphs
  the sweep carries **two** (`θ³`-at-`c = 2` aside, `θ⁴` contributes nothing
  and `K4` contributes everything it has); the `n = 3` multigraph with
  multiplicities `(1,2,2)` and the `n = 4` "C₄ with two opposite edges
  doubled" are **outside the sweep entirely**. Result: the sweep pool covers
  **14** of the stratum's **22** iso classes — all 14 inside the `K4` family
  — carrying **58** of its **76** sites; the 8 unswept classes carry the
  other **18**. **No iso class the pool knows is missing from the
  enumeration (0/14).**
- **Neither `1904` nor `1976` counts distinct mathematical objects, and
  (FR-14) says so with the arithmetic.** Both are *labelled-instance* counts
  over shape lists that carry isomorphic duplicates by design (the sweep
  families overlap each other and `named_inventory` re-lists habitats): one
  `K4` iso class alone is carried **49 times** in the pool. Exactly,
  `1904 = 58 + 1846` and `1976 = 76 + 1900`, the second summand being the
  duplicate-induced over-count in each. So the `1904` vs `1896` gap that
  looked like eight missing sites is **a multiplicity artifact of two
  differently-built lists over the same 14 classes** — neither census is
  missing anything, and the canonical figures are **14 classes / 58 sites**
  (swept) against **22 classes / 76 sites** (complete).
- **The one place a refutation could have lived is named, constructed, and
  then shown unrealizable.** Legality clause (ii) is **exactly** "the
  hub-hub subgraph `Λ` of `G′` is properly edge-2-coloured" ((FR-10)(ii),
  asserted over 8728 (split, colouring) pairs). So a shape whose `Λ` has an
  **odd cycle** would have *no legal admissible colouring at all*, refuting
  (FR-R1) at every one of its bare-cycle sites. The driver **constructs**
  such a graph and confirms 0 legal colourings out of 1024, with an
  even-cycle negative control at 4 of 4096 — parity, not size, is the
  mechanism. It cannot happen here: a `Λ`-cycle is a cycle of `G` on hubs
  only, of length ≥ 7 (girth), while `n_hub ≤ 4`.
- **Legality clause (i) ("all bodies distinct") is *vacuous* on this
  stratum**, not merely satisfied: over **every** admissible colouring of
  **every** site of the complete stratum the collision count is **0**
  ((FR-12)), and the characterization behind it (a collision is always a
  pair of length-2-branch interiors) is asserted, not assumed. The uniform
  reason is a short girth-7 + branch-length count, given in *Step FR11*.
- **The recipe is a formula, not a search.** (FR-11) builds one colouring
  per site from the site's combinatorics — frame branch bits forced to
  alternate, `Λ` properly 2-coloured, every other bit the constant 0 — and
  its **first** variant is a pattern colouring at **1904/1904** pool sites
  and **1976/1976** stratum sites. The A/B swap and the second constant are
  never needed.
- **What does not move.** (FR-4)'s named gap — §(K-grid) (GR-5) restated at
  `G′` — stays exactly as named; this direction does not touch it. The
  (OC-16) side is untouched. **Class uniformity of `hK` is untouched**: what
  closes is the (ANH-14) chart-to-frame residue *on the bare-cycle stratum*
  — (ANH-13)'s `c′ = 1` column, 1904 of the swept 6426 length-5-branch
  sites (29.6 %), i.e. the (ANH-R1) β-clause is now proven at those sites
  and untouched at the other ~70 %.

### Standing notation (on top of §(K-frame) *Standing notation*)

`G` a `k = 4` class shape; `v` an eligible split with `b — v — a — c` the
split branch (`deg v = deg a = 2`, `b, c` hubs); `G′ = G − v + ab`;
`H = G − v − a = G′ − a`; `P = [b,x₁,x₂,x₃,c]` a length-4 companion; `X` the
weld. A **hub** is a vertex of degree ≥ 3; a **branch** is a maximal path
with degree-2 interior and hub ends; `G°` is the hub multigraph, `Λ` the
hub-hub subgraph of `G′` (equivalently: the length-1 branches). `Γ_A`, `Γ_B`
are the two colour classes of `Λ` under an admissible `col`. `n_hub = |V(G°)|`.
`--frame` etc. name modes of `patexist.py`.

### Step FR7 — (FR-8)/(FR-14): the bare-cycle stratum is FINITE, here is all of it, and here is what the sweep was missing

> **(FR-8)** *(proven; census driver-asserted, `--strat`)* Every bare-cycle
> site has `c(G) = 3`, and therefore:
>
> (i) `(|V(G)|, |E(G)|) = (16, 18)`; `Σ_{hubs} deg = 2c − 2 + 2n_hub` with
> every hub of degree ≥ 3 gives **`n_hub ≤ 2c − 2 = 4`**; `G` has exactly
> `c − 1 + n_hub = n_hub + 2` branches, of total length 18 and each of
> length ≤ 5 ((SD-6)); and `G°` has **no loop** (a loop branch is a cycle of
> `G` of length ≤ 5).
>
> (ii) Hence `G°` is one of exactly **four** connected loopless multigraphs
> with `n + 2` edges and min degree 3 on `n ∈ {2,3,4}` vertices:
> `n = 2` with a single 4-fold edge; `n = 3` with multiplicities `(1,2,2)`;
> `n = 4` cubic — either `K4` or `C₄` with two opposite edges doubled.
>
> (iii) The `n = 2` family carries **no** `k = 4` triple (four branches of
> total 18 with the split branch 3 and each ≤ 5 forces `(3,5,5,5)`, which
> has no length-4 `b`–`c` companion). So the stratum lives over
> `n_hub ∈ {3,4}`.
>
> (iv) Enumerating all branch-length tuples over (ii): **600** class shapes
> carrying a (length-3 split branch, length-4 companion) pair; **470** of
> them carry a bare-cycle site; **1976** bare-cycle sites in total. Every
> shape met has `girth(G) = 7` and `girth(G′) = 6` exactly, and every branch
> of every `G′` has length ≤ 5.

*Why this is exhaustive, and where it exceeds `outer.sweep_shapes`.* Each
filter the enumeration applies is a **necessary** condition of the object
being enumerated — `c(G) = 3` ((ANH-13)(iv)); loopless and `n_hub ≤ 4` by
(i); split branch of length exactly 3 (that is what `orient`/`split_data`
means); a length-4 `b`–`c` companion (that is what `k = 4` means); branch
lengths in `[1,5]` ((SD-6), and the driver runs `lmax = 6` and observes the
maximum is 5, so the bound is not doing hidden work). `kslidecomb.shape_ok`
is the *class* certification and its `hnoRigid` half is tested at branch
granularity, i.e. it accepts a **superset** of class shapes — which is the
safe direction for an exhaustiveness claim. The sweep, by contrast, runs
`theta3` / `theta4` / `K4` / `K4+par` plus **simple** 5-hub graphs; at
`c(G) = 3` only `theta4` and `K4` are in range, so the `n = 3` `(1,2,2)`
multigraph and the `n = 4` doubled-`C₄` were never swept. Labelled site
counts per family are `K4` 1896, doubled-`C₄` 48, `n = 3` 32; but **labelled
counts are the wrong unit for comparing the two censuses** — see (FR-14).

**This is the sentence (ANH-14)(b) and (FR-5) had to hedge, and it no longer
needs hedging.** "Every class shape" *is* established on the bare-cycle
stratum, because on that stratum "every class shape" is a finite list.

> **(FR-14)** *(proven; asserted by `--recon`, which keys both censuses by
> shape isomorphism class — canonical over the ≤ 24 hub permutations, exact
> since `n_hub ≤ 4`)*
>
> (i) **The enumeration misses nothing.** Of the **14** isomorphism classes
> the (ANH-9) pool carries with a bare-cycle site, **0** are absent from the
> complete-stratum enumeration; all 14 lie inside the swept `K4` family. The
> enumeration carries **22**, so the 8 extra classes — 4 over the `n = 3`
> `(1,2,2)` multigraph, 4 over the `n = 4` doubled-`C₄` — are exactly what
> the sweep never saw.
>
> (ii) **Site counts are class-level invariants; the published totals are
> not.** The number of bare-cycle sites of a labelled shape depends only on
> its isomorphism class (asserted). Summed over classes: **58** for the
> pool's 14, **76** for the complete 22. The *labelled* totals are
> `1904 = 58 + 1846` and `1976 = 76 + 1900`, the second summand in each
> being the duplicate-induced over-count of a shape list that carries
> isomorphic copies (433 labelled shapes for 14 classes; 470 for 22). One
> `K4` class — hub multigraph `K4`, branch lengths `(1,1,3,5,3,5)`, 8 sites
> — is carried **49 times** in the pool, once by `named_inventory` (as
> `flank:K4 menu-blocked`) and 48 times by the `K4` sweep family.
>
> (iii) **Consequently the `1904` vs `1896` difference is a multiplicity
> artifact, not a missing-site gap in either direction.** Both lists cover
> the same 14 classes over the `K4` family; they weight them differently.
>
> (iv) **At `c(G) = 3` every length-5-branch site is a bare-cycle site**
> (`other5 = 0`, and no `e0 is None` branch occurs), asserted over all 470
> labelled shapes — which is (ANH-13)(iv) measured over the complete
> stratum rather than over the sweep.

**The `c′ ≤ 1` columns of §(K-ann) *Step A14*, re-derived over the complete
strata** (`--recon` part 3). The `c′` histogram
`{0: 8, 1: 1904, 2: 3846, 3: 276, 4: 392}` counts (shape, split, length-4
companion, length-5 branch) instances over the same pinned pool, so its
cells are labelled counts of the same kind:

| cell | complete stratum, per iso class | complete stratum, labelled | the landed pool figure |
|---|---|---|---|
| `c′ = 0` (`c(G) = 2`) | **2**, over **1** iso class — `θ(3,4,5)`, 2 eligible splits × 1 companion × 1 loop branch | 4 | **8** |
| `c′ = 1` (`c(G) = 3`) | **76**, over **22** iso classes | 1976 | **1904** |

`c(G) = 2` has one hub multigraph (three parallel edges), and with the split
branch pinned at 3, lengths ≤ 5 summing to 12 and a length-4 companion
required, **θ(3,4,5) is its unique inhabitant** — which re-derives §(K-out)
*Step O12*'s "unique theta class member" from the length arithmetic alone.

**What this does to the landed histogram: a framing fix, not a number
change.** Every cell is a *true statement about the pinned pool's labelled
shape list*, which is what `anhr1.py --size` measures and what its own
prose says ("over the full 4296-triple pool of *Step A9*"). It becomes wrong
only under a class-level reading — "1904 bare-cycle sites *exist*", "8
`c′ = 0` sites *exist*" — which the surrounding text does not quite make,
but which a reader can easily take. The repair is therefore (a) say
*labelled instances of the pinned pool*, not sites of the class; (b) record
the class-level figures above alongside; (c) record that at `c′ ≤ 1` the
sweep is **incomplete at the iso-class level** (14 of 22 at `c′ = 1`) and
that (FR-8) supplies the complete list. The 29.6 % ratio (`1904/6426`)
survives as a pool ratio and should be labelled as one; it is **not** a
class-level ratio, and no class-level ratio is available, since the `c′ ≥ 2`
cells sit where the `|V°| ≤ 5` cap genuinely binds.

### Step FR8 — (FR-9): the frame's normal form in `G′`

> **(FR-9)** *(proven; every clause asserted per site at 1904/1904 pool
> sites (`--frame`) and 1976/1976 stratum sites (`--strat`))* At a
> bare-cycle site:
>
> **(a) `H/P` is exactly (bare 6-cycle) ∪ β and nothing else.**
> `|E(H/P)| = 11 = 6 + 5` and `|V(H/P)| = 10 = 6 + 4`; β is not a loop
> (a loop of length 5 would be a 5-cycle of `H/P`, and `girth(H/P) ≥ 6`
> off `|E(H/P)| = 5` — §(K-ann) *Step A9*). So β joins two distinct cycle
> nodes, of `H/P`-degree 3; every other cycle node has degree 2.
>
> **(b) The frame is a 7-point open path in `G′`.** The cycle's nodes are
> `X` (always on it, (ANH-13) trap (b)) and five far bodies `z₁…z₅`; far
> bodies satisfy `deg_{G′} = deg_H = deg_{H/P}`. Reading the cycle from `X`
> gives `x — z₁ — … — z₅ — x′` in `H ⊆ G′`, with `x, x′ ∈ P` the two
> companion attachment points. (The closed-hexagon degeneration `x = x′` of
> (ANH-14)(a) occurs **0 times** in the whole stratum; the argument below
> does not depend on that.)
>
> **(c) `x` and `x′` are hubs of `G′`.** `b` and `c` are hubs by
> `split_data`; an interior companion vertex carries two `P`-edges plus its
> frame edge.
>
> **(d) `S := {i : deg_{G′}(z_i) ≥ 3}` has `|S| ∈ {1, 2}`.** `≤ 2` by (a);
> `≥ 1` because the frame has length 6 while every branch of `G′` has length
> ≤ 5 — `G′`'s branch multiset is `G`'s with the length-3 split branch
> shortened to 2, and `G′` has the same hubs as `G`. Measured over the
> stratum: `{1: 1928, 2: 48}`.
>
> **(e) Each hub `z_j` has all of its hub-hub edges on the frame.** Its
> three `G′`-neighbours are its two frame neighbours and β's first interior
> node, which has `H/P`-degree 2. So `z_j`'s `Λ`-edges are among
> `{f_{j−1}, f_j}`, and are present only when the corresponding frame
> neighbour is a hub — i.e. only at `j = 1` (`f₀ = x z₁`) or `j = 5`
> (`f₅ = z₅ x′`).
>
> **(f) No `H`-edge joins two frame vertices except the six frame edges and
> possibly the `P`-edge `x x′`.** Such an edge would be an extra
> `H/P`-edge between two cycle nodes, contradicting (a) (β has length 5, not
> 1); edges inside `P` are contracted away, and by girth the only `P`-chord
> is a `P`-edge. (`x x′ ∈ E(H)` at **576** of the 1976 sites.)
>
> **(g) When `|S| = 2`, EVERY hub-hub edge of `G′` is a frame edge.** Then
> both β-endpoints are far bodies, so `deg_{H/P}(X) = 2`, i.e.
> `Σ_{p∈P} deg_H(p) = 10`, i.e. `deg_G(b) = deg_G(c) = 3` and
> `deg_G(x_i) = 2`; hence `x = b`, `x′ = c`, the hubs are exactly
> `{b, c} ∪ {z_j}_{j∈S}`, and by (e)/(f) every edge between two of them is a
> frame edge.
>
> **(h) `Λ` is a disjoint union of paths on ≤ 4 vertices.** (R4) gives max
> degree ≤ 2; a `Λ`-cycle would be a cycle of `G′` on hubs only, hence
> (it cannot use `ab`, `a` having degree 2) a cycle of `G`, of length ≥ 7,
> while `n_hub ≤ 4`. Measured: only paths on 2 or 3 vertices occur.
>
> **(i) The frame is exactly `|S| + 1 ∈ {2,3}` COMPLETE, pairwise-distinct
> branches of `G′`.** Each maximal run between consecutive frame hubs has
> degree-2 interior and hub ends, hence is a whole branch; two runs are
> edge-disjoint and separated by a hub, so they are different branches.
> Run-length profiles over the stratum: `(1,5) 368, (2,4) 368, (3,3) 464,
> (4,2) 368, (5,1) 360` at `|S| = 1`, and `(1,2,3) (1,3,2) (1,4,1) (2,2,2)
> (2,3,1) (3,2,1)` at 8 each at `|S| = 2`.

### Step FR9 — (FR-10): the component law, and what the two legality clauses actually say

> **(FR-10)** *(proven; both halves driver-asserted, `--validate`)*
>
> **(i) Only hub-hub edges propagate a ruling component.** Within a branch
> the colours alternate ((AC-2) conjunct 4 / *Step G12*), so two same-family
> edges of one branch are never adjacent. Consequently: two hubs lie in the
> same `A`-component **iff** they are joined by a path of `A`-coloured
> hub-hub edges; a frame edge with **no** hub endpoint is a **singleton**
> ruling component; and every `A`-component is a star at a hub, a double
> star across an `A`-coloured `Λ`-edge, or a single interior edge. (Asserted
> hub-pairwise over every admissible colouring of every census split.)
>
> **(ii) Legality clause (ii) IS "`Λ` is properly edge-2-coloured".**
> `closedHubNbhd u` has three members exactly when `u` is a hub with two hub
> neighbours, and then it is `{u, w₁, w₂}` with `uw₁, uw₂ ∈ Λ`. If both are
> `A`, all three sit in one `A`-component and the clause fails. Conversely
> if no hub carries two same-family `Λ`-edges, `Γ_A` and `Γ_B` are
> matchings, every `Γ_A`-component has ≤ 2 hubs, and `{u,w₁,w₂}` is never
> mono. (Asserted as an **iff** over 8728 (split, colouring) pairs.)

**The one place a refutation could have lived, and the constructed witness
that shows the mechanism is real.** By (ii), a graph whose `Λ` contains an
**odd cycle** admits *no legal admissible colouring whatsoever*, so (FR-R1)
would fail at every one of its bare-cycle sites — a clean structural flank,
of exactly the shape `Pencil-strategy.md` §2.3 warns to look for. `--kill`
**constructs** such a graph (a 5-cycle of hubs, each with a pendant 2-path
to a common body): 1024 admissible colourings, **0** legal; and its
6-cycle-of-hubs control has 4 legal of 4096. So the mechanism fires and the
mechanism is **parity**, not size. It is unrealizable on this stratum by
(FR-9)(h) alone — and that is the whole of the argument's dependence on
`hnoRigid` beyond the class definition.

### Step FR10 — (FR-11): the recipe, and (FR-R1) proven

> **(FR-11)** *(proven; the construction runs green at 1904/1904 pool sites
> and 1976/1976 stratum sites, in its **first** variant every time)* At any
> bare-cycle site define a colouring of `G′` by:
>
> 1. **frame branches** — set the `|S| + 1` free bits so that the frame path
>    *alternates*: `col(f_i) = A ⟺ i` even;
> 2. **`Λ`** — properly edge-2-colour it (alternate along each `Λ`-path),
>    seeded by whatever step 1 already forced;
> 3. **every other branch** — the bit 0.
>
> This is well defined (step 1 by (FR-9)(i); step 2 by (FR-9)(h) plus the
> observation that the frame's `Λ`-edges are *consecutive* frame edges,
> hence already alternating; step 3 vacuously), and it is a **pattern
> colouring**: it meets (FR-4)'s (pattern) clause and both legality clauses.

*Proof of the pattern clause.*

**3–3.** The frame path has even length 6 and alternates. ∎

**Three distinct components per family.** Say `A = {f₀, f₂, f₄}`. By
(FR-10)(i) a frame edge with no hub endpoint is a singleton component, so it
is automatically distinct from everything; only *anchored* frame edges (those
with a hub endpoint) can collide, and two same-family anchored frame edges
collide iff some hub of one and some hub of the other are joined by a path
of same-family `Λ`-edges.

*Case `|S| = 1`, `S = {j}`.* By (FR-9)(e):

- `j ∈ {2,3,4}`: `z_j` has `Λ`-degree **0**, so its component is `{z_j}`.
  The anchored `A`-edges are `f₀` (at `x`) and, when `f_{j−1}` or `f_j` is
  `A`, that edge (at `z_j`); `x ≠ z_j`, so they are distinct. Mirror for `B`
  with `x′`.
- `j = 1`: `f₀ = x z₁` is `z₁`'s only `Λ`-edge and is `A`. Then `f₀` is the
  **only** anchored `A`-edge (`f₂`, `f₄` have no hub endpoint), so there is
  nothing to separate; and `Γ_B(z₁) = {z₁} ∌ x′`, so the anchored `B`-edges
  `f₁` (at `z₁`) and `f₅` (at `x′`) are distinct.
- `j = 5`: the mirror image.

*Case `|S| = 2`.* By (FR-9)(g) every `Λ`-edge is a frame edge; consecutive
frame edges alternate, so `Γ_A` and `Γ_B` are matchings, and a same-family
`Λ`-edge joining the hubs of two anchored same-family frame edges would be a
second same-family frame edge at a common frame vertex — impossible under
alternation unless it *is* one of them, which forces the two anchored edges
to coincide. ∎

**Legality (ii)** is step 2 plus (FR-10)(ii). **Legality (i)** is *Step
FR11*. ∎

> **(FR-R1) — PROVEN.** *Every bare-cycle site of every `k = 4` class triple
> admits a pattern colouring.* The pattern clause and legality (ii) hold by
> (FR-11) uniformly; legality (i) holds by (FR-12); and independently of the
> argument, the whole (finite) stratum is enumerated with a pattern
> colouring exhibited at every one of its **1976** sites, the scarcest
> having **16** of 32 admissible colourings pass.

**What this buys, said exactly.** By §(K-frame) (FR-4), a pattern colouring
at a site gives an exact ℚ(i) chart point of the triple with the universal
polynomial `C ≠ 0` there, and by §(K-ann) (ANH-9)(iii) that **proves** the
(ANH-R1) β-clause at that site. So **the (ANH-14) chart-to-frame dominance
residue is discharged on the entire bare-cycle stratum as an argument** —
1904 of §(K-ann)'s 6426 length-5-branch sites — with (FR-4)'s single named
gap ((GR-5) restated at `G′`) riding along unchanged. Nothing here touches
the other 4522 sites, the (OC-16) side, or class uniformity of `hK`.

### Step FR11 — (FR-12): legality clause (i) is *vacuous* on this stratum

> **(FR-12)** *(proven; characterization asserted and count measured over
> **every** admissible colouring of **every** stratum site, `--strat`)*
>
> (i) **Characterization.** Two bodies of `G′` share a grid point iff they
> lie in the same `A`-component and the same `B`-component. Such a pair is
> always **two interiors of length-2 branches**: hubs never collide with
> hubs (a `Γ_A`-link and a `Γ_B`-link would be the same `Λ`-edge in two
> colours); a hub never collides with a non-hub, and two *adjacent*
> non-hubs never collide, because each such configuration closes a cycle of
> `G′` of length ≤ 4, hence a cycle of `G` of length ≤ 5; and a degree-2
> body whose `A`-neighbour is a non-hub has `A`-component of size 2, which
> forces the partner to be that neighbour.
>
> (ii) **Vacuity.** No such pair exists at any colouring of any bare-cycle
> site. Let `u` (between hubs `p_A`, `p_B`) and `w` (between `q_A`, `q_B`)
> collide. If `{p_A,p_B} = {q_A,q_B}` the two branches close a 4-cycle of
> `G′` — impossible (`girth(G′) = 6`). Otherwise the `Γ_A`-path from `p_A`
> to `q_A` (length `t ≥ 1`) and the `Γ_B`-path from `p_B` to `q_B` (length
> `s ≥ 0`) close a cycle of `G′` of length `4 + t + s`, so `t + s ≥ 2`.
> Every `Λ`-edge on those paths is a **length-1 branch**, and every hub it
> meets is a distinct hub, so `t + s ≤ 3` by `n_hub ≤ 4`; and `t + s ≥ 3`
> already needs ≥ 5 distinct hubs. So `t + s = 2`, the cycle has `G′`-length
> 6 and therefore `G`-length 7 (it must run through the split branch, since
> `girth(G) = 7`), and it consists of two length-2/3 branches and two
> length-1 branches — total 7 of the 18 edge-lengths across 4 of the
> `n_hub + 2 ≤ 6` branches, leaving ≤ 2 branches to carry 11 with each
> ≤ 5. Contradiction. **Measured: 0 collisions.**

*(Read (FR-12)(ii) as the uniform reason behind a measured 0, not as a
substitute for it: the count is what the driver asserts; the argument is why
it had to be 0. The two together are why legality (i) needs no repair step
in the recipe.)*

### The (`≤3`-closedHubNbhd) line — which side this argument sits on

`notes/Phase39.md` *Blockers* records that feasibility propagation **as a
proposition** is refuted for any purely combinatorial `≤3`-closedHubNbhd
criterion (`not_pencilNondegFeasible_of_triangle_two_hubs`). **This
direction's results sit entirely on the other side of that line, and
(FR-10)(ii) is the clause that has to say so out loud.**

- (FR-10)(ii) is an equivalence about **one constructed configuration**: it
  says that the σ-fixed grid point built from a given `col` has, at each
  3-member closed hub neighbourhood, three non-collinear quadric points
  **iff** `col` 2-colours `Λ` properly. It quantifies over *colourings of a
  fixed graph*, never over placements, and it concludes about a **point**,
  never about `PencilNondegFeasible G`.
- Nothing here propagates: (FR-11) *constructs* a witness and (FR-4) reads
  its consequence through rank lower semicontinuity on the irreducible chart
  ((ANH-9)(iii)), exactly as §(K-frame) already does. There is no step of
  the form "the combinatorial criterion holds, therefore the graph is
  feasible".
- The two statements are in fact **logically independent**, and the
  `--kill` witness makes that concrete: its odd-`Λ`-cycle graph is one where
  *the σ-fixed grid construction can never be legal*, which says nothing
  about whether that graph is `PencilNondegFeasible` (a question about all
  placements). Reading (FR-10)(ii) as a feasibility criterion would be
  exactly the move the landed refutation forbids — so **do not**; it is a
  criterion for *this construction's* hypotheses.

**The coordinator's flagged hypothesis (F14) is therefore confirmed as
stated**, and the confirmation is sharper than the hypothesis: it is not
merely that (FR-4)'s clause is checked at a constructed point, it is that
the clause's exact combinatorial content ((FR-10)(ii)) is a statement about
`Λ`'s edge-colouring — an object that only exists once a colouring is
chosen, i.e. only downstream of the construction.

### Verdict — what this buys, exactly

- **§(K-frame) (FR-R1): PROVEN**, and the section's *What would change this*
  item (i) is discharged in the affirmative. The route item (i) sketched —
  "alternation is nearly free; the content is keeping the three same-family
  edges in distinct components; *Step G12*'s branch bits plus girth 6 look
  sufficient" — is **correct in shape and understated in strength**: the
  three same-family edges are kept apart *automatically* once the frame's
  normal form ((FR-9)(e)/(g)) is available, and the binding girth number is
  **7**, not 6, which is what makes legality (i) vacuous ((FR-12)).
- **§(K-ann) (ANH-14) / the (K-ann) gap-map cell**: the chart-to-frame
  residue on the bare-cycle stratum is **closed as an argument**, with
  (FR-4)'s named (GR-5)-at-`G′` gap the only rider. The residue sentence's
  (FR-R1) form can be retired in favour of "proven; one named gap".
  *Coordinator's call whether the cell moves; the status of `hK` does not.*
- **(ANH-14)(b)'s boundedness caveat: DISCHARGED on this stratum** (not
  widened). This is the first time in the arc that a "the pool is not the
  class" caveat has been removed rather than enlarged, and the reason is
  structural (`c(G) = 3` is finite), not computational.
- **A latent sweep gap, measured and bounded**: `outer.sweep_shapes` misses
  two of the four `c(G) = 3` hub multigraphs, i.e. **8 of the 22**
  isomorphism classes of the bare-cycle stratum, carrying **18 of its 76**
  class-level sites ((FR-14)(i)/(ii)). §(K-ann) *Step A14*'s `c′`
  histogram is the place this shows: its `c′ = 0` and `c′ = 1` cells are
  labelled pool counts, true as such and incomplete as class statements —
  the repair is spelled out in *Step FR7* and is **framing, not
  arithmetic**.
- **An incidental §(K-ann) gain, worth recording where (ANH-14) lives.**
  (ANH-14)(a) measured its "seven distinct points" clause at **6/6**
  census-pool sites and explicitly noted that distinctness was *not*
  measured over the full 1904. (FR-9)(b) measures it at **1904/1904** and
  at **1976/1976** over the complete stratum — and the degenerate
  closed-hexagon alternative `x = x′` **never occurs**. So (ANH-14)(a)'s
  hedge ("either way one of two universal polynomials governs the site")
  can be simplified: on this stratum it is always the **open 7-point
  chain**, hence always the single irreducible degree-12 `C` of
  (ANH-14)(c)/(d), never (e)'s closed-hexagon two-term form.
- **Class uniformity is untouched. No gap-map *status* moves.**

### Verification

`notes/scripts/w4/patexist.py` (new, untracked; graph-combinatorial only —
no placement is built, no arithmetic beyond graph search, so there is no
sampled object to guard and no exactness question to raise; the single
`random.Random` is `--kill`'s tie-break, seeded 20260807 and printed).
Imports only catalogued primitives and owning drivers read-only:
`exactcore` (`neighbors`), `kbare_common` (`verts_of`, `is_2ec`),
`nogood_subdiv` (`hcard_ok`, `triangles`), `closure`
(`alternation_classes`, `colourings`, `components`), `outer` (`split_data`,
`eligible_splits`, `shapes_from`, `companions4`), `shrink` (`census_pool`),
`annih` (`girth`, `path_edges`), `shrink` (`hp_edge_rows`), `anhr1`
(`core_decompose`), `framedom` (`bare_sites`, `pool_splits`, `chn_sets`,
`line_ids`, `crit_33`, `legality_free`). Seven local devices, each named as
such in its docstring: `branches_with_ends` and `shape_key` (the canonical
`closure.alternation_classes` returns a branch as an *edge set* with
parities and does not name its two hub ends, which is exactly what an
isomorphism key needs), `len5_sites` (`framedom.bare_sites` with the
`e0 is None` arm counted rather than skipped — and asserted equal to it on
the two arms they share), `frame_path` (the frame ordering — `bare_sites`
returns the six edges in the *contracted* cycle's order, which does not say
where the weld breaks them open), `lambda_graph` / `lam_components`,
`c3_hub_multigraphs`, and `collisions` / `both_len2_interiors`. Nothing
existing is modified (`git diff --name-only -- '*.py'` empty), so the
figure-invariance gate discharges on that check alone. From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --frame     # 12 s  (FR-9) at 1904/1904 pool sites
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recipe    # 12 s  (FR-11) constructed, 1904/1904
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --strat     #  3 s  (FR-8)+(FR-12), the COMPLETE stratum, 1976/1976
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recon     # 15 s  (FR-14) + the c' <= 1 cells re-derived
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --kill      # 12 s  cheap kill + the odd-Lambda-cycle witness/control
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --validate  # 12 s  (FR-10)(i)/(ii) + the free-bit dictionary
```

All six modes byte-identical under `PYTHONHASHSEED` 0 and 999; every
invocation far inside the 600 s budget. Nothing gates on `repin.star_generic`
(no placement is sampled anywhere), no figure is a `place_pencil_general`
rate, and every claim is an exhaustive scan of a pinned finite object, an
asserted equivalence, or a constructed witness.

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (FR-8)(i)–(iii) | — | **proof-level** (three lines of counting); the multigraph list it predicts is what (iv) enumerates |
| (FR-8)(ii) | `--validate`, `--strat` | the multigraph census printed and pinned at 4, with multiplicities |
| (FR-8)(iii)/(iv) | `--strat` | 0 shapes over the `n = 2` family; 600 shapes / 470 with sites / 1976 sites; `lmax = 6` with max branch 5; `(girth G, girth G') = (7,6)` at 470/470 |
| (FR-9)(a)–(i) | `--frame`, `--strat` | every clause asserted **per site**, 1904/1904 and 1976/1976, 0 misses; the histograms are the by-product |
| (FR-10)(i) | `--validate` | for every admissible colouring of every census split, `same A-component` == `connected in the A-coloured hub-hub graph`, hub-pairwise |
| (FR-10)(ii) | `--validate` | legality clause (ii) == `Λ properly edge-2-coloured`, as an **iff**, 8728 (split, colouring) pairs |
| the odd-`Λ`-cycle mechanism | `--kill` | a **constructed** odd-`Λ`-cycle graph: 0 legal of 1024; even-cycle control: 4 legal of 4096 (F13: the guard has a witness it must reject *and* a negative control) |
| (FR-11) | `--recipe`, `--strat` | the recipe's colouring passes `crit_33` **and** `legality_free` at 1904/1904 and 1976/1976, in variant `(flip=False, other=0)` every time — i.e. no search |
| (FR-12)(i) | `--strat` | every collision found over every colouring of every site is asserted to be a length-2-branch-interior pair (the assert stands whether or not any is found) |
| (FR-12)(ii) | `--strat` | the collision count over the complete stratum: **0** |
| (FR-14)(i) | `--recon` | both censuses keyed by iso class; `set(pool) − set(stratum)` **asserted empty**, and `set(pool) ⊆ K4-family classes` reported |
| (FR-14)(ii) | `--recon` | site count asserted constant on each iso class; `labelled == iso total + duplicate over-count` asserted for both lists; the 49-fold duplicate exhibited |
| (FR-14)(iv) | `--recon` | `other5 == 0` and `loop0 == 0` asserted at all 470 `c(G) = 3` labelled shapes; `len5_sites` asserted equal to `framedom.bare_sites` per split |
| the `c′ ≤ 1` cells | `--recon` | the complete `c(G) ∈ {2,3}` strata enumerated and their `c′ = 0` / `c′ = 1` counts printed at both granularities |
| (FR-R1) | `--strat` | the exhaustive colouring scan: **0** sites with zero pattern colourings, scarcest 16/32 |
| (FR-4)'s named gap | — | **untouched and not driver-testable**: (GR-5) restated at `G′` is prose |

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(FR-8)** | the bare-cycle stratum is finite: 4 hub multigraphs, 600 shapes, 470 with sites, **1976** sites | **proven** (counting + exhaustive enumeration; every filter a necessary condition, `shape_ok` accepting a superset) |
| **(FR-9)** | the frame's normal form: 7-point path, hub ends, `\|S\| ∈ {1,2}`, hub `z_j`'s `Λ`-edges are frame edges, no other frame chords, 2-or-3 complete distinct branches | **proven** (from `\|E(H/P)\| = 11` and girth; every clause asserted at 3880 site-instances) |
| **(FR-10)** | hub-hub edges are the only component propagators; legality (ii) **is** the proper edge-2-colouring of `Λ` | **proven** (both halves asserted as equivalences) |
| **(FR-11)** | the recipe; pattern clause + legality (ii) | **proven-informally** (uniform case analysis, no residue; construction green 1976/1976 first variant) |
| **(FR-12)** | legality (i) is vacuous on the stratum | **proven-informally** (girth-7 + branch-count argument), **measured 0** over every colouring of every site |
| **(FR-14)** | the two censuses reconciled by isomorphism class: 0 missing, 14 of 22 swept, the gap a multiplicity artifact; the `c′ ≤ 1` cells re-derived | **proven** (canonical keying, exact at `n_hub ≤ 4`; every step asserted) |
| **(FR-R1)** | class-uniform pattern-existence on the bare-cycle stratum | **PROVEN** — by (FR-11)+(FR-12) uniformly, and independently by exhaustive enumeration of the finite stratum |

**Class uniformity of `hK` is untouched. No gap-map *status* moves.**

### What would change this

*(i)* **RESOLVED in this draft, by (FR-14) and *Step FR7*'s table.** The
open item this slot carried — "a `c(G) = 3` figure quoted from
`outer.sweep_shapes` is suspect" — is settled: the sweep's `c′ ≤ 1` figures
are **correct as labelled pool counts** and **incomplete as class
statements** (14 of 22 iso classes at `c′ = 1`; 1 of 1 but 4× duplicated at
`c′ = 0`). The concrete edit to §(K-ann) *Step A14* is: keep the histogram,
say *labelled instances of the pinned pool*, add the class-level line
(`c′ = 0`: 2 sites over the single class θ(3,4,5); `c′ = 1`: 76 sites over
22 classes), and mark the 29.6 % as a pool ratio. **No landed number is
wrong.** What is *not* settled, and stays out of scope here, is the
`c′ ≥ 2` cells: there `|V°| ≤ 5` genuinely binds and no complete
enumeration is available (nor is one finite — `c(G) ≥ 4` shapes are
unbounded in `n_hub`).

*(i′)* **The duplication itself is worth a one-line note wherever pool
figures are quoted.** `--recon` measures 433 labelled shapes for 14 iso
classes (a 31× average, 49× at the worst class). That is by design — the
sweep families overlap and `named_inventory` re-lists habitats — but it
means **no pool count is a count of mathematical objects**, and any future
"N of M" over `outer.sweep_shapes` inherits the same caveat. This is a
`notes/scripts/README.md`-level observation, not a §(K-frame) one.

*(ii)* **Closing (FR-4)'s named gap** — (GR-5) restated at `G′` — would turn
(FR-R1)+(FR-4) into an unconditional discharge of the (ANH-14) residue on
the bare-cycle stratum. Two lines of prose in §(K-grid); the hypotheses are
already asserted per instance by `framedom.py --transport`.

*(iii)* **The same technique on the `c′ ≥ 2` strata.** Everything above
turns on `H/P` being *exactly* a 6-cycle plus one branch. At `c′ = 2`
(3846 sites, the largest stratum) `H/P − β` has 12 edges and 11 nodes and is
no longer bare, so (FR-9)(a) fails and the determinant law (FR-3) no longer
reduces to a 6×6 pattern — the pure condition there is (ANH-13)'s
`6m × 6m` branch-screw determinant. Whether a *pattern-colouring* analogue
exists for that determinant is the natural successor question, and it is
**not** a corollary of anything here.

*(iv)* **A transfer to §(K-grid) (GR-15)** (direction TCOL's target). The
transferable technique is not the recipe but its two enablers: *reduce the
colouring question to a statement about `Λ` alone*, and *use `hcard` + girth
to bound `Λ` so hard that the statement becomes vacuous*. (GR-15) carries a
spline/rank side that (FR-R1) does not, and its shapes are tight (hence
`c(G)` unbounded, hence `n_hub` unbounded), so the *finiteness* half — the
decisive one here — does **not** transfer. Say so plainly to TCOL: the
useful export is (FR-10)(i)'s component law and (FR-10)(ii)'s reading of the
closed-hub-neighbourhood clause, both of which are statements about
admissible colourings in general and hold verbatim at any shape.

*(v)* **A refutation would have to come from the mechanism (FR-10)(ii)
names** — an odd `Λ`-cycle, or a `Λ`-parity clash between two forced frame
`Λ`-edges. Both are constructible as graphs (`--kill` builds the first) and
both are excluded here by `n_hub ≤ 4`. Any future stratum with more hubs
should be checked against them **first**; they are the cheap kill for this
family of questions.

**Continuation (2026-08-19, sixth fan-out direction FRES) — (FR-4)'s named gap is CLOSED, and the closing needed a clause the gap's own name did not carry: (GR-5) restates at `G′` verbatim ((FR-15), every hypothesis either free or already driver-asserted), but (GR-5) is a *chart-MAP* statement — hub normals free, body points derived — while (ANH-9)(iii)'s semicontinuity consumes membership in the *chart VARIETY* of (ANH-9)(ii), whose parametrization runs the other way (hub points free, panel normals derived); (FR-16) supplies that second statement, and the mechanism is that at a σ-fixed configuration `normal ∝ point` makes the two parametrizations' genericity loci COINCIDE — both are exactly the closed-hub-neighbourhood LI clause `framedom.legality_free` already tests — so (FR-17) discharges the (ANH-14) residue on the WHOLE bare-cycle stratum with NO named gap, by formula rather than by search, and with no driver run at all.**

Answering `notes/Pencil-fanout-archive.md` §"Sixth fan-out" → Direction FRES, i.e.
§(K-frame) *Step FR3*'s **(FR-4) named gap** and *What would change this* item
(v) — "the (GR-5)-at-`G′` restatement, written". Read against §(K-grid) *Step
G6* ((GR-5)) and *Step G13*; §(K-frame) *Steps FR3/FR4* ((FR-4)/(FR-5)) and
*Steps FR7–FR11* ((FR-8)–(FR-14), (FR-R1)); §(K-ann) *Steps A10/A15*
((ANH-9)(ii)/(iii), (ANH-14)); §(K-clos) (AC-2)/(AC-4)/(AC-9); §(K-ind) *Step
I2* ((I2), girth `≥ 7`); the *Shared dictionary*'s (R1)/(R3)/(R4). **No driver
was run and no driver was written**: every hypothesis this block consumes is
already asserted per instance by the landed `framedom.py --pattern` /
`--transport`, and everything on top is proof. The reserved
`notes/scripts/w4/fres.py` is **returned unused**.

**Status, stated before the mathematics.**

- **The restatement is real, and it is as cheap as the record predicted —
  but it is not the statement the consumer needs.** (FR-15) transports (GR-5)
  to `G′` hypothesis by hypothesis: `hcard` is **free** (it is a consequence of
  `hK`'s own `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` hypothesis,
  and independently of §(K-ind) (I2): the split leaves the hub set and the
  hub-hub subgraph `Λ` untouched); the non-hub star-rank-3 condition is **free**
  (admissible alternation at a degree-2 body *is* that condition); the
  3-member-`closedNbhd` clause is **free** (`girth(G′) ≥ 6`); the two remaining
  inputs are (FR-4)'s own legality clauses. Its **final** clause — "at a
  target-rank grid this *is* `hK`'s conclusion" — does **not** transport, and is
  dropped: `G′` is not tight.
- **The clause the gap's name did not carry.** (GR-5) concludes
  `pencilChartPoint (PencilSeed.ofCoord q) hubSel u ∝ pt_u`: the grid is
  reproduced by a **seed** of `Chart.lean`'s construction, whose free data are
  the **hub normals** and whose body points are *derived*. (ANH-9)(iii) instead
  runs rank lower semicontinuity **on the irreducible chart of (ANH-9)(ii)**,
  which is the image of the **opposite** parametrization — hub **points** free,
  panel normals derived, interiors panel-constrained — i.e. literally
  `widened.place_pencil_general`, what `outer.chart_point` and
  `dominance.base_seed` sample and what every §(K-ann)/§(K-out) figure is
  measured on. Being a point of the first parametrization's image makes a
  configuration a *pencil configuration*; it does **not**, by itself, put it on
  the second's irreducible chart, and a witness sitting on a different component
  of the pencil-configuration variety would make the semicontinuity step void.
  **This is the direction's one genuine finding**, and it is the reason the
  outcome is "gap closed **plus** a stated extra ingredient" rather than
  "restatement immediate".
- **The extra ingredient is discharged, and by the clause already tested.**
  (FR-16): identify planes with points through the σ-fixed quadric's form and a
  σ-fixed configuration's panel normal at a hub **is** that hub's point. The
  points-first parametrization needs two open conditions — *hub points in
  general position along `Λ`* (so the panel normal is determined) and *panel
  normals pairwise distinct at every degree-2 body with two hub neighbours* (so
  the interior meets are lines) — and σ-fixity makes both of them the **same**
  condition, namely `{pt_w : w ∈ closedHubNbhd(u)}` linearly independent at
  every body `u`. That is (GR-5)'s own LI hypothesis, `framedom.legality_free`'s
  clause (ii) (plus (i)), and it is asserted exactly at every one of the 30
  built points by `--transport`. So the σ-fixed grid point is in the image of
  the (ANH-9)(ii) parametrization **at its generic-fibre locus** — not merely in
  its closure.
- **What that buys: an unconditional discharge on the whole bare-cycle
  stratum.** (FR-17). With (FR-R1) proven ((FR-11)+(FR-12), and independently
  the exhaustive enumeration of the finite stratum), (FR-3)'s determinant law,
  (FR-16), (ANH-14) and (ANH-9)(ii)/(iii), the (ANH-R1) `β`-clause holds at
  **every** bare-cycle site of **every** `k = 4` class triple — 76 class-level
  sites over 22 isomorphism classes — with **no named gap**. The witness is a
  **formula**: (FR-11)'s recipe colouring with *any* injective assignment of
  **positive** rationals to the ruling components; `framedom.build_at`'s seeded
  retry loop is a convenience, not a step of the argument.
- **"Unconditional" is a statement about named gaps, not about tier.** The
  chain's standing is the arc's ordinary **proven-informally** — its weakest
  links are (ANH-14)(c), (ANH-9)(ii)/(iii), (FR-1) and (FR-16), all
  informal-tier algebraic geometry, none Lean-checked. Nothing here is a rate, a
  sample, or a genericity guard, and nothing gates on `repin.star_generic` —
  σ-fixed points never pass it ((AC-9)), and the argument never asks them to.
- **What does not move.** The (OC-16) side gains one retro-certification and
  nothing else ((FR-16) applies verbatim to (FR-6)'s θ(3,4,5) points, so those
  four on-stratum colourings are honest chart points of `G′` — which is what
  "the first constructed, non-sampled inhabitants of that locus" was asserting).
  The (FR-6) follow-ons ((ii)/(iii)/(iv) of *Steps FR0–FR6*'s *What would change
  this*) are **untouched and remain un-commissioned**. §(K-grid) (GR-15) and
  **`hK`'s class uniformity are untouched**; the other ~70 % of §(K-ann)'s
  length-5-branch sites are untouched. **No gap-map *status* moves.**

### Standing notation (on top of §(K-frame) *Standing notation* and *Steps FR7–FR11*'s)

For a loopless multigraph `Γ`: `H(Γ)` its hubs (degree `≥ 3`), `Λ(Γ)` its
hub-hub subgraph, `d_h` the number of hub neighbours of a hub `h` and `e_s` the
number of hub neighbours of a non-hub `s`. `hcard` (= (R4)) says `d_h ≤ 2`;
`e_s ≤ 2` is automatic. `closedHubNbhd_Γ(u) = {w : deg_Γ w ≥ 3 and (w = u or
w ∼ u)}` (`Motive.lean:82`) — so at a **hub** it is `{h} ∪ {hub neighbours}`
(`1 + d_h` members) and at a **non-hub** it is `{hub neighbours}` (`e_s`
members). `closedNbhd_Γ(u) = {u} ∪ N_Γ(u)`. We write `Chart(Γ)` for the pencil
chart of `Γ` in the precise sense fixed in *Step FR13* below. Points are
homogeneous over `ℚ(i)`; `⟨·,·⟩` is the standard symmetric form `Σ x_i y_i`,
whose isotropic quadric is (AC-2)'s fixed quadric `Q`, and it is used
throughout to identify `(P³)^*` with `P³` — under that identification a plane
and its pole are the same vector, which is exactly what "σ-fixed" (`normal ∝
point`, §(K-clos) *Step Z2*) says at every body.

### Step FR12 — (FR-15): (GR-5) at `G′`, hypothesis by hypothesis — and the one clause that does not transport

> **(FR-15)** *(proven-informally, at exactly (GR-5)'s own standing; every
> transported hypothesis is either a two-line graph argument given below or
> asserted per instance by `framedom.py --pattern` / `--transport`)* Let `G` be
> a `k = 4` class shape, `v` an eligible split with `b — v — a — c`, and
> `G′ = G − v + ab = G.splitOff v a b e₀`. Let `pt` be a σ-fixed grid
> configuration of `G′` from an admissible colouring such that
>
> - all bodies are pairwise distinct as projective points, and
> - at every body `u` of `G′`, `{pt_w : w ∈ closedHubNbhd_{G′}(u)}` is linearly
>   independent.
>
> Then there are selectors `hubSel`, `nbrSel` and an explicit seed `q` over
> `ℚ(i)` with
>
> `pencilChartPoint (PencilSeed.ofCoord q) hubSel u ∝ pt_u` and
> `pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel G′ u ∝ pt_u`
>
> at **every** body `u` of `G′`.
>
> **(GR-5)'s final clause does not transport and is dropped.** "at a
> target-rank grid this **is** `hK`'s conclusion at `G`" is a statement about
> the *tight* shape `G`: `f(V(G′)) = f(V(G)) + 1`, so `G′` misses tightness by
> one and the count `6(|V|−1) − def` that `hK`'s conclusion carries is not the
> one a `G′`-grid attains. Nothing here re-derives it, and (FR-4)'s consumer
> does not want it.

*Proof.* (GR-5)'s proof is replayed verbatim; only its **inputs** need
transporting, and the table below does each one. The two clauses that are
genuinely graph-dependent are the last two rows, and both come out *free* at
`G′`.

| (GR-5)'s input | at `G` | at `G′` | why |
|---|---|---|---|
| `hcard` | class shape + feasibility | **free**, two independent ways | *(i)* `hK`'s own hypothesis `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` (`Escape.lean`, the `hK` slot of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`; **`hK` names `v`'s two neighbours `a, b` — the workbook's `b, a` — so `hK`'s `G.splitOff v a b e₀` is this section's `G′ = G − v + ab`, letters swapped and object identical**) unfolds to `IsNondegPencilRealization G′ …`, and the landed `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) gives `(G′.closedHubNbhd u).ncard ≤ 3` at every body — **`hcard` at `G′` is a hypothesis `hK` already carries about `G′` itself, not something transported from `G`.** *(ii)* Combinatorially, from `hcard` at `G`: by §(K-ind) (I2) `splitOff` at a degree-2 body leaves the hub set and the hub multigraph `G°` unchanged and shortens only the branch through `v` (here `3 → 2`), so the length-1 branches — i.e. `Λ` — are untouched; `v` and `a` are non-hubs, so neither the deleted edge `bv` nor the new edge `ab` is a hub-hub edge, and `closedHubNbhd_{G′}(h) = closedHubNbhd_G(h)` at every hub `h`. Asserted per instance: `hcard_ok(G′)` at all 1540 site-carrying splits, 0 failures ((FR-4)'s *Verification*, `--pattern`). |
| all bodies distinct | hypothesis | hypothesis | supplied by (FR-4) legality clause (i); **vacuous** on the bare-cycle stratum by (FR-12), and asserted exactly at every built point (`config_asserts`). |
| closed-hub-neighbourhood LI | hypothesis | hypothesis | supplied by (FR-4) legality clause (ii), whose exact combinatorial content is (FR-10)(ii)'s proper edge-2-colouring of `Λ`; asserted as an exact rank equality at every body of every one of the 30 built points (`--transport`). |
| isotropy / conjugacy of the configuration | (AC-2) | (AC-2) | graph-free; asserted per body and per edge at every built point (`config_asserts`). |
| non-hub **star rank 3** | hypothesis | **free from admissibility** | Let `s` be a degree-2 body of `G′` with neighbours `u, w`. Admissibility (`closure.alternation_classes`: the two edges at a degree-2 body get opposite rulings) gives `col(su) ≠ col(sw)`. Writing the grid map as the Segre embedding composed with a fixed `ℚ(i)`-linear isomorphism (`closure.grid_point` is bilinear in `(s:t)` and `(u:v)`, with invertible coefficient matrix), `pt_s = e_{s_s} ⊗ f_{u_s}`, `pt_u = e_{s_s} ⊗ f_{u_u}`, `pt_w = e_{s_w} ⊗ f_{u_s}` with `u_u ≠ u_s` and `s_w ≠ s_s` by distinctness — three tensors that are linearly independent in `K² ⊗ K²`. **So the alternation clause of admissibility *is* the star-rank-3 condition**, at `G′` and at `G` alike. |
| degree-2 bodies have **3-member** `closedNbhd` | "on a 2-edge-connected class shape" | **free** | Every non-hub of `G′` has degree exactly `2`: `G` is rigid so `deg_G ≥ 2` ((R1)), and by (I2) `splitOff` changes no surviving vertex's degree. Its two neighbours are distinct from it and from each other because `girth(G′) ≥ 6`: a `G′`-cycle either avoids `ab`, and is then a `G`-cycle, or uses `ab` and lifts to a `G`-cycle one edge longer, while `girth(G) ≥ 7` by (R3) + `hnoRigid` (§(K-ind) *Step I2*). Hence `IsFin3SelectorOf (G′.closedNbhd s) (nbrSel s)` is satisfiable with **no slot unassigned**, and `PencilSeed.ofCoord`'s `fillNbr := fillHub` coupling (`Engine.lean:89`) stays vacuous — the one clause of (GR-5)'s proof that reads the ambient graph at all. (`is_2ec(G′)` is asserted per instance anyway, 0 failures; 2-edge-connectivity of `G′` follows from that of `G` since suppressing a degree-2 body preserves it — but the proof needs only min degree 2 and girth `≥ 3`.) |

With the inputs in place the body of (GR-5)'s proof is unchanged and
graph-free: take `hubNormal w := pt_w`; at any body `u` every selected input of
`pencilChartPoint` lies in `pt_u^⊥` (isotropy for `u` itself, conjugacy for a
hub neighbour), `hcard` caps the selected inputs at 3, the LI hypothesis lets
the unused slots be filled inside `pt_u^⊥` keeping the triple independent, and
`cross₃` then returns a nonzero vector of the 1-dimensional annihilator, which
contains `pt_u`. Normals: at a hub the chart returns the seed's `hubNormal`; at
a non-hub it returns `cross₃` of the three `closedNbhd` chart points, each
`∝` its grid point, hence `∝ cross₃(pt_u, pt_{u'}, pt_{u''}) ∝ pt_u` by the same
isotropy/conjugacy argument, with the star-rank-3 row above supplying the LI. ∎

**What (FR-15) is worth, said plainly.** It is the statement the gap was
*named* after, it is true, and it is what `hK`'s conclusion object would need if
a later pass wanted `hK` itself at `G′`. It is **not** what (FR-4)'s consumer
needs — see *Step FR13*.

### Step FR13 — (FR-16): the clause the gap's name did not carry — chart-VARIETY membership, and why σ-fixity makes it free

**The correction, stated before the theorem.** §(K-grid) (GR-5) and §(K-ann)
(ANH-9)(ii) describe **two different parametrizations of the same incidence**,
and they run in opposite directions.

- **(GR-5) / `Chart.lean` — normals first.** Free data: the hub normals
  (`PencilSeed.hubNormal`, read only at `closedHubNbhd` members, i.e. only at
  hubs) plus the fill vectors. Derived: every body point, as
  `cross₃` of the selected normals. At a hub with two hub neighbours the point
  is fully **determined**; at a non-hub with two hub neighbours it sweeps the
  2-dimensional space `{n_{h₁}, n_{h₂}}^⊥`, i.e. the meet line of the two
  panels.
- **(ANH-9)(ii) / `widened.place_pencil_general` — points first.** Free data:
  the hub **points**. Derived: each panel normal, in the `≤ 2` linear
  conditions its hub neighbours impose; then each interior point, on the
  intersection of its hub neighbours' panels. This is the parametrization
  `outer.chart_point` and `dominance.base_seed` sample, and it is the one whose
  irreducibility (ANH-9)(ii) asserts and (ANH-9)(iii) consumes.

Both land inside the pencil-configuration variety of `G′`; neither is
*a priori* inside the other. So "the grid point is a chart point" in (GR-5)'s
sense does **not** license "(ANH-9)(iii) applies to it": the semicontinuity step
needs the witness on the **irreducible variety whose generic point defines
`M_pen^gen`**, and a witness on a different component of the configuration
variety would make the step void. **That is the clause (FR-4)'s named gap did
not name, and it is the one this step supplies.**

**The chart, made precise.** For `Γ` loopless with `hcard`, min degree 2 and
girth `≥ 3`, define the tower

1. `U_H ⊆ (𝔸³)^{H(Γ)}` — hub points, restricted to the open locus where at
   every hub `h` the `1 + d_h` points `{p_h} ∪ {p_u : u a hub neighbour of h}`
   are affinely independent (equivalently: their homogeneous lifts have rank
   `1 + d_h`);
2. `N → U_H` — fibre at `h` the punctured linear space
   `{n_h ≠ 0 : ⟨n_h, p_u − p_h⟩ = 0 ∀ hub neighbours u}`, of dimension
   `3 − d_h` **constantly on `U_H`**;
3. `N° ⊆ N` — the open locus where at every non-hub `s` with `e_s = 2` the two
   hub-neighbour panels meet in an **affine** line, i.e. their affine normals
   are independent (`widened.meet_line`'s nonzero-direction test);
4. `𝒫 → N°` — fibre at `s` the intersection of `s`'s `e_s` hub-neighbour
   panels, an affine subspace of dimension `3 − e_s`, constant on `N°`;

and `Φ : 𝒫 → (𝔸³)^{V(Γ)}` forgetting the normals, `Chart(Γ) := \overline{Φ(𝒫)}`.
Each stage is a Zariski-locally-trivial bundle of **constant** fibre dimension
over the previous, and `U_H` is a nonempty open subset of an affine space, so
`𝒫` is irreducible and rational over `ℚ`, `Φ(𝒫)` is irreducible and contains a
dense open of `Chart(Γ)`, and `Chart(Γ)` is irreducible. `hcard` is what makes
step 2 work at all (`d_h ≤ 2`, so the normal space is never `0`;
`place_pencil_general` returns `None` on `d_h ≥ 3` for exactly that reason).
**The restriction to `U_H` and `N°` is not decoration** — it is what makes the
fibre dimensions constant, hence what makes (ANH-9)(ii)'s phrase "the image of
an irreducible rational parametrization" literally true. This is the reading
this section uses, and the only one under which that phrase holds.

> **(FR-16)** *(proven-informally; its hypothesis is exactly (GR-5)'s LI clause,
> asserted per body at every one of the 30 built points by `framedom.py
> --transport` and equivalent, at injective ruling parameters, to
> `framedom.legality_free`)* Let `Γ` be loopless with `hcard`, min degree `2`
> and girth `≥ 3`, and let `pt : V(Γ) → P³` be a **σ-fixed** pencil
> configuration — every body isotropic, adjacent bodies conjugate — such that
>
> (i) all bodies are pairwise distinct as projective points and none is at
> infinity, and
> (ii) at every body `u`, `{pt_w : w ∈ closedHubNbhd_Γ(u)}` is linearly
> independent.
>
> Then `pt` lies in `Φ(𝒫)` — the **image** of the (ANH-9)(ii) parametrization at
> its generic-fibre locus, not merely in its closure — hence on the irreducible
> chart `Chart(Γ)` whose generic point defines `M_pen^gen`.
>
> *(Of the three standing hypotheses on `Γ` only **`hcard`** is used in the
> proof — it is what makes `d_h ≤ 2`, hence what makes the normal fibre of
> *Step FR13* stage 2 nonzero and `place_pencil_general`'s `return None` branch
> at three independent hub neighbours unreachable. Min degree 2 and girth `≥ 3`
> are carried because they are what makes the harness's degree bookkeeping
> (`neighbors`, `hn`) agree with the tower — a loop or a parallel pair at a
> degree-2 body would be counted once, not twice. Both hold at `G′` by
> *Step FR12*'s last table row. The affinity clause in (i) is likewise not a
> restriction: *Step FR14*'s parameter recipe supplies it outright.)*

*Proof.* Identify `(P³)^*` with `P³` by `⟨·,·⟩` and set `n_h := pt_h` at every
hub.

*(a) It is an incidence point.* `⟨n_h, pt_h⟩ = ⟨pt_h, pt_h⟩ = 0` is isotropy,
and `⟨n_h, pt_u⟩ = ⟨pt_h, pt_u⟩ = 0` for every neighbour `u` of `h` — hub or
not — is conjugacy. So each hub's whole closed star lies on the plane `n_h`.

*(b) The hub points lie in `U_H`.* At a hub `h`,
`{p_h} ∪ {p_u : u a hub neighbour}` **is** `{pt_w : w ∈ closedHubNbhd_Γ(h)}`,
because `closedHubNbhd` of a hub is that hub together with its hub neighbours
and nothing else. Hypothesis (ii) makes it linearly independent as homogeneous
`4`-vectors, i.e. of rank `1 + d_h`, which for affine points is exactly affine
independence — `U_H`'s condition.

*(c) The normal lies in the fibre, and the fibre has its generic dimension.*
`n_h = pt_h` satisfies the defining conditions by (a); and the fibre's dimension
is `3 − d_h` — its generic value — **precisely** because the rank in (b) is
`1 + d_h`.

*(d) `N°`.* At a non-hub `s` with `e_s = 2` and hub neighbours `h₁, h₂`,
`{n_{h₁}, n_{h₂}} = {pt_w : w ∈ closedHubNbhd_Γ(s)}` — `closedHubNbhd` of a
non-hub is exactly its hub neighbours — independent by (ii), so the two panels
are **projectively** distinct planes; (f) upgrades that to `N°`'s affine form.

*(e) The interior points lie in their fibres.* `⟨pt_s, n_{h_i}⟩ = ⟨pt_s,
pt_{h_i}⟩ = 0` is conjugacy again, for each hub neighbour `h_i` of `s`; for
`e_s ≤ 1` the fibre is a plane or all of space and there is nothing to check.

*(f) The one place the affine model needs a word.* At `e_s = 2` two **distinct**
planes of `P³` always meet in a line, but two distinct *affine* planes of `𝔸³`
meet in a line only when their affine normals are independent — otherwise the
projective meet is the line at infinity and `widened.meet_line` returns a zero
direction. Here that cannot happen: `pt_s` lies on the meet by (e) and is an
affine point by (i), so the meet is not the line at infinity and the affine
normals are independent. **The no-body-at-infinity clause is exactly what
discharges this**, which is why it is stated rather than waved at.

So `pt = Φ(x)` for the explicit point `x = ((p_h), (n_h), (p_s)) ∈ 𝒫`. ∎

**The sentence to carry away.** The points-first parametrization asks for *two*
independent open conditions — hub points in general position along `Λ` (so the
panel normal is determined) and panel normals pairwise distinct at every
two-hub-neighbour interior (so the meets are lines). At a σ-fixed configuration
the normals **are** the points, so those two conditions are literally the same
condition, and it is the **single** clause
`{pt_w : w ∈ closedHubNbhd(u)}` LI (the affine/projective seam of (f) being the
only bookkeeping left) — which is (GR-5)'s own hypothesis,
`framedom.legality_free`'s clauses (i)+(ii) together, and the exact rank
equality `--transport` asserts at every body of every built point. **The
transport therefore costs nothing beyond what the driver already tests — but it
is a different theorem from (FR-15), and stating only (FR-15) would have left
the consumer's step unlicensed.**

**Three riders, named so they are not silently assumed.**

- **The guard is irrelevant here, and must be.** §(K-clos) (AC-9) says a
  σ-fixed point never passes `repin.star_generic`. That is not an obstruction:
  the guard cuts out a **dense open** subset of `Chart(Γ)` (nonempty at the
  pooled shapes by (ANH-10)'s 26/26 guard-accepted seeds), so it does not change
  the generic point, and (FR-16) + (ANH-9)(iii) never evaluate it. This is
  §(K-frame) (FR-4)'s "rank lower semicontinuity on the irreducible chart, never
  a genericity guard", made explicit at the level of the variety.
- **`ℚ(i)` is harmless, for a reason worth writing once.** `Φ` is defined over
  `ℚ` and `𝒫` is `ℚ`-rational, and the frame determinant is a `ℤ`-coefficient
  polynomial in the placement; so a nonzero value at any `ℚ(i)`-point of `𝒫`
  makes the pullback a nonzero element of `ℚ[𝒫]`, nonvanishing on a dense open,
  and (ANH-9)(iii)'s own `ℚ`-density argument then supplies rational points.
- **The tower's stated girth `≥ 3` is one clause short of nonemptiness — a
  correction, not a hole in this theorem** (§(K-chart) (CH-5), direction CIRR,
  2026-08-19). At girth 3 a Λ-triangle carrying a non-hub on two of its hubs
  makes stage 3 (`N°`) empty at *every* seed, so *Step FR13*'s tower is
  vacuous there; girth `≥ 4` restores nonemptiness. This costs (FR-16) nothing
  — its witness `pt` already exists, so nonemptiness at that `Γ` is not in
  question — and it costs no consumer anything, because girth ≥ 4 is free at
  `G′` three independent ways: this section's own last table row
  (girth `(G′) ≥ 6`), the class predicate `gridcol.class_shape`'s two-hub-
  triangle filter, and the landed `not_pencilNondegFeasible_of_triangle_
  two_hubs` (`Motive.lean:563`).

**Reach.** (FR-16) hypothesizes nothing about the bare-cycle stratum, nothing
about `k`, and nothing about tightness — only `hcard`, min degree 2, girth `≥ 3`
and the two legality clauses. So it certifies **every** σ-fixed grid witness
this arc has built on a legality-clean colouring as an honest point of that
graph's (ANH-9)(ii) chart. In particular it applies verbatim to §(K-frame)
(FR-6)'s θ(3,4,5) points (`--outer` skips illegal colourings and runs
`config_asserts` + `verify_pencil_witness` on the rest), which is exactly the
content "the first **constructed**, non-sampled inhabitants of that locus" was
asserting and had not licensed.

### Step FR14 — (FR-17): (FR-4) with no named gap, and the unconditional discharge on the whole bare-cycle stratum

> **(FR-17)** *(proven-informally, **no named gap**; a composite whose standing
> is its weakest link — see the *Confidence verdict*)* Let `G` be a `k = 4`
> class shape, `v` an eligible split, `P` a length-4 companion of `(b, c)` and
> `β` a branch with `H/P − β` a bare 6-cycle — i.e. a **bare-cycle site**. Then
> the §(K-ann) **(ANH-R1) `β`-clause holds at that site**: `H/P − β` is
> independent at the generic pencil placement of `G′`. This holds at **every**
> bare-cycle site of **every** `k = 4` class triple — all **76** class-level
> sites over the stratum's **22** isomorphism classes ((FR-8)/(FR-14)), i.e.
> 1904 of the pinned pool's labelled instances — with **no residual hypothesis
> and no named gap**.

*Proof.* Six steps, each at its own standing.

1. **A pattern colouring exists** — (FR-R1), **PROVEN** (*Step FR10*): (FR-11)'s
   recipe meets (FR-4)'s (pattern) clause and legality (ii) uniformly, (FR-12)
   makes legality (i) vacuous, and independently the finite stratum is
   enumerated with a pattern colouring exhibited at all 1976 labelled sites.
2. **The grid point exists, by formula.** Assign the `A`-components and the
   `B`-components any injective families of **positive** rationals. Then
   `pt_w = grid_point((1, s_w), (1, u_w)) = [1 + s_w u_w,\ −i(1 − s_w u_w),\
   u_w − s_w,\ −i(u_w + s_w)]`, whose last coordinate is nonzero (both
   parameters positive), so **no body is at infinity**; and two bodies coincide
   iff they share both ruling parameters, iff they share both components, which
   legality (i) forbids. Isotropy and conjugacy are (AC-2). So the exact `ℚ(i)`
   witness is **constructed, not searched** — `framedom.build_at`'s seeded retry
   loop is a convenience, not a step.
3. **`C ≠ 0` at the frame image** — (FR-3)(ii): at a σ-fixed grid configuration
   the `6 × 6` hinge-line determinant of the site's six frame edges is nonzero
   **iff** they are coloured 3–3 with pairwise-distinct components per family,
   which is exactly the (pattern) clause; the identity
   `det = 128·Vdm(s)·Vdm(u)` over the function field is `framedom.m2` (FR-M1),
   and both directions are asserted at every built site with a negative control
   (`--transport`, 30/30). (ANH-14)(d)'s `det(Gram) = −C²` identifies that
   determinant with (ANH-14)'s universal polynomial `C` up to sign, and
   (FR-9)(b) settles that on this stratum the governing object is always
   (ANH-14)(a)'s open 7-point chain, never (e)'s closed hexagon.
4. **The grid point is on the irreducible chart of the triple** — **(FR-16)**,
   whose hypotheses are supplied by step 2 (distinctness) and legality (ii)
   (the closed-hub-neighbourhood LI), with `hcard` at `G′` free by (FR-15)'s
   first table row. *This is the step (FR-4) had to name as a gap.*
5. **Semicontinuity** — (FR-1) with `X = Chart(G′)` (irreducible, *Step FR13*),
   `f` the morphism reading the six frame hinge lines off the placement (all six
   frame edges are `H`-edges of `G′` by (FR-9)(b), so `f` is polynomial in the
   placement), `D = {C = 0}`: one point off `D` forces `C ≢ 0` on `X`, hence
   `C ≠ 0` on a dense open of `X`, hence at its generic point.
6. **The generic point is the pencil placement** — (ANH-9)(ii) defines
   `M_pen^gen` there, and (ANH-9)(iii) reads `C ≠ 0` at the generic point as
   `E(H/P) − β` independent in `M_pen^gen`, which is (ANH-R1)'s `β`-clause at
   the site. ∎

**"Unconditional" — say exactly what it means, because the word is doing
work.**

- **What is closed.** No clause of the argument is left unwritten. (FR-4)'s
  "true-modulo-named-gap" becomes **(FR-17)**, plain. In particular the
  1904/1904 pattern battery and the 30/30 exact certificates stop being the
  *evidence* for the stratum and become *instances of a theorem*; (FR-5)'s
  boundedness caveat was already dissolved by (FR-8)/(FR-14), so nothing hedges
  the quantifier "every class triple" either.
- **What its standing is.** **proven-informally**, the arc's ordinary tier —
  the weakest links being (ANH-14)(c)'s irreducibility argument,
  (ANH-9)(ii)/(iii), (FR-1) and (FR-16), none of which is Lean-checked and all
  of which are standard-but-informal algebraic geometry. "No named gap" is not
  "machine-verified"; the two are independent axes and this block moves only the
  first.
- **What it does *not* reach.** (a) The **other ~70 %** of §(K-ann)'s
  length-5-branch sites: 1904 of 6426 pool instances are bare-cycle, and
  (FR-9)(a) — `H/P` is exactly a bare 6-cycle plus `β` — fails immediately at
  `c′ ≥ 2`, so neither (FR-3)'s `6 × 6` reduction nor (FR-11)'s recipe has an
  analogue there. (b) The **(OC-16) side**: (FR-16) certifies (FR-6)'s
  constructed points as chart points and changes nothing else; the strict
  availability package stays 0/8 with (AC-9) the named mechanism, and the
  irreducibility of the hard-stratum target-rank locus stays un-owned ((FR-7))
  — **struck as unnecessary since 2026-08-19 (direction OCON)**: §(K-out)
  (OC-17) shows this locus is open in the whole chart, so its irreducibility
  is the chart's, owned by (ANH-9)(ii); see Step FR6.
  (c) **`hK`**: (ANH-R1) is one input of one route; discharging it on one
  stratum of one `k` moves no gap-map status, and §(K-grid) (GR-15) is
  untouched.

### Step FR15 — the scope line: what this block does NOT say

Four sentences, so no later reader has to reconstruct them.

- **It does not touch class uniformity.** `hK`'s status is exactly what it was.
  Nothing here is a flank against §(K-grid) (GR-15), and nothing here bears on
  the `g`-detector, the balance layer, or route-ledger entry 5.
- **It does not re-open the `≤3`-closedHubNbhd line.** *Steps FR7–FR11*'s
  §"The (`≤3`-closedHubNbhd) line" applies verbatim and its reasoning is
  unchanged: (FR-16) quantifies over **one constructed configuration** and
  concludes about a **point** of a variety; it never says "the combinatorial
  criterion holds, therefore the graph is `PencilNondegFeasible`". The one place
  feasibility appears is the *opposite* direction — `hK`'s hypothesis
  `HasGenericPencilRealization K 3 G′` **supplying** `hcard` at `G′` — which is
  a hypothesis being consumed, not a criterion being propagated.
- **It does not develop the (FR-6) follow-ons.** Items (ii) (the
  `ℓ_min = 5` / `deg_H(h) = 2` battery beyond θ(3,4,5)), (iii) (the (FR-7)
  irreducibility foothold) and (iv) (the structural account of the on-stratum ⟺
  coincidence-pair anti-correlation) of *Steps FR0–FR6*'s *What would change
  this* are **untouched and remain un-commissioned**. (FR-16) makes item (iii)
  marginally cheaper to state — the foothold's "irreducible rational family" is
  the colouring's grid family, and *Step FR13*'s tower is the ambient it sits in
  — but running it is a separate commission.
- **It does not move any gap-map *status*.** The (K-frame) row's *what would
  close it* cell changes ("(FR-4)'s named gap alone" → "closed; (FR-17)"), and
  the (K-ann) row's §(K-frame) clause loses its rider. Both are wording, not
  status.

### Verdict — what this buys, exactly

- **§(K-frame) (FR-4): the named gap is CLOSED.** (FR-15) is the restatement as
  named; (FR-16) is the clause the name did not carry and is what the consumer
  actually needed. (FR-4) may be re-read as **(FR-17)**: proven-informally, no
  named gap.
- **§(K-ann) (ANH-14) / the (K-ann) gap-map cell**: the chart-to-frame residue
  on the bare-cycle stratum is now discharged **with no rider at all**. The
  row's §(K-frame) clause should drop "what remains is (FR-4)'s one named gap
  alone" and say "closed as an argument, no rider (§(K-frame) (FR-17))".
  **Status does not move**: (ANH-R1) at the other ~70 % of length-5-branch
  sites, and class uniformity, are exactly where they were.
- **§(K-grid) (GR-5) / *Step G6***: gains a companion, not a correction. (GR-5)
  is untouched and true as landed; what this block adds is that its LI
  hypothesis has a **second** meaning nobody had drawn — at a σ-fixed
  configuration it is precisely the (ANH-9)(ii) parametrization's genericity
  locus — and that the (GR-5) statement alone is a chart-**map** fact, not a
  chart-**variety** fact.
- **§(K-ann) (ANH-9)(ii)**: gains a precise reading. Its "irreducible rational
  parametrization" is literally true of the tower of *Step FR13*, i.e. of
  `place_pencil_general` **restricted to its constant-fibre-dimension locus**;
  without that restriction the fibres jump and the phrase is not a
  parametrization. Recording this costs nothing and removes a latent ambiguity
  that this direction had to resolve before it could proceed.
- **§(K-frame) (FR-6)**: retro-certified. Its four on-stratum θ(3,4,5)
  colourings are honest points of θ(3,4,5)'s `G′`-chart by (FR-16); the
  section's "first constructed, non-sampled inhabitants of that locus" now has
  its licence. **No other (OC-16)-side statement moves.**

### Verification

**No driver was run, and no driver was written.** The reserved
`notes/scripts/w4/fres.py` is **returned unused**, and the file does not exist.
The reason is structural, not budgetary: every hypothesis this block consumes at
an instance is *already* asserted by the landed `framedom.py`, and everything on
top of those hypotheses is proof, which no driver mode can test (F11). Nothing
existing is modified (`git diff --name-only -- '*.py' '*.m2'` empty), so the
figure-invariance gate discharges on that check alone, and no new invocation row
is owed to `notes/scripts/README.md` §3.

The landed runs each claim rests on, per driver and mode
(§(K-frame) *Steps FR0–FR6* and *Steps FR7–FR11* *Verification*; re-runnable
from the repo root):

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --pattern    # 13 s  1904/1904; `hcard_ok(G')`/`is_2ec(G')` at 1540 site-carrying splits, 0 failures
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --transport  # 25 s  30/30 exact certificates: distinctness, isotropy/conjugacy, the per-body closedHubNbhd RANK equality, `verify_pencil_witness`, `C != 0` two routes, negative controls
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --outer      #  5 s  the theta(3,4,5) table (FR-16)'s reach clause cites
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --rulings    #  2 s  (FR-2)/(FR-3) measured
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --strat      #  3 s  the COMPLETE stratum, 1976/1976 (FR-R1)
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recipe     # 12 s  (FR-11) constructed, first variant
M2 --script notes/scripts/m2/framedom.m2                           #  1 s  (FR-M1) `det = 128*Vdm(s)*Vdm(u)`
```

**Source facts read off the landed definitions, not their docstrings** (the
CLAUDE.md "docstrings are not evidence" clause; each was opened this pass):

| fact | where | what was read |
|---|---|---|
| `closedHubNbhd u = {w : PencilHub w ∧ (w = u ∨ w ∼ u)}` | `Molecule/Pencil/Motive.lean:82` | the **definition body** — hence "hub ⟹ `{u} ∪` hub neighbours; non-hub ⟹ hub neighbours", the identity *Step FR13* (b)/(d) turns on |
| `hcard` at `G′` is `hK`'s own hypothesis | `Molecule/Pencil/Escape.lean`, the `hK` slot of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` | `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` → `IsNondegPencilRealization G′ …` (`Motive.lean:140`) → `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) |
| the chart map reads hub normals only | `Molecule/Pencil/Chart.lean:393,412` (`pencilChartPoint`, `pencilChartNormal`) + `Engine.lean:89` (`PencilSeed.ofCoord`, `fillNbr := fillHub`) | the normals-first direction of (GR-5), and that the `fillNbr` coupling is vacuous exactly when `nbrSel` fills all three slots |
| the (ANH-9)(ii) parametrization is points-first | `notes/scripts/w4/widened.py:160` (`place_pencil_general`) | hub points sampled free; `nrm[h]` from `nullspace` of the **hub**-neighbour differences; non-hubs on `meet_line` / `in_plane_point` / free; `return None` at three independent hub neighbours (unreachable under `hcard`) |
| the chart is `G′`'s, not `G`'s | `notes/scripts/w4/outer.py:242` (`chart_point`), `dominance.py:547` (`base_seed`), `repin.py:225` (`seed_probe`) | all three call `place_pencil_general(Gp, …)` with `Gp = G − v + ab` |
| the legality clauses are the LI clause | `notes/scripts/w4/framedom.py:176` (`legality_free`), `:433` (`site_certificate`) | `legality_free` = pairs injective + no 3-member `closedHubNbhd` mono-component; `site_certificate` additionally asserts `rank([pt[w] for w in S]) == len(S)` at **every** body |
| admissibility = alternation at degree-2 bodies | `notes/scripts/w4/closure.py:254` (`alternation_classes`) | the constraint graph links the two edges at a degree-2 body only — nothing else |
| the grid map is Segre ∘ (linear iso) | `notes/scripts/w4/closure.py:160` (`grid_point`) | bilinear in `(s:t)`, `(u:v)` with invertible coefficient matrix — the step *Step FR12*'s star-rank-3 row uses |

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (FR-15) | — | **proof-level**: a hypothesis-transport theorem. Its *transported hypotheses* are asserted per instance — `hcard_ok(G′)`/`is_2ec(G′)` by `--pattern` (0 failures at 1540 splits), distinctness + isotropy/conjugacy + the per-body `closedHubNbhd` rank equality by `--transport` (30 points) |
| (FR-15)'s dropped clause | — | **proof-level, negative**: `f(V(G′)) = f(V(G)) + 1` is arithmetic; nothing measures it because nothing claims it |
| (FR-16) | — | **proof-level**; its hypothesis is `--transport`'s per-body rank assertion, and `--outer`'s `legality_free` filter for the θ(3,4,5) reach clause. **No driver can test the conclusion** (membership in a variety's parametrized image is not a finite check) |
| (FR-16)'s guard rider | `--transport` (indirectly) | that the argument never evaluates `repin.star_generic` — `site_certificate` does not call it, by design; §(K-clos) (AC-9) is why it must not |
| (FR-17) step 1 | `patexist.py --strat`, `--recipe` | (FR-R1) exhaustively at 1976/1976 |
| (FR-17) step 2 | — | **proof-level** (an explicit parameter recipe). `--transport`'s seeded `build_at` is the same object built by search; the recipe removes the search |
| (FR-17) step 3 | `framedom.m2` (FR-M1), `--rulings`, `--transport` | the function-field identity; both directions of the criterion at 30 built sites with negative controls |
| (FR-17) steps 4–6 | — | **proof-level**: (FR-16) + (FR-1) + (ANH-9)(ii)/(iii). Semicontinuity on an irreducible variety is not a driver-testable sentence |
| (FR-17)'s reach | `patexist.py --strat`, `--recon` | 22 iso classes / 76 class-level sites / 1976 labelled — the quantifier "every class triple" is the enumeration, not a sample |
| the 30 % / 70 % split | `anhr1.py --size` (landed) | 1904 of 6426 length-5-branch **pool instances**; a pool ratio, per (FR-14)(iii) |

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(FR-15)** | (GR-5) restates at `G′` verbatim, minus its target-rank clause; `hcard`, star-rank-3 and the 3-member-`closedNbhd` clause all come out free | **proven-informally**, at exactly (GR-5)'s own standing (the transported hypotheses are additionally asserted per instance) |
| **(FR-16)** | a legality-clean σ-fixed grid configuration of an `hcard` graph lies in the **image** of the (ANH-9)(ii) parametrization at its generic-fibre locus; at σ-fixity the points-first and normals-first genericity loci coincide, and both are the `closedHubNbhd` LI clause | **proven-informally** (bundle-tower irreducibility + explicit membership; no driver can test the conclusion, its hypothesis is what `--transport` asserts) |
| **(FR-17)** | the (ANH-R1) `β`-clause at **every** bare-cycle site of **every** `k = 4` class triple — 76 class-level sites, 22 iso classes | **proven-informally, NO named gap** — a composite of (FR-R1) (PROVEN), (FR-3) (proven-informally), (FR-16), (ANH-14) (proven-informally), (ANH-9)(ii)/(iii) (proven-informally) and (FR-1) (proven-informally, standard) |
| the (ANH-9)(ii) reading | the chart is the image of `place_pencil_general` **restricted to its constant-fibre-dimension locus**; without that restriction it is not a parametrization | **proven-informally** (fibre-dimension bookkeeping); recorded because the direction had to fix it before proceeding |
| the (FR-6) retro-certification | θ(3,4,5)'s four on-stratum colourings are honest `G′`-chart points | **proven-informally** ((FR-16) applied; `--outer` supplies the hypotheses per colouring) |

**Class uniformity of `hK` is untouched. No gap-map *status* moves.**

### What would change this

*(i)* **The natural successor is the `c′ ≥ 2` strata, and nothing here is a
head start on them.** (FR-17) is a bare-cycle theorem end to end: (FR-9)(a)
gives `H/P = ` bare 6-cycle `∪ β`, (FR-3) reduces the pure condition to a
`6 × 6` colouring pattern, and (FR-11) builds the colouring. At `c′ = 2`
(3846 pool instances, the largest stratum) the pure condition is (ANH-13)'s
`6m × 6m` branch-screw determinant and none of the three survives. **(FR-16),
however, transfers unchanged** — it is a statement about σ-fixed configurations
of any `hcard` graph — so a `c′ ≥ 2` attack would inherit the chart-membership
half for free and owe only the determinant half.

*(ii)* **A Lean pin, if a later pass wants the tier moved.** The objects exist
(`Chart.lean`, `Engine.lean`, `Motive.lean`), and (FR-15) is the statement a
compiler spike would formalize; (FR-16) is not — it is algebraic geometry over a
variety the Lean side does not carry. So the honest reading is that (FR-15) is
Lean-pinnable and (FR-17) is not, and that closing the *named gap* is a
different achievement from moving the *tier*. This is the same distinction the
(FR-4) → (FR-17) move makes, and it should not be blurred.

*(iii)* **A `--chartmem` reconstruction mode would add rhetoric, not
evidence.** One could write a driver that, at each built point, recovers the
`place_pencil_general` parameters (hub points; `nullspace` of the hub-neighbour
differences; `meet_line` for each two-hub-neighbour interior) and re-runs the
parametrization to reproduce the grid exactly. It would assert **nothing**
`--transport` does not already assert: the reconstruction succeeds *iff* the
per-body `closedHubNbhd` rank equality holds, which is the assertion already in
`site_certificate`. Written down here so a later pass does not spend a dispatch
rediscovering that.

*(iv)* **A refutation would have to attack (FR-16), and the shape it would
take is worth naming.** The claim is that σ-fixity collapses two genericity
conditions into one. It would fail if the (ANH-9)(ii) parametrization needed a
condition **not** expressible in `closedHubNbhd` terms — e.g. if
`place_pencil_general` constrained a panel normal by a *non-hub* neighbour
(it does not: `widened.py:183` filters `if u in hubset`), or if a body could
have three hub neighbours (`hcard` forbids it, and the code's `return None`
branch is unreachable for that reason). Those two source facts are the whole
load-bearing surface; both were read this pass and both are recorded in
*Verification*.

*(v)* **The (FR-6) follow-ons stay open and un-commissioned**, unchanged by
this block: the `deg_H(h) = 2` battery beyond θ(3,4,5), the (FR-7)
irreducibility foothold, and the structural account of the on-stratum ⟺
coincidence-pair anti-correlation. The only thing that moved for them is that
(FR-16) licenses their σ-fixed witnesses as chart points, which the foothold
((iii)) in particular was implicitly assuming.
