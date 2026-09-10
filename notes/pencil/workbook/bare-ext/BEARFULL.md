## §(K-bare-ext) — continuation (direction BEARFULL): the merge inequality's **real theorem** is a **SHORT-CYCLE LAW** — every cycle of length `≤ 6` forces `δ = 0`, which **contains** (BE-32)(ii)/(iii) and proves (BE-32)(+) at **196 043 of 203 723** forced pairs; **(b2) is a COROLLARY of (b1)** by one line of Grassmann, so the ear case's (β) side loses a clause; and the **EAR-DECOMPOSITION route is REFUTED as a replacement for the internal R-node** — a one-line theorem shows every minimum-degree-`≥ 3` graph forces a single-edge ear

Direction **BEARFULL** (`notes/Pencil-fanout.md` §"BEARFULL", ordinal 47), the
arc's fifty-fifth and the **fourth** consecutive whose primary jobs were forced:
BEARCASE closed **(α)** and left the (β) side with exactly two items — **(1)**
(BE-32)(+) as a theorem and **(2)** (b2) for a general piece — plus a
coordinator-raised **routing question** that lifts BTWOCUT's own S-all/S-mark
bar for that job only. Read against *Steps BE34–BE37* (BEARCASE), *Steps
BE29–BE33* (BIMAGE), *Steps BE24–BE28* (BTWOCUT), *Steps BE19–BE23* (BINDUC)
and *Steps BE14–BE18* (BZAVOID), whose figures are **cited, never re-run**.
Driver `notes/scripts/w4/bearfull.py`
(`merge|cycles|forced|chain|bgrass|eardec|chord|validate`), importing
`bearcase`, and through it `bimage` / `btwocut` / `binduc` / `bzavoid` /
`kbare_common`, **read-only**; all exact ℚ, every rng seeded and printed.

**Status, stated before the mathematics.**

- **The merge inequality proves far more than it has been asked for, and the
  extra is two LATTICE laws.** For an optimal partition `P`, merging *any* set
  `S` of parts is a competitor, so **`5 e_Q(S) ≤ 6(|S|−1)` for EVERY `S`** —
  the quotient multigraph `Q` on the parts is **simple** (`|S| = 2`) and has
  **girth `≥ 6`** (`|S| = 3, 4, 5` forbid a triangle, a 4-cycle and a 5-cycle),
  with a 6-cycle allowed but **TIGHT**. And the partition weight
  `g(P) = 5 e_in(P) + 6|P| − 6n` is **supermodular** on the partition lattice,
  so the **join of two optimal partitions is optimal**: there is a unique
  **coarsest** optimal partition `P_max`, and **`δ_uv = 0 ⟺ u, v` lie in one
  block of `P_max`** — which makes *"`δ = 0`"* an **EQUIVALENCE RELATION**.
  **(BE-39)(i)/(ii)**.
- **Hence the SHORT-CYCLE LAW, and it is the theorem (BE-32)(ii)/(iii) were
  two instances of.** The crossing edges of a cycle `C` form a closed walk in
  `Q` with **distinct** edges, hence an even subgraph, hence contain a
  `Q`-cycle of length `≥ 6`. So the number of crossings is `0` or `≥ 6`:
  **every cycle of length `≤ 5` lies inside a single part of every optimal
  partition**, and a 6-cycle either does or splits into **six** parts forming a
  **tight** set whose merge is again optimal. Either way
  **`δ_xy = 0` for any `x, y` on a common cycle of length `≤ 6`**, and in
  general **`δ_xy ≤ max(0, L − 6)`** on a common `L`-cycle — which beats
  (BE-32)(iv)'s `δ ≤ dist` for every `L ≤ 11`. **(BE-32)(ii) is `L = 3`;
  (BE-32)(iii) is `L = 4` and its hypothesis WEAKENS from `≥ 3` common
  neighbours to `≥ 2`.** **(BE-40)**.
- **(BE-32)(+) is thereby PROVED at 196 043 of 203 723 aggressively-forced
  pairs, and REDUCED to a statement with no geometry in it.** Every forcing
  step whose three points put **two in one closed star** puts the admitted hub
  on a triangle or a 4-cycle with that star's centre — **401 489 of 401 544
  steps**, and the **first** step is *always* of that shape, which is exactly
  why (BE-32)(ii)/(iii) are the base case. What is left is *"every
  aggressively-forced pair is `≤6`-cycle-class connected"* — **measured at
  203 723 pairs with zero escapes**, and the residue is the **SPREAD** step, at
  **55** of 401 544. **(BE-41)**.
- **The proof's boundary is LOCATED, and it is exactly where the merge
  inequality runs out of slack.** A 6-cycle of `Q` is tight and a 7-cycle is
  not (`5·7 = 35 < 36`), so (BE-40) cannot reach past 6 — and a **named
  triangle-chain family** produces forcing steps whose shortest cycle is
  `7, 8, …`, escaping the certificate. **`δ = 0` at every member anyway**, and
  a blind hunt in the non-vacuous band (`def₃ > 0`) over **27 414** forced
  pairs finds **zero** escapes and **zero** `δ ≠ 0`. **(BE-41)(iii)**.
- **(b2) IS A COROLLARY OF (b1), by one line of Grassmann — job 2's clause
  stops being independent.** `Π_u ⊆ Z`, so for any subspace `X`
  **`dim(X ∩ Z) ≤ dim Z − 2 + dim(X ∩ Π_u)`**, and the same at `v`. Hence
  **(b1) ⟹ (b2) outright whenever `δ₁ ≥ 5`**, and `ρ̄₁ ∩ Π_u = 0` at **either**
  end gives (b2) at **every** `δ₁`. The only pieces needing more are those with
  `dim(ρ̄₁ ∩ Π_u) ≥ 1` at **both** ends and `δ₁ ≤ 4` — the **series** shape at
  both ends, where (BE-38)(i) settles the all-S piece and the SPQR peel is the
  stated route for the rest. Measured on bearcase's free sampler
  **extended to `dist_{G₁}(u,v) ≥ 5`**, which is precisely what (BE-38)(ii)'s
  transfer does not reach: **19 pieces, 0 failures**, the bound holding as an
  exact inequality at every draw and **tight at 144** of them. **(BE-42)**.
- **THE ROUTING VERDICT IS *NO*, and it is a theorem rather than a
  preference.** In a **chord-free** open ear decomposition the **last** ear has
  length `≥ 2` and receives no later attachment, so its interior vertices have
  degree **exactly 2** in `G`; if there is no ear at all, `G` is a cycle. So
  **`G` chord-free-ear-decomposable ⟹ `G` has a degree-2 vertex** —
  contrapositively **every graph of minimum degree `≥ 3`, i.e. every 3-connected
  block, i.e. every R-NODE, forces a single-edge ear in EVERY open ear
  decomposition.** Swept: **2 084 3-connected graphs, ZERO chord-free**;
  6 968 of 12 620 2-connected graphs chord-free, **every one** of them with a
  degree-2 vertex. And the single-edge step is **not** soft: it demands
  `p_v ∈ π_u` **and** `p_u ∈ π_v`, which **no** generic point of `Y°(G)`
  satisfies (128 draws, decided exactly, zero), so nothing the induction holds
  at `G` transfers to `G + uv`. **The ear route RELOCATES the R-node
  difficulty; it does not remove it.** **(BE-43)**.
- **S-mark's pin ((BE-25)(ii)) STANDS — and the bar-lift bought one genuinely
  new fact.** The ear route needs a **third** shape, **S-dec**, marked by the
  decomposition: strictly **weaker** than S-all (finitely many pairs, named in
  advance) and not S-mark. It still meets **cross pairs** ((BE-28)(i)) whenever
  a later ear attaches at an earlier ear's interior, and avoiding that
  **requires a cycle through every degree-`≥3` vertex** — satisfied by all
  12 620 swept graphs, and **failing** at any subdivision of a non-Hamiltonian
  3-connected base, of which **Petersen** is the smallest (non-Hamiltonicity
  decided by exhaustive search). **Both gaps localise at the same place: the
  R-node.**
- **Verdict: (BE-14) OPEN and unchanged in status. HIT shape 3 (a routing
  verdict that re-ranks the board, and it is a clean NO) carrying shape 2's
  job-2 half (b2 closed as a reduction).** Job 1 moves from **MEASURED** to
  **PROVED at 96.2 % of instances with a 55-step named residue**, but is **not
  closed**. `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G` and the 2-cut
  step are untouched. **Not a PENCIL event.** Classification in **(BE-43)(v)**.
- **Reservation FULLY CONSUMED.** Labels **(BE-39)–(BE-43)** and *Steps
  BE38–BE42*; nothing returned.

### Standing notation

Inherited from *Steps BE9–BE37* verbatim (`f := def₃`, `g_{uv}`, `δ_{uv}`,
`ρ̄_{uv}`, `ρ_{uv}`, hub, `Π_v := p_v ∧ π_v`, `Z := Π_u + Π_v`, `E`, `c₂`,
`loss`, `slack`, the Klein form, the α-plane `S_p`). Added here:

- for a partition `P` of `V(G)`: `d(P)` the number of edges **not** inside a
  part, `e_in(P) = |E| − d(P)`, `value(P) = 6(|P|−1) − 5 d(P)`, and
  `f(W) = 5|E(W)| − 6(|W|−1)` the part weight of `kbare_common`'s part-sum
  identity (`f(∅) = f(singleton) = 0`);
- `Q = Q(P)`, the **quotient multigraph** on the parts of `P`, one edge per
  crossing edge of `G`; `e_Q(S)` the number of `Q`-edges with **both** ends in
  a set `S` of parts;
- a set `S` of parts is **TIGHT** when `5 e_Q(S) = 6(|S|−1)`, i.e. merging it
  leaves the value unchanged;
- `P_max`, the **coarsest optimal partition** ((BE-39)(ii));
- the **`≤L`-cycle class** of a vertex: the union-find classes generated by
  `V(C)` over all cycles `C` of `G` with `|C| ≤ L`;
- the **aggressive plane-class closure** `forced_same_plane` — seed a hub `h`
  with `A := N[h]`, repeatedly admit a hub `v` with `|N[v] ∩ A| ≥ 3` and set
  `A := A ∪ N[v]`; the forced pairs are the pairs inside one `fam(h)`. **This
  is the operator every claim below is proved or measured for**, and it
  **over**-claims forcing (it assumes every three points independent), which is
  the direction that makes an empty sweep the **stronger** statement;
- an **open ear decomposition**: a cycle `C`, then paths whose two endpoints
  are **distinct** vertices of the current graph and whose interior is new; a
  **single-edge ear** (equivalently a **chord**) is such a path of length 1.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read beyond the four BINDUC read (`Graph.partitionDef`,
`Graph.deficiency`, `bodyBarDim`, `SimpleGraph.IsGeneralPositionPlacement`);
the pencil condition is read off `kbare_common.verify_pencil_witness` and
`bimage.plane_at` — *every closed star admits a common normal*, i.e. **every
closed star is coplanar** — and that reading is what (BE-43)(iii) rests on.
**No `.lean` was opened for edit; the standing 2026-08-05 Lean hold binds.**

### Step BE38 — the two partition-lattice laws the merge inequality proves, and which the arc had not extracted

> **(BE-39)(i)** *(proven; **THE QUOTIENT SPARSITY LAW**, and `girth(Q) ≥ 6`)*
> Let `P` be optimal, `Q` its quotient. Then for **every** set `S` of parts
>
> **`5 e_Q(S) ≤ 6(|S| − 1)`.**
>
> *Proof.* Merging `S` into one part is a partition of value
> `value(P) − 6(|S|−1) + 5 e_Q(S)`, which is `≤ value(P) = f` by optimality. ∎
>
> Consequences, read off the `|S|` it is applied at:
> `|S| = 2` gives `e_Q ≤ 1`, so **`Q` is simple** — two parts of an optimal
> partition are joined by at most one edge of `G`, hence a vertex has at most
> **one** neighbour in each part other than its own. `|S| = 3, 4, 5` give
> `e_Q ≤ 2, 3, 4`, forbidding a triangle, a 4-cycle and a 5-cycle of `Q`;
> `|S| = 6` gives `e_Q ≤ 6`, so a 6-cycle is allowed and is **TIGHT**. Hence
> **`girth(Q) ≥ 6`**.
>
> Measured (`bearfull.py merge`): **EXHAUSTIVE over every connected labelled
> graph on `n = 3…6` (27 474 graphs) plus 600 seeded masks at each of
> `n = 7, 8` — 28 572 graphs, 28 633 optimal partitions and 130 331
> **ENUMERATED** subsets of their parts, `0` violations**, of which **61** are
> tight; the girth histogram is `forest: 28 572, 6: 61`, with **zero** entries
> below 6 and **zero** parallel `Q`-edges. The 61 are exactly the 6-cycles'
> finest partitions.

> **(BE-39)(ii)** *(proven; **THE JOIN LEMMA** — `δ = 0` is an equivalence
> relation)* Write `g(P) := Σ_B f(B) = value(P) − (6(n−1) − 5|E|)`, so
> `g(P) = 5 e_in(P) + 6|P| − 6n`. Then `g` is **supermodular** on the partition
> lattice:
>
> - `e_in(P ∨ P′) ≥ e_in(P) + e_in(P′) − e_in(P ∧ P′)`, because an edge inside
>   a `P`-block **or** inside a `P′`-block is inside a join block, and the
>   edges inside **both** are exactly `e_in(P ∧ P′)`;
> - `|P ∨ P′| ≥ |P| + |P′| − |P ∧ P′|`, because the bipartite
>   block-intersection graph has `|P| + |P′|` vertices, `|P ∧ P′|` edges and
>   `|P ∨ P′|` components, and `#components ≥ #vertices − #edges`.
>
> Hence `g(P ∨ P′) ≥ g(P) + g(P′) − g(P ∧ P′)`. If `P, P′` are both optimal,
> the right side is `≥ max + max − max = max`, so **`P ∨ P′` is optimal**. ∎
>
> Therefore the optimal partitions are closed under join and have a unique
> **coarsest** element `P_max`, and
>
> **`δ_uv = 0 ⟺ u` and `v` lie in one block of `P_max`.**
>
> *(⟸)* `P_max` is an optimal partition with `u, v` together, so
> `g_uv ≥ f`, and `g_uv ≤ f` always. *(⟹)* `g_uv = f` means some optimal
> partition has them together; joining it into `P_max` keeps them together. ∎
>
> **This is the tool the whole of (BE-32)(+) needed and did not have:
> *"`δ = 0`" is TRANSITIVE.** (BE-32)(ii)/(iii) prove the stronger *"no optimal
> partition separates them"*, which is transitive for a different and weaker
> reason; the join lemma makes `δ = 0` itself an equivalence relation, which is
> what lets short-cycle certificates **compose**.
>
> Measured: **61 ENUMERATED pairs** of distinct optimal partitions (only 61
> graphs under the cap have more than one optimal partition, and they are the
> 6-cycles), `0` failures; and `δ_uv = 0 ⟺` same block of `P_max` at
> **435 072** pairs, `0` failures.

### Step BE39 — the short-cycle law, which CONTAINS (BE-32)(ii) and (iii)

> **(BE-40)(i)** *(proven; **cycles of length `≤ 5` never split**)* Let `C` be
> a cycle of `G`, `P` an optimal partition, and `r` the number of edges of `C`
> whose ends lie in different parts. Going round `C`, the crossing edges form a
> **closed walk** in `Q`; by (BE-39)(i) no two `G`-edges join the same pair of
> parts, so those `r` `Q`-edges are **distinct**. A non-empty set of distinct
> edges forming a closed walk has every `Q`-vertex of **even** degree, hence
> contains a `Q`-cycle, which by (BE-39)(i) has length `≥ 6`. So
>
> **`r = 0` or `r ≥ 6`.**
>
> For `|C| ≤ 5` the second is impossible, so `r = 0`: **every cycle of length
> `≤ 5` lies inside a single part of every optimal partition.** ∎

> **(BE-40)(ii)** *(proven; the 6-cycle is the TIGHT boundary)* If `|C| = 6`
> and `r > 0` then `r = 6`, so every edge of `C` crosses; and two vertices of
> `C` in one part are impossible — adjacent-but-one puts two `G`-edges between
> the **same** pair of parts, and any other coincidence closes a `Q`-cycle of
> length `< 6`, both forbidden by (BE-39)(i). So `C` meets exactly **six**
> parts carrying **six** `Q`-edges — a **TIGHT** set, whose merge is again optimal by
> (BE-39)(i)'s equality case. Either way **some optimal partition has all of
> `C` in one block**, so by (BE-39)(ii)
>
> **`δ_xy = 0` for any `x, y` on a common cycle of length `≤ 6`**,
>
> and, `δ = 0` being an equivalence relation, for any `x, y` in one
> **`≤6`-cycle class**. ∎

> **(BE-40)(iii)** *(proven; the general bound)* With `r` crossings the walk
> visits at most `r` parts, so merging them gives
> `δ_xy ≤ 6(r−1) − 5r = r − 6 ≤ |C| − 6`:
>
> **`δ_xy ≤ max(0, L − 6)` for `x, y` on a common `L`-cycle**,
>
> which is strictly better than (BE-32)(iv)'s `δ_xy ≤ dist(x,y)` for every
> `L ≤ 11`. ∎

> **(BE-40)(iv)** *(containment, and a genuine weakening of a landed
> hypothesis)* **(BE-32)(ii)** — a common triangle — is `L = 3`.
> **(BE-32)(iii)** — `≥ 3` common neighbours — is `L = 4`, and its hypothesis
> **weakens**: two non-adjacent vertices with **`≥ 2`** common neighbours
> already lie on a 4-cycle, so `δ = 0`. Nothing is refuted; a landed theorem is
> **strengthened**, and both become instances of one statement.
>
> Measured (`bearfull.py cycles`): over the same exhaustive `n = 3…6` census
> plus 400 seeded masks at `n = 7`, **241 771 ENUMERATED `(cycle of length
> ≤ 5, optimal partition)` incidences with `0` violations**; **33 262** 6-cycle
> incidences of which **61** split into six parts forming a tight set and `0`
> violate the dichotomy; **294 500** pairs in a common `≤6`-cycle class, `0`
> with `δ ≠ 0`; **289 000** pairs with a common cycle of length `≤ 8`, `0`
> violating `δ ≤ max(0, L−6)` at the shortest one; and **61 770** non-adjacent
> pairs with `≥ 2` common neighbours — a hypothesis (BE-32)(iii) does **not**
> cover — `0` with `δ ≠ 0`.

### Step BE40 — (BE-32)(+): the closure operator named, the theorem proved at 96.2 % of instances, and the boundary located

> **(BE-41)(i)** *(proven; the **STAR-2 step**, and it contains (BE-32)(ii) and
> (iii) as its base case)* Let the aggressive closure admit a hub `v` on the
> strength of three points `x, y, z ∈ N[v] ∩ A`. Suppose two of them lie in one
> closed star `N[w]` and are **not** the degenerate pair `{v, w}`. Then `v` and
> `w` lie on a common cycle of length `3` or `4`:
>
> - `a, b ∈ N(v) ∩ N(w)` with `a, b ∉ {v, w}` give the 4-cycle
>   `v — a — w — b — v`;
> - `a = v` (so `v ∈ N[w]`, i.e. `v ∼ w`) and `b ∈ N(v) ∩ N(w)` give the
>   triangle `v — w — b — v`.
>
> By (BE-40) `δ_{vw} = 0`, and by (BE-39)(ii) these compose. **The FIRST step
> is always of this shape**: `|N[v] ∩ N[h]| ≥ 3` with `v ≁ h` means `≥ 3` common
> neighbours ((BE-32)(iii)), and with `v ∼ h` it means a common neighbour, i.e.
> a triangle ((BE-32)(ii)). So **(BE-32)(ii)/(iii) are exactly the base case of
> this induction**, and the rest of it is new. ∎
>
> Measured (`bearfull.py forced`): **401 544 forcing steps**, of which
> **401 489** are star-2 — **PROVED** — and **55** are not. Carrying only the
> star-2 links, **196 043 of 203 723** aggressively-forced pairs have `δ = 0`
> **proved with no measurement at all**; the exhaustive `n = 3…6` tier is
> **100 %** proved and every unproved pair is at `n ≥ 7`.

> **(BE-41)(ii)** *(the residue, stated exactly, and it is geometry-free)*
>
> > **CORRECTION, 2026-09-01 (direction BSPREAD, *Steps BE73/BE75* /
> > (BE-74)/(BE-76)) — read this clause with its carve-out, and then read
> > (BE-74).** The displayed sentence below is **FALSE as a universal
> > statement**, and it is refuted by **(BE-41)(iii) immediately after it**:
> > 4 of that family's 8 members carry an aggressively-forced pair whose
> > shortest cycle has length `7` or `8`. The escape is **asserted non-empty**
> > by this direction's own driver (`bearfull.py chain`, and re-derived at
> > `bspread.py chain`), so the measurement line below reports `0` escapes over
> > the **random and enumerated** tiers only — the **constructed** tier
> > escapes **by design**. **(BE-32)(+) was never in danger**: `δ = 0` at
> > every member, and it is now a **theorem** ((BE-74)), proved without any
> > cycle certificate. So this clause is **RETIRED, not repaired**: the
> > `≤6`-cycle class is a **sufficient** certificate for `δ = 0`
> > ((BE-40)) that the aggressive closure can **escape** ((BE-41)(iii)), and
> > (BE-32)(+) does not depend on it.
>
> What is left of (BE-32)(+) is
>
> **every aggressively-forced pair lies in one `≤6`-cycle class**,
>
> a statement about a graph and a union-find, with **no configuration, no
> genericity, no constructor and no closure-operator subtleties** in it. The
> unproved case is the **SPREAD** step: the three points come from three
> different closed stars and no two share one, so no `≤4`-cycle is available at
> `v`.
>
> Measured: **203 723** forced pairs, **`0`** outside a `≤6`-cycle class
> **in the random and enumerated tiers** (the constructed tier of (BE-41)(iii)
> **escapes by design**, and is the counterexample — correction above); and
> at `n ≤ 7`, where `δ` is affordable directly, **144 539** forced pairs with
> **`0`** having `δ ≠ 0`.

> **(BE-41)(iii)** *(the boundary, LOCATED — and it is exactly where the merge
> inequality runs out of slack)* A 6-cycle of `Q` is tight and a 7-cycle is
> not: `5·7 = 35 < 36 = 6·6`. So (BE-40) **cannot** be pushed past 6, and the
> question is whether the aggressive closure can. It can. Let `t₀ … t_k` be a
> path, let `x_i` complete the triangle `(t_i, t_{i+1})` for `i < k`, and let
> `v` be joined to `t₀`, to `x_{k−1}` and to a pendant. The closure admits every
> `t_i` (each shares `{t_i, t_{i−1}, x_{i−1}}` with `A`) and then admits `v` on
> `{v, t₀, x_{k−1}}` — and the **shortest cycle through `v` has length
> `k + 2`**, so the family crosses (BE-40)'s bound at `k = 5`.
>
> Measured (`bearfull.py chain`): `k = 3…6 × ` 1 or 2 pendants, **8 members**;
> the admitting step is **ASSERTED** to be a genuine spread step at every one —
> *no* witness triple at all makes it star-2, so it is outside (BE-41)(i) and
> not merely unlucky; the `k ≥ 5` members have shortest cycle `7` and `8` and
> are **NOT** in a common `≤6`-cycle class with `t₀`; **and `δ = 0` at every one
> of the 8** (the driver `assert`s it — a `δ ≠ 0` here would be HIT shape 4). So
> the residue is **real**: the `≤6`-cycle certificate is not merely unproved
> past 6, it is **absent**, and (BE-32)(+) survives anyway.
>
> And the same escape **found blind**, in the band where the statement is not
> vacuous (`def₃ > 0`, so `δ = 0` is not free): **2 541** connected graphs at
> `n = 9…13` with `m ∈ [n, 1.4n+2]`, **1 973** of them with `def₃ > 0` **and** a
> forced pair, **27 414** forced pairs of which **`0`** are outside a
> `≤6`-cycle class, and **3 802** direct `δ` computations with **`0`**
> violations.

### Step BE41 — (b2) is a corollary of (b1), and the ear case's (β) side loses a clause

> **(BE-42)(i)** *(proven; **ONE LINE OF GRASSMANN**, and it is not a dimension
> count)* `Π_u ⊆ Z` by the definition `Z = Π_u + Π_v`. So for **any** subspace
> `X`,
>
> `dim(X ∩ Z) + dim Π_u = dim((X ∩ Z) + Π_u) + dim(X ∩ Z ∩ Π_u)
>  ≤ dim Z + dim(X ∩ Π_u)`,
>
> using `X ∩ Z ∩ Π_u = X ∩ Π_u`. With `dim Π_u = 2` and `X = ρ̄₁`:
>
> **`dim(ρ̄₁ ∩ Z) ≤ dim Z − 2 + min( dim(ρ̄₁ ∩ Π_u), dim(ρ̄₁ ∩ Π_v) )`.** ∎
>
> No genericity, no count, no transversality — a Grassmann identity and an
> inclusion. (ZJACOB (JC-6) is satisfied by construction: nothing here is
> derived *from* a dimension count.)

> **(BE-42)(ii)** *(proven; the consequence — (b2) stops being an independent
> clause)* (b2) demands
> `dim(ρ̄₁ ∩ Z) ≤ max(δ₁ + dim Z − 6, dim Z − 2)`. Then:
>
> - **(b1) at strength `≤ 1` gives `dim Z − 1`**, which meets (b2) exactly when
>   `δ₁ + dim Z − 6 ≥ dim Z − 1`, i.e. **`δ₁ ≥ 5`**. So **(b1) ⟹ (b2)
>   outright at `δ₁ ≥ 5`**, `dim Z` cancelling — the same cancellation
>   (BE-36) used to refute (β) as stated, now pointing the other way.
> - **(b1) sharpened to `ρ̄₁ ∩ Π_u = 0` at EITHER end gives `dim Z − 2`**, i.e.
>   **(b2) at every `δ₁`**.
>
> So the three clauses of (BE-37)(ii) are **not independent**: (b2) is (b1) at
> one end, sharpened from `≤ 1` to `0`. The only pieces needing more are those
> with `min(dim(ρ̄₁ ∩ Π_u), dim(ρ̄₁ ∩ Π_v)) ≥ 1` and `δ₁ ≤ 4`. Of those, the
> `= 2` case is `Π_u ⊆ ρ̄₁`, i.e. the **(P) trap genuinely realised**, which
> (BE-38)(iii) **asserts** does not occur below `ρ₁ = 6` (a non-vacuous
> occurrence would stop that driver); and the `= 1` case is the **series**
> shape at that end — every `u–v` path leaving `u` by the same edge, an S-node
> in the SPQR sense. There (BE-30)(i) describes `ρ̄₁` as a chain through that
> leading hinge line, (BE-38)(i) settles the **all-S** piece outright, and a
> general such piece **peels** its leading edge and recurses down the SPQR
> tree — stated here as the route, **not** as a proof. ∎

> **(BE-42)(iii)** *(the sharpening's mechanism, NAMED rather than measured)*
> Every hinge line at `u` lies in `Π_u = p_u ∧ π_u`: the closed star of `u` is
> coplanar in `π_u` ((BE-16), read off `verify_pencil_witness`), so a hinge line
> at `u` passes through `p_u` inside `π_u`. `assert_generic_star` forbids two
> hinge lines at a body from coinciding, so **any two hinge lines at `u` SPAN
> `Π_u`**. If two `u–v` paths leave `u` by different edges then `ρ̄₁` lies in
> **both** path spans ((BE-30)(iv)) whose `Π_u`-parts are **different lines**.
> That is the mechanism behind (BE-38)(iii)'s measured *"`0` wherever two `u–v`
> paths leave `u` by different edges"* — stated here as the reason, with the
> honest note that turning it into `ρ̄₁ ∩ Π_u = 0` still needs the interior
> lines to be generic against `Π_u`, which is a **genericity proviso** and is
> labelled as one.
>
> **CORRECTED 2026-08-28 (BSHARP, (BE-45)(iii)): the sentence this mechanism was
> read off is false, so the mechanism is NOT SUFFICIENT.** The containment is
> real and it decouples per path ((BE-44)(i)), but distinct first edges do not
> give `0` — six of the `bgrass` rows below have three of them and `dim = 1`, by
> path saturation ((BE-45)(ii)); the exact criterion is (BE-45)'s dichotomy. The
> genericity proviso this block disclosed is separately **DISCHARGED**
> ((BE-46)); what fails is **sufficiency**, not the proviso. No measurement in
> this block changes.
>
> Measured (`bearfull.py bgrass`): **19 pieces, every one with
> `dist_{G₁}(u,v) ≥ 5`** — exactly the regime (BE-38)(ii)'s `dist ≤ 4` transfer
> does not reach — over 8 independent generic draws each from bearcase's free
> parametrization, each passing `assert_generic_star` **and**
> `verify_pencil_witness`, with the chosen plane at `u` and at `v`
> **asserted** equal to `plane_at`'s closed-star plane and `Π_u ⊆ Z`,
> `Π_v ⊆ Z` **asserted as identities of spaces**. **(BE-42)(i) held at every
> draw of every piece and was TIGHT at 144 of them**; **`0` pieces fail (b2)**.
> The rows split exactly as (BE-42)(ii) predicts: every piece with
> `dim(ρ̄₁ ∩ Π_u) = 1` came out at `δ₁ = 5` (so (b1) ⟹ (b2)), and the two
> pieces with `0` — `θ(5,5,5)` at its hubs (`δ₁ = 3`) and `C₁₀` at antipodes
> (`δ₁ = 4`) — are proved by the second branch. Every `(2,2)` row is a
> `δ₁ = 6` row, i.e. the vacuous corner the spec's own observation 1 names.

### Step BE42 — the routing verdict: the ear route is REFUTED as a replacement for the internal R-node

**The hypothesis, restated as the coordinator posed it.** Every 2-connected
graph has an **open ear decomposition** starting from a cycle — **classical**,
and the construction is Whitney's (H. Whitney, *Non-separable and planar
graphs*, Trans. Amer. Math. Soc. **34** (1932), no. 2, 339–362; author, year,
title, journal, volume and pages verified against the AMS primary listing, and
**no section number is asserted**, per `CLAUDE.md` *Referencing prior work*).
(BE-18) reduces (BE-14) to 2-connected graphs; a cycle is max-degree `≤ 2`, one
of the **free** base classes ((BE-25)(iv)); and each ear **with an interior
vertex** attaches at a pair `{u,v}` that **is** a 2-cut of the enlarged graph,
so that step is exactly BEARCASE's ear case with `G₂` the ear and `G₁`
arbitrary. **Each of those four links checks out** — they were verified against
the landed statements, not against the prose that cites them. The question is
whether anything else is needed. It is.

> **(BE-43)(i)** *(proven, one line; **GAP (i) IS DECIDED**)* In a **chord-free**
> open ear decomposition the **last** ear has length `≥ 2` and no later ear
> attaches to it, so its interior vertices have degree **exactly 2** in `G`; and
> if there is no ear at all then `G` is a cycle. Hence
>
> **`G` has a chord-free open ear decomposition ⟹ `G` has a vertex of
> degree 2**,
>
> equivalently: **every graph of minimum degree `≥ 3` — in particular every
> 3-connected graph, i.e. every R-node — forces a single-edge ear in EVERY open
> ear decomposition.** ∎
>
> The counting bound `m ≤ 2n − |C| ≤ 2n − girth(G)` (each ear must add a
> vertex) is the weaker numerical shadow of the same fact; `K₄` violates it
> already (`6 > 5`).
>
> Measured (`bearfull.py eardec`): **EXHAUSTIVE over the 2-connected labelled
> graphs on `n = 3…6` (11 617) plus 900 seeded masks at each of `n = 7, 8` —
> 12 620 graphs**, per-graph **decided** by exhaustive search with two sound
> prunes: **6 968** admit a chord-free open ear decomposition, **every one** of
> them has a degree-2 vertex (`0` exceptions, which the theorem forbids), and of
> the **2 084** 3-connected graphs **ZERO** do.

> **(BE-43)(ii)** *(proven and swept; the chord step's COMBINATORIAL half is
> FREE)* Adding `uv` raises `d(P)` by one for exactly the partitions that
> separate `u` and `v`, so
>
> **`def₃(G + uv) = max( def₃(G) − δ_uv, def₃(G) − 5 )`.**
>
> *Proof.* `value_{G+uv}(P) = value_G(P) − 5·[u,v separated]`. The maximum over
> partitions with `u, v` together is `g_uv = f − δ_uv`; the maximum over the
> rest is `≤ f`, with equality whenever `δ_uv > 0`; and `f − δ_uv = g_uv ≥ 0`,
> so the `max` is never empty. ∎
>
> Measured: **EXHAUSTIVE over every connected labelled graph on `n = 3…6` and
> every non-edge — 189 587 `(graph, non-edge)` instances, `0` violations.**

> **(BE-43)(iii)** *(the obstruction, and it is not a dimension count;
> **GAP (i) is NOT soft**)* By (BE-16) the pencil condition **is** *every closed
> star coplanar*. So `G + uv` demands **`p_v ∈ π_u` AND `p_u ∈ π_v`**: the
> chord variety `Y°(G+uv)` is a **proper closed subset** of `Y°(G)`. The
> induction hands over a **generic** point of a component of `Y°(G)`, which
> therefore lies **outside** `Y°(G+uv)`. And attainment cannot be inherited by
> specialisation in any case: `dim M` is **upper** semicontinuous, so moving
> onto a proper closed subvariety can only **raise** it above the cap
> attainment demands — the semicontinuity points the **wrong way**, which is
> the same shape as the arc's other hard steps.
>
> Measured: **128** generic pencil draws from bearcase's free sampler, at
> pieces with `u, v` **non-adjacent**, each **decided exactly** (a rank
> computation over ℚ, never sampled): **`0`** satisfy both conditions. The
> codimension is **2 conditions** whenever both closed stars span a plane —
> **labelled as a count**; nothing here derives properness, smoothness or
> transversality from it.

> **(BE-43)(iv)** *(**GAP (ii)**: the third shape exists, is weaker than S-all,
> and still meets cross pairs)* The ear induction needs the welding clause at
> the **next** ear's attachment pair, so it carries a third shape — call it
> **S-dec**, marked by the **decomposition** rather than by a rooted tree.
> S-dec is strictly **weaker** than S-all (finitely many pairs, **named in
> advance**) and is not S-mark; **that weakening is the one genuinely new piece
> of information the lifted bar bought**, and it is worth recording because it
> makes the cross-pair obligation a question about a *named finite set* rather
> than about *all* pairs.
>
> It does **not** avoid cross pairs. A later ear may attach at a vertex
> **interior** to an earlier ear, and then the pair is a **cross pair** in the
> sense of (BE-28)(i) — contracting it destroys the 2-cut, so neither the
> (BE-21) `def₃` law nor the (BE-22)(i) fibre-product law reaches it. **Proved:**
> a decomposition avoiding that entirely forces **every degree-`≥3` vertex onto
> the initial cycle**, because a vertex off `C` that receives no later
> attachment has degree 2. So a **necessary** condition for the ear route to
> avoid cross pairs is that **some cycle of `G` carries every branch vertex**.
>
> Measured, and the first column is an **honest negative for this analysis**:
> **12 620 of 12 620** swept 2-connected graphs have such a cycle, so under the
> cap gap (ii) does **not** bite. It says where to look instead. For a
> **subdivision** of a base `B`, a cycle carrying every branch vertex is exactly
> a **Hamiltonian** cycle of `B`; the **Petersen** graph is 3-connected and
> **non-Hamiltonian** (decided by exhaustive search in the driver), so **every
> subdivision of Petersen** — 2-connected, not 3-connected, carrying an
> **internal R-node** — has no such cycle, and every open ear decomposition of
> it meets a cross pair. **Both gaps localise at the same place: the R-node.**

> **(BE-43)(v)** *(**THE VERDICT**, and the classification, mandatory and
> explicit)*
>
> **NO.** The ear case is **not** already the induction step, and the internal
> R-node ((BE-31)(ii), BEARCASE's successor (3)) **does not leave the critical
> path**. The reason is (BE-43)(i): every R-node forces a single-edge ear, and
> (BE-43)(iii) prices that ear as a genuinely new geometric obligation of the
> same shape as the ones the arc has found hard. **S-mark's pin ((BE-25)(ii))
> STANDS** — and stands for a *different* reason than BTWOCUT's: not because
> S-all's cross-pair gap is unclosed (it still is), but because the ear route
> does not escape it and adds a second gap of its own.
>
> **What the route DOES buy, stated positively rather than discarded.** It
> **re-specifies** the internal R-node instead of retiring it: given cross-pair
> closure, *"handle a 3-connected block with flexible children"* becomes
> *"handle a single edge addition, repeated"* — a strictly more local
> obligation, whose **combinatorial half is already free** ((BE-43)(ii)) and
> whose geometric half is one sentence long. Whether that is progress is
> exactly the price of the chord lemma, and it is now a **named** item rather
> than a hunch.
>
> **Nothing the arc carries is refuted.** Not `PencilPair K 3 G`; not
> `hbareSplit`; not (BE-14)-for-all-`G`; not the 2-cut step; not S-mark. What
> **is** refuted is the **coordinator's own job-3 hypothesis**, by a theorem.
> What is **strengthened** is (BE-32)(iii) (its hypothesis weakens from `≥ 3`
> to `≥ 2` common neighbours) and (BE-32)(iv) (`δ ≤ max(0, L−6)` beats
> `δ ≤ dist` for `L ≤ 11`). **No route is closed. One route is refused.**
> **Not a PENCIL event.**

### Verdict, classification, and the price

**Which HIT shape this is.** **Shape 3** — *a routing verdict on job 3 that
re-ranks the board, in the NO direction*, which the spec calls a real
deliverable — **carrying shape 2's job-2 half**: (b2) is closed, as a reduction
to a clause the (BE-37)(ii) reduction already carries. It is **not shape 1**:
job 1 is not closed. It is **not shape 4**: no obstruction to (BE-32)(+) was
found, and the deliberately adversarial family built to break the proof has
`δ = 0` at every member.

**Job 1 ((BE-32)(+)).** **Advanced from MEASURED to PROVED at 96.2 % of
instances, and REDUCED for the rest.** The closure operator is **named** (the
aggressive one, `bimage.forced_same_plane`, which over-claims forcing). The
mechanism is a **short-cycle law** that contains both known mechanisms as its
`L = 3` and `L = 4` cases, plus a **join lemma** that makes `δ = 0` transitive
so the certificates compose. 401 489 of 401 544 forcing steps and 196 043 of
203 723 forced pairs are **proved**; the residue is the **spread** step at 55
instances, all at `n ≥ 7`; and what is left is a statement with **no geometry
in it**.

**Job 2 ((b2) for a general piece).** **CLOSED, as a reduction, and the
reduction is one line.** (b2) follows from (b1) outright at `δ₁ ≥ 5` and from
(b1) sharpened to `0` at either end for all `δ₁`; the leftover — series at
both ends with `δ₁ ≤ 4` — is where (BE-38)(i) settles the all-S piece and the
SPQR peel is the route for the rest, stated as a route and not as a proof. Measured at 19
pieces with `dist ≥ 5`, exactly the regime (BE-38)(ii) does not reach, with
`0` failures and the bound tight at 144 draws.

**Job 3 (the routing question).** **DECIDED NEGATIVE by a theorem.** Reported
as a verdict, not a preference, exactly as the spec demanded; and the negative
is worth what the spec said it was worth — it **confirms S-mark** and retires
the distraction, while leaving behind one usable reformulation and one new
combinatorial law ((BE-43)(ii)).

**The price, re-quoted against BEARCASE's.**

- **BEARCASE's successor (1) is 96.2 % discharged and fully reduced;
  successor (2) is discharged.** Successor (3), the internal R-node, is
  **confirmed** on the critical path by job 3 and is now the arc's sole named
  residue of the 2-cut lemma alongside the spread step and cross-pair closure.
- **What it will cost next.** **(1)** The **SPREAD STEP** — stated here as
  *every aggressively-forced pair lies in one `≤6`-cycle class*, which
  **direction BSPREAD found REFUTED as stated** (2026-09-01, (BE-76)) and then
  **CLOSED by a different tool**: the residue is *forced ⇒ `δ = 0` at the
  spread steps*, and **(BE-74) proves it outright** — pure graph theory,
  55 known instances, and the merge inequality is **known** not to reach it
  (a 7-cycle of `Q` has slack `−1`), so the successor needed a different tool
  or a restriction of the closure operator, and the **different tool** is
  (BE-39)(i) spent on the closure's admission rule rather than on cycles. **(2)** **(b1) sharpened to `0`**, which
  is now carrying **both** (b1) and (b2). **(3)** The **internal R-node**, and
  its new alternative coordinate: the **chord step** *(BE-14) + clause for `G`
  ⟹ for `G + uv`*, whose combinatorial half is free. **(4)** **Cross-pair
  closure** ((BE-28)(i)), unchanged, and now known to be required by **both**
  candidate inductions.
- **What a successor should attack, in this pass's ranking.**
  **(1)** **(b1) sharpened to `0`** — it now discharges two of the three
  clauses of the ear case's (β) side, and (BE-42)(iii) names its mechanism.
  **(2)** The **spread step**, the last 3.8 % of (BE-32)(+).
  **(3)** The **chord step**, as the internal R-node's local reformulation.
  **(4)** BTWOCUT's successor (2), the bundle-construction proof — unchanged,
  still skipped.

### Verification

`python3 notes/scripts/w4/bearfull.py merge` (39 s — 28 572 graphs, 28 633
optimal partitions, 130 331 enumerated part-subsets, 61 tight sets, 61 join
pairs, 435 072 `P_max` pairs); `cycles` (24 s — 241 771 short-cycle
incidences, 33 262 6-cycle incidences, 294 500 class pairs, 289 000 `L`-bound
pairs, 61 770 two-common-neighbour pairs); `forced` (9 s — 401 544 steps,
203 723 pairs, 144 539 direct `δ` checks); `chain` (1 231 s — the 8-member
boundary family plus 2 541 blind graphs, 27 414 forced pairs, 3 802 `δ`
computations); `bgrass` (394 s — 19 pieces × 8 generic draws); `eardec` (3 s —
12 620 2-connected graphs decided, plus the Petersen witness); `chord` (25 s —
189 587 `(graph, non-edge)` instances and 128 decided pencil draws);
`validate` (467 s, exit 0 — reduced tiers of all seven modes).

Every mode `assert`s its proved laws rather than printing them: a violation of
(BE-39)(i)/(ii), (BE-40)(i)–(iii), (BE-42)(i), (BE-43)(i) or (BE-43)(ii) stops
the run. `optimal_partitions` cross-checks its own set-partition enumeration
against `kbare_common.exact_deficiency`'s packing oracle on **every call**;
`def3_fast` cross-checks `btwocut.def3_multi` against `exact_deficiency` at
every call with `|V| ≤ 13`; `forcing_derivation` `assert`s that its recorded
derivation reproduces `bimage.forced_same_plane`'s pair set exactly.

**F25 bar, read off the shipped driver.** Eight modes, one per headline
sentence. The combinatorial modes are **exact integer arithmetic with no
sampling inside a graph**: `optimal_partitions` enumerates the **whole**
partition lattice, `merge` enumerates **every** subset of every optimal
partition's parts, `cycles` enumerates **every** cycle to length 8, `forced`
enumerates **every** forcing step of **every** seed hub, `eardec` **decides**
each graph by exhaustive search with two sound prunes, and `chord`'s `def₃`
law is checked at **every** `(graph, non-edge)` pair. The geometric mode is
**exact ℚ** throughout, every rng **seeded with a printed literal**, every
configuration passed through `assert_generic_star` **and**
`kbare_common.verify_pencil_witness`, the chosen planes at `u` and `v`
**asserted** equal to `plane_at`'s closed-star planes, and `Π_u ⊆ Z`,
`Π_v ⊆ Z` **asserted as identities of spaces** rather than of dimensions.
`chord`'s geometric column is a **decision** (a rank over ℚ), not a sample.
Graph-level sampling appears only where it is named as such: the `n ≥ 7` mask
tiers and the `n = 9…13` blind hunt.

### Caps, disclosed rather than smoothed

1. **`merge` and `cycles` are exhaustive to `n = 6` and sampled beyond.** Only
   **61** graphs under the cap have more than one optimal partition (they are
   the 6-cycles), so the **join-lemma sweep is thin** — the lemma is
   **proved**, and the sweep confirms rather than carries it. The same is true
   of the 61 tight sets.
2. **`cycles` enumerates cycles to length 8 only**, so the
   `δ ≤ max(0, L−6)` column is read at the shortest common cycle of length
   `≤ 8` and is **silent** about pairs whose only common cycles are longer.
3. **(BE-41)(ii) is MEASURED, not proved**, and is the load-bearing cap of job
   1. **CORRECTED 2026-09-01 (direction BSPREAD, (BE-76)): this disclosure is
   WEAKER THAN THE TRUTH and under-reports a KNOWN refutation.** It reads *"no
   aggressively-forced pair outside a `≤6`-cycle class was found under this
   cap"*, never *"none exists"* — but one **is** known to exist, by
   construction, at (BE-41)(iii) in this same direction. The honest form is
   *"the escape set is non-empty and constructed; the tiers below sample the
   region where none was found"*. A cap disclosure that under-reports a known
   refutation is the F11 hazard running backwards. (The clause itself is now
   **retired** by (BE-74), which proves (BE-32)(+) with no cycle certificate.) The `n = 7, 8, 9` tiers are
   1 400 seeded masks each; the `n = 9…13` blind hunt is seeded random and
   computes `δ` at every not-connected pair **and two further forced pairs per
   graph**, not at all of them.
4. **The direct `δ` check on forced pairs is capped at `n ≤ 7`** by the cost of
   `g_exact`; beyond that the evidence is the blind hunt's 3 802 computations.
5. **`bgrass` inherits bearcase's sampler shape guard** — branch vertices an
   independent set, each free vertex with at most one branch neighbour — so the
   battery is **subdivisions only**, and says nothing about pieces with
   adjacent branch vertices. `δ₁` is the **measured** max `dim ρ̄₁` over draws, a
   **lower** bound on the combinatorial `δ₁`, which **under**-states the (b2)
   bound — the conservative direction.
6. **(BE-42)(iii) is a mechanism, not a proof of `ρ̄₁ ∩ Π_u = 0`.** The
   containment `ρ̄₁ ⊆ ⟨P⟩ ∩ ⟨Q⟩` is exact and the two `Π_u`-lines are distinct;
   concluding `0` still needs the interior lines generic against `Π_u`, and
   that is **labelled a genericity proviso**, exactly as (BE-38)(ii) was.
7. **`eardec`'s per-graph decision is exhaustive within a 400 000-state cap**
   with two sound prunes; a cap overflow is reported **UNDECIDED**, never as a
   negative (none occurred). The sweep is exhaustive to `n = 6` and 900 seeded
   masks at `n = 7, 8`.
8. **(BE-43)(iii)'s measurement establishes only that the generic point of
   `Y°(G)` is not a chord point** — **not** that `Y°(G+uv)` is empty, nor that
   it has any particular dimension. The codimension-2 statement is **labelled a
   count**.
9. **(BE-43)(iv)'s cross-pair necessary condition does not bite under the
   cap.** The Petersen witness is a **construction**; it shows the condition
   fails somewhere, not how often.
10. **Nothing here touches the closure operator's own faithfulness.** Every
    claim is about the **aggressive** operator, which over-claims forcing; a
    theorem for it holds a fortiori for the genuinely forced pairs, and that is
    the only direction in which the caps are safe.

### Harness note — the `kbare/` sibling-import set gains its SEVENTH `w4/` consumer

`notes/scripts/w4/bearfull.py` imports `bearcase`, `bimage`, `btwocut`,
`binduc`, `bzavoid` and `kbare_common` **read-only**. The recorded **UNPAID**
debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20) is extended: the
chain is now **SEVEN** deep — `battain → bzavoid → binduc → btwocut → bimage →
bearcase → bearfull` — and `bearcase` gains its **first** external consumer
(`sample_piece_config`, `subdivide`), which is a **new** row. **NO MOVE MADE**:
a dispatch may not edit a landed driver another direction may be importing in
flight. The consumer lists to extend are the `kbare/`, `battain`, `bzavoid`,
`btwocut` and `bimage` rows, plus a new `bearcase` row.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-39)(i) quotient sparsity, `girth(Q) ≥ 6` | **PROVED** (one line from the merge inequality), swept at 130 331 enumerated subsets |
| (BE-39)(ii) join lemma, `δ = 0` an equivalence relation | **PROVED** (supermodularity of `g`), swept thinly (61 pairs) because few graphs have two optimal partitions |
| (BE-40)(i)/(ii) short-cycle law to `L = 6` | **PROVED**, swept at 241 771 + 33 262 incidences |
| (BE-40)(iii) `δ ≤ max(0, L−6)` | **PROVED**, swept at 289 000 pairs to `L ≤ 8` |
| (BE-40)(iv) (BE-32)(iii) weakens to `≥ 2` common neighbours | **PROVED**, swept at 61 770 pairs |
| (BE-41)(i) star-2 step | **PROVED**; covers 401 489/401 544 steps and 196 043/203 723 pairs |
| (BE-41)(ii) forced ⟹ `≤6`-cycle class | **REFUTED AS STATED** (2026-09-01, direction BSPREAD (BE-76)) — the 203 723 + 27 414 pairs with 0 escapes are the **random/enumerated** tiers; the **constructed** tier on the next row escapes **by design**. **RETIRED, not repaired**: (BE-74) proves (BE-32)(+) with no cycle certificate |
| (BE-41)(iii) the boundary family | **CONSTRUCTED**; `δ = 0` asserted at every member |
| (BE-42)(i) the Grassmann bound | **PROVED**; exact at every draw, tight at 144 |
| (BE-42)(ii) (b1) ⟹ (b2) at `δ₁ ≥ 5`, and always from `0` | **PROVED** |
| (BE-42)(iii) the `0` mechanism | **NAMED, not proved** — genericity proviso disclosed |
| (BE-43)(i) min-degree-`≥3` ⟹ a chord is forced | **PROVED**; 2 084 3-connected graphs, 0 chord-free |
| (BE-43)(ii) `def₃(G+uv)` law | **PROVED**, swept exhaustively at 189 587 instances |
| (BE-43)(iii) the chord's geometric obstruction | **PROVED** for the semicontinuity half; the codimension is a **count**; 128 decided draws |
| (BE-43)(iv) cross pairs need a cycle through all branch vertices | **PROVED** (necessity); does not bite under the cap; Petersen witness |
| (BE-43)(v) the routing verdict | **NO**, resting on (BE-43)(i)+(iii) |

### What would change this

- **A proof of the spread step** — or a restriction of the aggressive closure
  that excludes it — would make (BE-32)(+) a theorem outright and, with (BE-42),
  close the ear case's (β) side to the single remaining clause (b1)-sharpened.
- **A forced pair with `δ ≠ 0`** would be HIT shape 4 and would have to be
  classified against (BE-23)(ii); the 8-member boundary family and the 27 414
  blind pairs were built to find one and did not.
- **A chord lemma** — *(BE-14) + the clause for `G` ⟹ for `G + uv`* — would
  reverse the job-3 verdict outright and retire the internal R-node, and its
  combinatorial half is already free ((BE-43)(ii)).
- **A graph whose optimal partitions have a `Q`-cycle of length `> 6`** would
  show the tight sets are richer than 6-cycles and might extend (BE-40); none
  appeared under the cap (the girth histogram is `forest` or `6`, nothing else).

### TERMINATION riders

**E1: NO** — this direction is partition combinatorics plus one Grassmann
identity plus one graph-theoretic theorem; no `g`-flank is involved and none is
produced. **E2: NO** — nothing landed is refuted; one landed hypothesis is
**weakened** ((BE-32)(iii)) and one landed bound **improved** ((BE-32)(iv)),
which is the strengthening shape E2 does not fire on, and the ear case
**narrows** by one clause. **E3: ARMED by GBAL, not fired** — this direction is
on the §(K-bare-ext) path, not (a′); reported, not acted on.
