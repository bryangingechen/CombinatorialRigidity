# PENCIL kernel-(K) research fan-out — dispatch specs

**Status: EIGHT fan-outs, FORTY-NINE single directions, ONE draft-only parallel direction,
FOUR concurrent pairs and ONE concurrent round of four dispatched; 88 LANDED, **NONE IN
FLIGHT, NONE DRAFTED — the concurrent round of four is COMPLETE** (BARCH 77, OBAR 78,
DSAT 79, GLEAF 80).
*(Round state, coordinator, 2026-09-03 — **CLOSED at GLEAF's landing**; what stays is the
round's cross-return observations, not its queue.

**DSAT** — **LANDED 2026-09-03 as ordinal 79**; detail in §"DSAT" below, not here. Status
only: **C2 is STRUCK as a *uniform* carry** — the (K-res) half **proved**, the class half
**measured at five shapes**, so it is **not** shown dead as a class-only conjunct; the
`(K-dom)` row landed at **581/800** status and **95/800** close-it, recomputed not appended, `gapdiff.py K-dom` **0 dropped**; §8.2, §8.6, §4-C2, §8's two
live-list clauses and §4's gate box moved in **one** commit as required; and its labels
**deviated correctly** to `(DM-5)`–`(DM-11)` per clause (L1) — reservation defect shape
three of the round, diagnosed in `notes/Pencil-labels.md`'s defects block, not here.

**OBAR** — **LANDED 2026-09-03 as ordinal 78**; detail in §"OBAR" below, not here. Its
`(K-out)` cell landed at **1810/1823** after a second content-duplication compression, so
the next `(K-out)` landing must **recompute, not append**; §8.2, §4.6 and §8.6 moved in
**one** commit as required; and its step-1 negative is chart-wide **on §(K-σ) (σ7)'s own
basis** — conjunct 4's argument plus 39/39 witnesses — never more.

**GLEAF** — **LANDED 2026-09-03 as ordinal 80**, the round's last; detail in §"GLEAF"
below, not here. Status only: **the reach question SPLIT** — the landed Phase-12/13/14
machinery **does** reach the branch-side demand, by a theorem, and what it reaches is
**implied by** (GR-18)(iii)'s residual, so **§8's rank 3 is SPENT**. Both of its owed
adjudications were cleared in advance (`a5d8101c`) and both were **spent at the landing**:
the `(K-grid)` fourth compression landed the row at **2 688/2 715** status and **974/985**
close-it with `gapdiff.py K-grid` **0 dropped, 8 added**, and the `notes/gapmap.py`
docstring was already re-worded to an unmintable placeholder. Its labels **deviated
correctly** to `(GR-145)`–`(GR-152)` — reservation defect shape **four** of the round, and
OBAR's shape five is the same error, which is what made the diagnosis systematic;
`notes/Pencil-labels.md`'s defects block owns it, not here.

**ALL FOUR VERDICTS HAVE NOW HAD THE COORDINATOR'S VERIFICATION TIER** — the clause that
stood here as *"as reported, not confirmed"* is discharged; each landing carries its own
disclosed self-caught defect
(DSAT an assert-caught wrong guess, GLEAF a **silently-wrong oracle** caught only by two
oracles disagreeing; OBAR's was an **unexercised failure branch**, which landed disclosed
as its own *Caps* item 1) — read those before trusting a figure.)*
**The eight landings after GLIST — BLINE (ordinal 73), BDEGTWO (74), RPOOL (75),
BSCOND (76), BARCH (77), OBAR (78), DSAT (79), GLEAF (80) — have their own sections; read
those, not the blurb below, for the current state.**
**BARCH (ordinal 77, §"BARCH") LANDED 2026-09-03** — the ninth strategy pass's **rank 2**,
dispatched as a **recon** after four structurally-different attempts hit one named
obstruction. **The method class is NOT dead — it CHANGES AMBIENT.** `s` and `r` are BOTH
`p_x`-free on the fixed core, so their GRAPH `Γ ⊆ Λ²K⁴ ⊕ Λ²K⁴` is a FIXED subspace and
`ρ̄_i ∩ Π_x = φ_p(Γ ∩ (Π_x ⊕ Π_x))` **exactly** (99/99, as subspaces) — the clause IS a
surjectivity statement about `Γ`, i.e. (BE-114)(iii)'s technique one ambient up, so
**(BE-139)(iv) is right inside `Λ²K⁴` and OVER-SCOPED as written** ((BE-149)). A **second**
`p_x`-free subspace `R₀ = r(ker s) ⊆ R = ρ̄(core; c₁, c₂)` certifies GOOD at every
`dim A ≤ 5` row (63/99), and a general **path bound** explains the asymmetry: `R`'s bound
is the distance between two neighbours of `x`, `A`'s the distance to the far terminal
((BE-150)). `dim Γ_Π ≤ 1` PROVES GOOD and fires at **39 of the 54** relaxation-blind
fibres, 21 at `dim A = 6` ((BE-151)). **And 14 → 12 reduces to (E4), UNPROVED**: per-side
weakening is **dead** (313/164/74/24/0 escapes at `f = 2..6`, (BE-152)), but the
**two-sided** (E4) `c_i(Π_x) = 2 ⟹ e₁+e₂ ≥ 4` leaves **0** of 6 400, is strictly weaker
(970 tuples) and **holds at BSATUR's own witness** — a per-side refutation cannot touch a
statement about the pair ((BE-153)). **§8's bar LIFTS narrowly**: `A_sharp` properness as
posed stays barred, `Γ`-properness and (E4) are lifted ((BE-154)). The clause itself stays
**OPEN**, (E4) is **unproved**, class uniformity **untouched**; not a PENCIL event. Driver
`notes/scripts/w4/barch.py` (five modes, `validate` 117 s). Run at `recon-opus`.
**BSCOND (ordinal 76, §"BSCOND") LANDED 2026-09-03** — the ninth strategy pass's **rank 1**,
at **(BE-57)(iv)'s two window conditions**, open since BWIN (51) and attacked by none of the
eleven (BE-14)-thread landings since. **BOTH DECIDED, AND THEY WERE ONE GAP**: the pencil
condition puts `p_{w₁} ∈ π_u` and `p_{w₂} ∈ π_v` always, so coincidence lands on `L` and the
leading lines MEET — **(S1) failing IS (S2)'s meeting-lines regime** ((BE-143)). **(S1) is
REMOVABLE** ((BE-148)): (BE-55)(iii)'s proof is **plane-agnostic** at `σ = ℓ_u ∨ ℓ_v`
((BE-144)), so the theorem holds with the hypothesis deleted. **(S2)'s first half is PROVED**
with the forcing list **exhaustive at two** by a `2 × 2` enumeration plus a
dense-open-vs-proper-closed argument ((BE-145)); **its second half is REFUTED AS STATED** —
`p_{w₁} = p_{w₂}` pins `λ` onto `W^{⊥K}`, at real window middles including two R-node ones,
the equivalence being `W ⊆ Σ_p` ((BE-146)) — **and then CLOSED** by the **coincidence excess
law**, which replaces the generic slice by a **dimension cap** (`Σ_p` caps `dim ρ̄₁ ≤ 3`, so
`excess = dim ρ̄₁ − 2 ≤ 1`) rather than repairing it ((BE-147)). The support audit is the
headline's other half: both samplers carry a **global distinctness filter**, the guard the
clause names rejects coincidence only on **edges**, and the pencil **predicate admits** it —
so `bwin.full_measure`'s own `(BE-56)(ii)` assert **fires** at 30 of 100 rows of the new
population ((BE-142)). **S-mark's other half — half (B) at side-degree `≥ 2` — is UNTOUCHED**;
not a PENCIL event. Driver `notes/scripts/w4/bscond.py` (eight modes, `validate` 229 s). Run
at `recon-opus`. *(Counter reconciled
by the coordinator 2026-09-03: this header read **76** and named GLIST as the latest landing
while `ROADMAP.md` read 82 and `Phase39.md` 83 — two concurrent directions incrementing one
shared counter from different baselines, the hazard `RESEARCH-ARC.md` §2 records. The count is
**directions**, which run **ordinal + 8**; no direction increments it, the coordinator does.)*
**GLIST (ordinal 68, §"GLIST") LANDED 2026-09-02** — the `hK` lane's own named successor,
one direction after GPACK, at **(GR-132)'s hub list-colouring at the `ℓ = 2`-rich shapes**;
the **committing** dispatch of a concurrent pair. **HIT shape 3 — REDUCED to a named
strictly-smaller condition — with HIT shape 1 on two sub-statements.** The end pattern is
**eliminable**: (GR-132)'s three clauses are a CSP in `α : hubs → J` and `γ : hubs → J^c`
alone, and **clause (a) is FREE**, implied by (b) because each of the six parts of
(GR-18)(i)'s partition is a **spanning** tree ((GR-134)). At a hub whose branches are all
length 2 (*pure*) the local system is feasible iff the incident absence-pairs lie in one
cross, and **at hub degree 3 that is `J`-free: `u` must be a LEAF of at least one of the six
trees**, equivalently the three `D_β` must not be a **perfect matching of `{1..6}`**
((GR-135)) — a second obstruction mechanism, independent of (GR-131)'s odd cycle, verified
exhaustively over the abstract configuration space. By the excess law there is **no
all-length-2 shape** and at `D = 0` at least `n − 12` hubs are pure, so the local half is a
**leaf-covering** demand on the packing ((GR-136)) — **but 82 % of the infeasible pairs are
locally feasible at every hub**, so the residual is genuinely global and this is *reduced*,
not *proved*. **The forced support audit REFUTES the coordinator's own expectation**: the
population **does** present the conflict (6 of the 12 shapes carry a pure hub), and what is
defective is the **denominator** — `229 320/229 320` counts only accepted pairs, against
**472 680** legal ones, 243 360 rejected ((GR-137)). Exhaustively at `n_hub = 4` on the
`D = 0` stratum, some legal pair is feasible at **every** shape. **The flagged option-board
contradiction is RECONCILED** (statement vs method), and **(GR-10)/(GR-15) are unchanged; E1
does NOT fire** — the one object that looked like a flank is refuted in the same step by 60
certificates, a *not-found-under-cap* reading of this direction's own DFS. Driver
`notes/scripts/w4/glist.py` (four modes, 530 s). Run at `recon-opus`.
**BSIGMA (ordinal 67, §"BSIGMA") LANDED 2026-09-02 — run DRAFT-ONLY in parallel with
GPACK**, the arc's first concurrent pair outside a prepared fan-out, and a **HIT on the
disproof lane**. BSATUR's own named residual `Σ_x ⊆ ρ̄_i` at `ρ_i = 5` is **REALIZED**, on
BSATUR's own peel with a new *configuration* — `p_x` and its tail coplanar — so **every**
flag is bad and **(PENCIL-SATURATES-GEN) is FALSE**. **SLACK, not a shortfall**, for the
third refutation running (78 rows, 0 shortfalls); half (B) untouched. Second result: the
**floor is a THEOREM** — `Σ_x ⊆ ρ̄_i ⟹ ρ_i ≥ 5` by a corank identity that also upgrades
(BE-105)(ii)'s measured half to proved. The forced support audit answers sharply: the
battery's five `deg = 1` terminals are its five **path** pieces, one generic configuration
each, so **the flag was never a variable of this claim** — the missing quantifier is the
**configuration stratum**. Survivor **(PENCIL-SATURATES-CHART)**, at a generic chart point.
**GPACK (ordinal 66, §"GPACK") LANDED 2026-09-02** — the arc's **FIRST `hK`-side direction
in 22 dispatches**, at **(GR-18)(iii)**, the grouping problem. **HIT shape 1 on a named half,
HIT shape 3 on the rest: the SPLIT is a THEOREM and the exchange freedom is LOAD-BEARING.**
The target has a normal form that deletes the packing from the statement — *"`|C_β ∩ J| =
3 − A(β)` for a length-legal `A(β)`"* is exactly *"`J` bisects `C_β` as evenly as
possible"*, and a (packing, split) pair is exactly a **signing** `s` of the odd branches with
`\|s(F)\| ≤ σ(F) = Σ_F ℓ − 6·c(F)`, the **5/6-sparsity slack** ((GR-129)); balance falls out
free. And **a legal signing always exists** ((GR-130)) — unconditionally, `def(G) = 0` and
nothing else, by Nash-Williams arboricity + Tutte/Nash-Williams packing + Edmonds' covering
applied a second time to the *halved* multiplicities, so **neither the packing nor the split
is ever the obstruction** and *Step G21*'s named successor object is retired. The
coordinator's reading was **verified at source and correct**; its named expectation was
**refuted exhaustively** — of **266 700** enumerated 6-tree partitions, **6 840** admit no
split at all, **every one** of them by a **non-bipartite split graph**, so the
certificate-induced packing is not canonical and `--pack`'s 907/907 is evidence for
(GR-18)(i) alone ((GR-131)). What is left is **exactly** the class-consistency clause, and at
`Λ = ∅` it is a **list-colouring of the hubs** with lists `J ∖ C_β` of size `A(β)`, asserted
sound *and* complete, whose only tight place is the **forced label at a length-2 branch** —
(GR-17)(d)'s own binding profiles ((GR-132)). **Job 2** answers the tight-stratum caveat:
**owned, not free** — `(K-res)` (RS-5)/(RS-6) own it and route `def > 0` members to the
**escape route**, while §2.5's `dim R_a ≥ 2` reading inverts its source. **(GR-10) and
(GR-15) unchanged in status; E1 does NOT fire — the split-less packings are NOT flanks.**
Driver `notes/scripts/w4/gpack.py` (three modes, 336–402 s). Run at `recon-opus`.
**BSATUR (ordinal 65, §"BSATUR") LANDED 2026-09-02** — at **(PENCIL-SATURATES)**,
*`dim(ρ̄_i ∩ Π) = 2 ⟹ ρ_i = 6`*, the clause BDOUBLE's redundancy theorem ((BE-101)) rests
on. **HIT shapes 2 AND 3 — the clause is REFUTED, and the repair is FREE.** The prep's
first instruction was *does the third clause survive the scrutiny the MIDDLE clause of its
own sentence failed*, and the answer is **no**. At a terminal of **side-degree 1** the
legal planes at `x` form a **pencil** (those through `p_x ∨ p_{c₁}`), and one of them is
bad exactly when it carries a `t` with `p_x ∧ t ∈ ρ̄_i`; since (M1) always puts `ℓ_e` in
`ρ̄_i ∩ Σ_x`, **a bad plane exists iff `dim(ρ̄_i ∩ Σ_x) ≥ 2`, i.e. iff `ρ_i ≥ 5`**
((BE-105)) — a trichotomy with no genericity in it. So `K4(5,3,3,3,3,3)` peeled at its
5-branch has **`c₁(Π_x) = 2` at `ρ₁ = 5`**, R-node-shaped, in the **generic flag regime**,
through **both** gates ((BE-104)). **Every sampler in the corpus draws that plane at
random**, so `bearcase.py`'s `assert not (cuv >= 2 and r1 < 6)` — a genuine assert, read at
source — could never fire: the **middle** clause over-read a *sufficient* condition as a
characterization; the **third** over-read a **GENERIC** statement as a **UNIVERSAL** one.
**The price is SLACK, not a shortfall** — `margin ≤ 0` and `reach = min(δ₁+δ₂,6)+a₁+a₂`
asserted at **260** exhibited bad-flag rows over three skeletons, **0** shortfalls — so
half (B) is untouched, exactly as the prep priced it; but at **76** of those rows `Π_x` is
exactly **tight** with `ρ₁ = 5`, and there (BE-101)(i)'s **proof** is gone: under the
measured floor `c_i(Π) = 2 ⟹ ρ_i ≥ 5`, **24** `Π_x` violations escape `U = Λ²K⁴` (controls
reproduce (BE-101)'s own `300/300, 0` and `313`) ((BE-106)). **The repair is
(PENCIL-SATURATES-GEN)** — the same clause **at a generic flag** — and it is **FREE**,
because (BE-14) is **EXISTENTIAL** ((BE-16)), the good locus is dense on an irreducible
chart ((BE-69)) and `reach` is lower-semicontinuous; under it **(BE-101)(i)/(ii) hold
verbatim and the 14 → 12 drop stands**, and at side-degree `≥ 2` there is **no flag freedom
at all** ((BE-107)). **Job 2 fired EMPTY**: **0** both-sides `c_i(⟨M⟩) = 1` rows and **0**
sides exceeding the generic profile at `⟨M⟩` over **72** peel rows — the first measurement
of the 12-block residue ((BE-108)). The coordinator's reading is **INAPPLICABLE** (its
ambient is a side-1-plus-**EAR** composition, and its content is the ear's *loss*, not
`ρ̄₁`'s dimension) **and refuted outright by the witness**, which is the (P) trap genuinely
realized at a non-vacuous piece — the **second** instance of the INAPPLICABLE kind. Driver
`notes/scripts/w4/bsatur.py` (five modes), plus `notes/scripts/gapdiff.py` for F21. Run at
`recon-opus` (fable unavailable).
**BDOUBLE (ordinal 64, §"BDOUBLE") LANDED 2026-09-02** — at **(NO-DOUBLE-PENCIL)**
((BE-97)(iii)), the one place BUNIF's 14 inequalities are tight. **HIT shapes 2 AND 3 —
the condition is REFUTED, and the tight block is REDUNDANT.** (BE-45)(ii)'s own
explicitly-flagged **vacuous corner** `d_min = 6` gives `ρ̄_i = ⟨P⟩ = Λ²K⁴`, hence
`c_i(U) = dim U` at **every** stable `U`; glued to (BE-45)(i)/(ii) at the other side that
is exactly the forbidden `(2, ≥1)` pair — **one landed lemma produces both clauses**, and
it is realized at **2 of BUNIF's own 92 rows** (`K4 + th(6,6,6)/ab + ear4/ua`, peel
`(a,b)`, both 2-blocks) ((BE-99)). BUNIF's census missed it because a side at `ρ_i = 6`
sits at `c_i = 2` **generically** and so never *"exceeds the generic profile"* — the
measurements are untouched, only the named condition was wrong. **It is SLACK, not a
shortfall**: `δ₁+δ₂ = 8`, margin **`−1`**, the peel attaining ((BE-100)), so **half (B)
survives** and this is *not* (BE-71)'s third mechanism. And under **(PENCIL-SATURATES)**
— *`c_i(Π) = 2 ⟹ ρ_i = 6`*, i.e. **(BE-38)(iii)'s third clause** contrapositively —
every `Π_x` violation **is** a `U = Λ²K⁴` violation (**300/300**, 0 escaping; **313**
escape without it), so `Π_x` and `Π_y` **drop out of the fourteen** and are **FREE in the
attaining case**: the live block list goes **14 → 12** and the measured tight place is
**closed** ((BE-101)). **Reading (1) CONFIRMED** — the condition is strictly stronger than
the obligation, equal only at `δ₁+δ₂ ≤ 6` (28 of 49 pairs), and 320 of 1 975 conceivable
double pencils are not violations. **Reading (2) REFUTED at its named weak link**
(`ρ ≤ min(dist,6)` runs the *other* way; 2 sides at `dist = 6`, `δ = 1`) with its
conclusion **recovered through `ρ`** ((BE-102)). **Job 2 fires on BOTH** target citations:
(BE-44)(ii) is used in its **per-shape** converse and (BE-45) in its **converse** — the
refutation itself uses only their proved halves. **Half (B) is NOT discharged**: the
residual is the per-side (PENCIL-SATURATES), the other **12** blocks stay
unwitnessed-not-excluded ((BE-97)(iv)), and the non-attaining case is live. Driver
`notes/scripts/w4/bdouble.py`; write-up §(K-bare-ext) *Steps BE98–BE102*.
**BUNIF (ordinal 63, §"BUNIF") LANDED 2026-09-02** — at **half (B)'s LAST residue**, the
class quantifier (BE-67)(iii), which BPEEL had reduced to *one number per (piece, peel)*:
**`reach(H;x,y) = min(δ₁+δ₂,6)`**. **HIT shape 2 — `reach` IS PER-SIDE DATA, and both
directions of the law are PROVED.** The flag pair's stabilizer `S(ϕ) ⊆ PGL₄` is
**5-dimensional**, contains the maximal torus, and by (BE-70)(ii) acts on **each side's
achievable family separately** (asserted 30/30, including a one-sided reglue through both
gates); in the generic flag regime the screw space splits `S(ϕ)`-canonically as
`Π_x ⊕ ⟨M⟩ ⊕ ⟨L⟩ ⊕ Π_y` of dims `(2,1,1,2)`, whose **16 sums are exactly the
`S(ϕ)`-stable subspaces** ((BE-94)). Against those the modular law gives a **CAP** on
`dim(ρ̄₁+ρ̄₂)` written entirely in per-side data — **containing** (BE-71)'s two located
mechanisms as the `U = core₁∩core₂` and `U = Π_x⊕Π_y` instances ((BE-95)) — and
degenerating each side independently along a 1-PS of `S(ϕ)` gives a **matching lower
bound**, so where the two meet (**121/122** peel rows, **393/400** abstract pairs)
`reach` is **pinned by two proofs** and the cap is **ATTAINED at 400/400** ((BE-96)). So
**(BE-67)(iii) at a peel ⟺ 14 inequalities `c₁(U)+c₂(U) ≤ dim U + max(0,δ₁+δ₂−6)`, each
side's `c_i(U) = dim(ρ̄_i ∩ U)` computed on its own** — exactly the *"statement about ONE
piece"* (BE-22)(vi) named. Measured: violation margin **`0` at 92/92** (so **no
shortfall**), and `Π_x` is the **ONLY** block where **both** sides bite (12/92, tight at
8), leaving the named residue **(NO-DOUBLE-PENCIL)** ((BE-97)). **Reading (1) REFUTED as
stated** (the welded half is not a separate half — it is the `U = Λ²K⁴` term); **reading
(2) CONFIRMED in shape, corrected in its expected failure point** (the operative object is
the flag pair's **stabilizer**, not the base; `G` is **not** inherited as a hypothesis).
Driver `notes/scripts/w4/bunif.py`; write-up §(K-bare-ext) *Steps BE93–BE97*.
**BBASE (ordinal 62, §"BBASE") LANDED 2026-09-02** — back to the **(BE-14) thread** after
four W4-side directions, at **candidate 1**: the **flag base off the no-adjacent-hubs
class** ((BE-65)(i)/(BE-68)(ii) item 1). **HIT shape 1 — the base is FREE, and it was
never (CH-1)'s object.** It is the **flag** variety of `B_real`, a flag at *every* vertex,
hence §(K-chart)'s tower's **stages 1–2 only**; the absent stages 3–4 are exactly where
min degree 2 and girth `≥ 4` are spent, so **(CH-1) does not apply** ((BE-89)). It is
**nonempty always**, a complete intersection of dimension `5|W| − 2|E|` that **factors
over `B_real`'s components**, and irreducible / ℚ-rational / dense in ℚ-points on every
component of **cyclomatic number `≤ 1`** — **with no hypothesis at all** on a forest,
because the flag tower's fibre is irreducible of **constant** dimension 3
((BE-90)/(BE-91)). The only obstruction is **REDUCIBILITY, not emptiness**, at a
`B_real`-**triangle** (flag dims 10 > 9) or **4-cycle** (12 = 12), both off the locus the
standing proviso `G` already imposes and both excluded on the class by girth `≥ 6`
((BE-92)). **All three coordinator readings were CORRECTED**, and job 2 came out two
ways: `hcard` **does** transport to the pieces and does **not** cap `B_real` ((BE-93)).
**Half (B)'s residue drops from TWO items to ONE** — the class quantifier (BE-67)(iii).
Driver `notes/scripts/w4/bbase.py`; write-up §(K-bare-ext) *Steps BE88–BE92*.
**WGROW (ordinal 61, §"WGROW") LANDED 2026-09-02** — the **fourth** W4-side
direction, and it settles **(PAIR-5)** *both ways* — **HIT shapes 1, 2, 3, 4 and
5**. As stated (PAIR-5) is **REFUTED** by `K₂,₃` ((GROW-5)), which is in the class,
carries a proper rigid subgraph (its `C₄`) and has no seed — and is the **only**
such graph; `K₂,₃` is **not a residual**, so **(E) is untouched**. The restriction
the prep's reading (1) named is a **THEOREM**: every class member has a seed **or**
a co-1 rigid set ((GROW-4), the **seed dichotomy**), and a residual forbids the
latter — so **(E-pair) IS A THEOREM** ((GROW-6)), and with (PAIR-6) so is **(V)**.
**W4's non-user-call cost list is EMPTY**; only **(K-res)**, a USER call, remains,
and the four-direction W4 concentration self-terminates exactly as the spec said it
would. The engine is a **change of carrier**: a class member is the partial
subdivision of its hub multigraph, weight `5`/`4` on un-subdivided/subdivided
edges, and rigidity is `exc(Q) = 5a + 4b − 6(k−1) ≥ 0` on every hub partition
((GROW-1)/(GROW-2)) — so the whole question leaves the geometry. **Job 2's fifth
payment is the biggest**: `Graph.deficiency` **is** a max over partitions
(`Deficiency.lean:273`) with a landed **Jackson–Jordán tight-partition layer** on
top, and the W4 workbook cited **none** of it (`partitionDef`: 0 hits) while the
sibling (K) workbook cites it 16 times — so the standing verdict is sharpened to
**per-arc**: *grep the sibling workbook for the Lean file you are about to cite*.
Readings (2) and (3) **confirmed**, (2) with a bound (a `j = 3` ear CAN grow
`|∂_hub|`, 241 witnesses) that kills the named attack as a route. Driver
`notes/scripts/w4/wgrow.py` (four modes, 204 s). Run at `recon-opus` (fable
unavailable).
**WPAIR (ordinal 60, §"WPAIR") LANDED 2026-09-02** — the **third** W4-side
direction, and it **REDUCES (E-pair)** to one named condition while proving two
strata of it — **HIT shapes 3, 4 and 5; not 1, not 2**. The counting shape the prep
guessed is an **exact identity**: if every branch has interior length `≤ 1` then
`f(V(G)) = 6 + e₀ + 2σ` ((PAIR-1)), so ¬(E-pair) forces `f ≥ 6` — against `f ≤ 4`
at every residual ever exhibited — and **(E-pair) follows from `f ≤ 5`**, one unit
weaker than (E). The engine is a **strict generalization of (EL-4)**: no residual
carries a rigid set attached to `≤ 2` outside hubs ((PAIR-3)), because
`hcard(G/U)` is *exactly* `|∂_hub U| ≤ 2` ((PAIR-2)) and the ear moves **never
grow** that count. That closes the independent-hub stratum outright ((PAIR-4):
full subdivisions, so `f ≥ 7` for any counterexample) and leaves the **seed
condition (PAIR-5)** — a hub-graph statement with no feasibility geometry in it.
**Job 3 over-delivers: (V) is a THEOREM given (E-pair)** ((PAIR-6)) — its two
`C₄`-carrying residues are *seeds*, killed by (PAIR-3) — so **W4's non-user-call
cost is now the single obligation (PAIR-5)**, with (K-res) the only other open
item and a USER call. **Job 2 paid a fourth time and now has a standing verdict**:
`ReducibleVertex.lean` carries **five** adjacent-degree-2-pair producers behind the
one cited, and the cited one's `hedge` **is (E) verbatim** — the systematic gap is
that the arc inventories landed *conclusions* and records landed *hypotheses* in
prose. Honest denominator **0, not 255** (the pool's max `f` is 2). Driver
`notes/scripts/w4/wpair.py` (five modes, 282 s). Run at `recon-opus` (fable
unavailable).
**WELOC (ordinal 59, §"WELOC") LANDED 2026-09-02** — the **second** W4-side
direction, and it **REFUTES (E-loc)** while proving the *other* obstruction shape
**impossible** — **HIT shapes 2 and 3, then 4 and 5; NOT shape 1**. `T32`
(`|V| = 32`) is a residual with two **disjoint** count-dependent `C₄` cores, so
every `E(G − v)` is count-dependent and no degree-`2` deletion is independent
((EL-5)); it is certified to the `W19`/`S29` standard — L6b for `G`, the landed
**necessary** `hcard` for both contractions, three rigidity oracles, no middle
zone. **The coordinator's guess was right and it was the cheap half**: a brick is
a hub `C₄`/`C₅` ((EL-3)) and **no residual carries one** ((EL-4)) — sitting away
from the degree-`2` vertices is exactly what makes it **shielded**, which closes
L6b's `¬hcard` escape and lets *Step 2*'s own (C1)+(C5) run with **maximality
replaced by shieldedness**. **Job 2 delivered the two landed items that decide
it**: `isKDof_zero_of_cycle`/`cycle_isProperRigidSubgraph` (every cycle of length
`≤ 6` is rigid, not just the `C₄` this arc cited) and the `hcard` necessary
condition read as a **transfer** — *every hub of a residual has `≤ 2` hub
neighbours* ((EL-1)) — WTRI's inventory lesson at one remove, an item landed AND
inventoried but in only one of its two roles. **(E) is NOT refuted**:
`f(V(T32)) = 4` **exactly**, so `T32` satisfies (E) and **(E) is now known
TIGHT** (the pool's max was `2`). The route dies by more than a hair — the
generalized bound is `f ≤ 4 + κ(v)` and `min_v κ(v) = 2` at `T32`, so the counting
argument reaches only `f ≤ 6`. **Successor named and cheaper: (E-pair)**, *two
adjacent degree-`2` vertices*, which is all `exists_adjacent_degree_two_pair_of_
edgeBound` consumes — and **(V) needs (E) only through the same branch-length
neighbourhood**, so W4's two non-user-call items now share one target. **A second
consumer that was never one:** *Step 0*'s `hfresh` sentence is true of the landed
*proof*, not the *obligation* — a residual is `Simple`, so `|E| ≤ |α|(|α|−1)/2`
discharges it at a larger `β` headroom; annotated at source (F12) along with three
over-statements in *Step 3*'s own (E-loc) paragraph. **Job 3's premise is void**
((E) did not land) and its substance is answered: (V) unchanged, holding outright
at `T32`. Driver `w4/weloc.py`, five modes — `--brick` runs (EL-4)'s chain on
**374** hub-cycle-carrying instances with shieldedness and `hcard(G/S)` asserted at
every step (**157** `j = 1` + **128** `j = 2` extensions taken, **0** failures,
**0** residuals). **Denominator disclosure: `0`, not `255`, and NOT (T)'s blind
spot** — 160 pool residuals carry no dependent set and 95 carry exactly one, so
**none** carries the configuration that decides the question; unlike (T), a sweep
*could* have seen this failure, the generator simply never built one.
`notes/check-gapmap-cells.py` **did not fire and was not skipped** (no W4 gap-map
row; none opened). **E1/E2/E3 do not fire — E2 came closest of any W4 landing**
(target refuted, but the successor IS specified, which is the clause it turns on);
**reported, not acted on**. Run at `recon-opus` (fable unavailable).
**WTRI (ordinal 58, §"WTRI") LANDED 2026-09-02** — the arc's **FIRST W4-side
direction**, and it **CLOSES A CARRIED COST: §(SAFE-RES) (T) IS A THEOREM** —
**HIT shape 1**, the one the spec ranked first; also shapes 3, 4 and 5, and **NOT
shape 2**. *A feasible residual `G` is triangle-free.* The proof is a two-case
contraction argument and it uses **no new mathematics**: `2EC` pins the pendant
triangle's hub at degree **exactly `≥ 4`** ((TF-2)), and the two **landed
feasibility TRANSFERS** — `PencilNondegFeasible.mono` at `deg z ≥ 5` ((TF-3)) and
`pencilNondegFeasible_induce_of_pendant_deg3` at `deg z = 4`, reached by deleting
**one** triangle vertex first so the hub demotes `3 → 2` across a single pendant
edge ((TF-4)) — make `G/Δ = G − x − y` feasible. That is a **good contraction**,
contradicting the residual. **The direction's own crux was an INVENTORY error, not
a hard theorem:** *Step 4*'s *"(T) is not provable from the landed set"* read
*landed set* as the feasibility **criteria** (L6b / L7c-3 / `hcard` /
no-two-hub-triangle) and missed the two **transfers**, which carry no
triangle-freeness hypothesis and therefore see straight past L6b's blind spot.
That claim is **RETRACTED AT SOURCE** (F12), and its consequence (ii) is
*sharpened* instead: the blind spot is **two-sided** — `G/Δ` inherits `hcard` and
inherits `≤ 1`-hub triangles, so **neither** verdict on the contraction can be
certified either. **Job 2 is DISSOLVED, not answered**: the two-pendant-triangle
structure the spec sent the direction at is **empty**, because no residual carries
even one triangle (so the bowtie dies at *every* `|V|`, not only `5`). **Job 3 is
MOOT and said so**: nothing is carried, nothing is relocated, and (V)'s
pendant-triangle residue is killed by a theorem. Consequences: route 3's cost list
drops **4 → 3** ((E-loc), (V), (K-res)); **(C8) collapses to case (A)
unconditionally**; and (V) is now the cheapest non-user-call item in the phase.
A **driver was shipped** — `w4/wtri.py`, three modes — but deliberately **not** as
a hunt: `--audit` checks the theorem's configuration on the blind-spot family
(**62 041/62 041** pendant triangles, 0 failures), `--validate` the mechanical
identities (same denominator), and `--regress` asks whether the by-product
one-plane certificate **(TF-6)** dissolves anything recorded — it re-derives
`saferes.py --prime`'s pool, reproduces its **255** exactly, finds **0**
triangle-carrying (as the theorem requires) and **0** dissolved, with `W19`/`S29`
intact. **The recorded 255/255 was never evidence and is not what settled this**;
the L6b blind spot is not a cap and no sweep removes it. Compiler-checked as a
composition in a deleted scratch spike; **four mechanical Lean obligations** (pure
degree/cut bookkeeping) remain for the W4 build, which the Lean hold still parks.
`notes/check-gapmap-cells.py` **did not fire and was not skipped**: there is no
gap-map row for the W4 side and this direction did not open one.
**TERMINATION E1/E2/E3, read against their (K)-arc definitions
(`notes/Pencil-fanout-archive.md`) and NOT by analogy.** **E1** (a g-flank) is a
§(K-grid) object and has no W4 instance; its nearest W4 reading — *an exhibited
object refuting the direction's target class* — would be a triangle-carrying
feasible residual, and none exists ((TF-5)). **Does not fire.** **E2** needs the
target *refuted or unprovable-as-posed*; it was **proved**. **Does not fire.**
**E3 is ARMED (by GBAL)** and this is the **first landing whose FIRST conjunct is
satisfied** — *the target is proven* — which is worth recording. Its **second
conjunct fails**: E3 needs every remaining ledger entry *adjudication-gated
rather than dispatchable*, and E3's own text names **W4** as an example of
adjudication-gated. That is no longer true of W4's residue — after (TF-5),
**(E-loc)** and **(V)** are dispatchable and need no adjudication (`notes/Phase39.md`
*Blockers*, standing since 2026-08-02), and the (BE-14) ranked list is dispatchable
throughout. **E3 DOES NOT FIRE — reported, not acted on.**
**A PENCIL event on the W4 side; `hK` untouched.** Run at `recon-opus` (fable
unavailable).
**BGENUINE (ordinal 57, §"BGENUINE") LANDED 2026-09-01** at **the price BONEONE
named in its own landing** — **HIT shapes 2, 5 and 4; NOT 1, NOT 3**.
**THE COINCIDENCE IS GENUINE, AND IT DOES NOT BITE.** (a) is settled by an
**argument, not a draw**: (BE-77)(ii)'s certificate `{v, b₁, b₂}` is a **HINGE
PAIR** — `v` and two of its own neighbours — and `binduc.assert_generic_star`,
the standing guard every landed measurement in this arc runs under, asserts
exactly that such a triple is affinely independent. So the aggressive operator
and the genuine one **agree pointwise** here; the over-claim is real in general
and **vacuous on this family** (1 836 of 1 856 admitting steps are hinge pairs,
372 of 392 whole derivations are, and the other 20 steps measure rank 3)
((BE-84)). (b) is **`0`**: at **392 / 392**, on exhibited exact-ℚ certificates,
`ρ̄₁ ∩ ρ̄₂ = 0` **as spaces** and **`H` ATTAINS** ((BE-86)). **The naive
shortfall reads `−1` at 100 of them, and that is a DENOMINATOR ERROR** —
(BE-22)(iii) holds *only when both pieces attain*, the gap-map row had dropped
the proviso, and with `a_i` the side's own attainment loss the criterion is
`dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6) + a₁+a₂`, met exactly. **The (CH-1) check is
answered `no`** at every member (girth `3` at 392/392, and at 648/648 of a
**new** `(10,5)` row at `n = 13` whose triangle-free sub-row is `648` pairs /
**0** forced) — and it **costs nothing**, because (BE-84) is pointwise and
(BE-86) is existential ((BE-85)). **Job 3 is VACUOUS** (no positive shortfall,
so the *On a future HIT* block does not fire), the enemy is **live as a
phenomenon and empty as an obstruction**, and half (B)'s residue is back to
**TWO** items ((BE-87)/(BE-88)). **Not a PENCIL event.** Run at `recon-opus`
(fable unavailable this session).
**BONEONE (ordinal 56, §"BONEONE") LANDED 2026-09-01** at **the whole of what
BSPREAD reduced job 2 to** — *can an R-node-shaped 2-cut peel have
`δ₁ = δ₂ = 1`?* — **HIT shapes 3, 2, 4 and 5; NOT 1**. **THE ANSWER IS YES, and
half (B)'s last general-position enemy is LIVE.** The question was never about
peels: `δ_i` and `rnode_shaped` are both **per-SIDE** and any two sides glue
((BE-79)(i)), so it asks whether ONE side can be R-node-shaped at `δ = 1` — and
a **9**-vertex `K₄`-skeleton side is, giving `WIT11`, an R-node-shaped peel at
`(1,1)` on **11** vertices (and `WIT16`, where **both** sides are
R-node-shaped, so the `and` reading falls too). **Both zeros behind the old
`no` are VACUOUS** ((BE-80)): such a side needs
`|V| ≥ 7 + min_s[5s + φ(q−p−1−s)] ≥ 9`, `= 9` **only over `K₄`**, so the peel
needs **11** — one **above** tier A's `n ≤ 10` — and **every** 2-cut of a
subdivided skeleton has a **PATH side**, `δ = min(L,6)`, never `1`, so tier B
had **0 chances at any cap**. The forcing test job 1 demands is **POSITIVE**:
**24 of the 48** `(1,1)` R-node peels on 11 vertices force `π_u = π_v`, **392
of 928** in all, every certificate exactly (BE-77)(ii)'s `{v, b₁, b₂}` split
`(2,2)` — so **(BE-66)(iv)'s CONCLUSION is REFUTED**, not merely unproved, and
its *load-bearing R-node hypothesis* corollary is a **size floor** ((BE-81)).
**The coordinator's route hypothesis is REFUTED and its own item (c) —
*test the generator artifact first* — is what produced the landing.** Job 2's
residue is **three** items, not two, and the price is that **genuineness** (the
aggressive operator over-claims) is now what stands between the enemy and half
(B) — **geometry again** ((BE-82)). Job 3: fifteen deep is a **de-facto shared
layer, not a device chain**; record, no move ((BE-83)(iii)). **(BE-32)(+),
(BE-73)(ii)(b) and (BE-77)(i)/(ii) untouched — the last CONFIRMED on the
witness; (BE-14) untouched; not a PENCIL event.** Run at `recon-opus` (fable
unavailable this session).
**BSPREAD (ordinal 55, §"BSPREAD") LANDED 2026-09-01** at the **SPREAD step**
((BE-32)(+) where (BE-41)(i)'s star-2 certificate does not apply) — **HIT shapes
1, 2 and 5, and shape 1 is the arc's first on this item**. **(BE-32)(+) is a
THEOREM**: a block `B` of an **optimal** partition absorbs at most **TWO** points
of any outside vertex's closed star — an edge route and a path route from `[v]` to
`B` make a triangle of `Q`, two path routes make a `4`-cycle, and two edge routes
coincide — and the closure admits on **THREE** ((BE-74)). The tool is
**(BE-39)(i), spent on the closure's own admission rule instead of on cycles of
`G`**, where BEARFULL spent it and where it runs out at `6`. So the **star-2 /
SPREAD split is RETIRED, not half-closed** (401 544/401 544 steps, 203 723/203 723
pairs, in the stronger *no optimal partition separates* form), (BE-32)(ii)/(iii)
are its `|B| = 1` case, threshold `2` **fails as it must**, and the coordinator's
closure-restriction hypothesis is **MOOT — its item-(c) scope change never paid**
((BE-75)). Job 0 **confirmed the coordinator in full** off the shipped driver and
annotated **five** surfaces ((BE-76)). Job 2: the closure **factorizes at a peel**,
so cross-cut-only forcing with both sides flexible forces **`δ₁ = δ₂ = 1`** —
BPEEL's 408 off-R-node positives are **408/408** exactly that, and its census-3
zero is **VACUOUS**, `0` of 24 874 at `(1,1)` ((BE-77)). **(BE-73)(ii)(b) and
BRULE's `π_u = π_v` corner become unconditional; (BE-14) untouched; not a PENCIL
event.** Run at `recon-opus` (fable unavailable this session).
**BPEEL (ordinal 54, §"BPEEL") LANDED 2026-09-01** at **half (B)'s CLASS
STATEMENT** ((BE-67)(iii)) — **HIT shapes 2, 4 and 5; NOT 1 and NOT 3**. The
spec's crux was **exhaustiveness**: two ways to fail are located and each
discharged, and nothing proved there is no third. The answer is that the
obligation is **retired, not discharged by enumeration**. The good locus is
**Zariski-open** on the irreducible `Chart(H)`, hence **dense or empty**, so a
failure is never a phenomenon at a special point and the whole question is the
value of **one generic invariant one exact-ℚ draw computes** ((BE-69)); and **no
topological branch crosses a 2-cut**, so at fixed flags `ρ̄₁, ρ̄₂` are functions
of **disjoint coordinate blocks** and the two sides share exactly **one datum,
the flag pair** — the achievable pairs are the full product, **modulo `G`**
((BE-70), MIX-measured 42/42). Together they bound what any mechanism can
*depend on*, so a third one could only appear as a **reach shortfall**;
completeness of the mechanism list is **not claimed** (F11), and the direction's
own Klein-**ruling** candidate is **examined and set aside** ((BE-71)). **Job 2
is CLOSED on (CH-1)'s class**: `G` empty at *every* flag ⟺ `Chart(H) = ∅`,
which (CH-1)(a) forbids ((BE-72)). **And one correction at source (F12):
(BE-66)(iv)'s stated REASON is refuted** — the landed *general* propagation rule
forces `π_u = π_v` at **non-adjacent** pairs (`K_{2,3}`) — while its
**conclusion stands**, from (BE-32)(+) + (BE-22)(vi); enumerated at **3 497**
forced R-node-shaped peels, every one with `min(δ₁,δ₂) = 0`, and **24 874**
both-flexible R-node peels, none forced. **That re-ranks the SPREAD step** as
the last gap in half (B)'s discharge. Landed at `recon-opus` (fable unavailable
this session).
**BDECOR (ordinal 53, §"BDECOR") LANDED 2026-09-01** at **the
ACHIEVABLE-DECORATIONS class statement** ((BE-62)(iii)) — BRNODE's successor
(1), taken after the coordinator re-ran the F26 consumer trace — **HIT shapes 1
and 2 at once, and there is no "past ears"**. The pencil condition is *every
closed star coplanar*, which at a hub is a **conjunction with one conjunct per
incident branch**, so at a fixed flag assignment the legal configurations of ANY
piece are a **product** of legal ear chains, one factor per **topological
branch**, **modulo the cross-branch proviso `G`** — disclosed, and never shown
nonempty in general ((BE-64)) — the per-child sets (BE-62)(iii) left open are
**never needed**, and the theta child falls out as a corollary with generic
`dim ρ̄ = max(0, Σ_j min(a_j,6) − 12)` and welded attainment **FREE**
((BE-66)). Job 2's hypothesis is **CONFIRMED and STRENGTHENED** (the freedom is
not the P-layer's, it is the pencil condition's); its weak link **(b)** (the
degree-3 terminal) is **harmless and provably so**, while **(a)** (the small-`m`
correction) is **real and does not stay inside its branch** — at `π_x = π_y` two
length-3 branches have EQUAL spans, `ρ̄` **exceeds** general position at 7 of 30
rows, and **7 of 7** of those are **non-attaining**, exactly what (BE-22)(iii)'s
hypothesis excludes. The residual coupling is the **flag base**, which is
§(K-chart)'s own tower — so (CH-1) supplies irreducibility, rationality and
dense ℚ-points already ((BE-65)) — and half (B) holds at **28/28** peels, 14 of
them peeling a theta child, **each row a per-piece theorem** ((BE-67)).
Dispatched at `recon-opus` — the mapped top rung with fable unavailable this
session.
**BRNODE (ordinal 52, §"BRNODE") LANDED 2026-09-01** at **the INTERNAL
R-NODE** ((BE-31)(ii)), the user's 2026-08-29 pick — **HIT shapes 1 and 3
at once**. Job 1's sharp question comes back **YES, by a proof**: a child's
whole boundary trace is `Δ ⊕ ({0} ⊕ ρ̄_e)` — a function of its `ρ̄` ALONE —
so `M(H)` restricted to `V(B)` **is** the motion space of the **decorated
skeleton** and the SP recursion **extends to a complete recursion over the
SPQR tree** (leaf line, `S` sums, `P` intersects, `R` the decorated kernel;
(BE-59)/(BE-60)) — (BE-31)(ii)'s residue **closed as a computation**, exact
at every configuration. The routing verdict (job 2, F26): the coordinator's
trace **CONFIRMED in its central clause** — the description was never what
the consumer is short of — with drawn (α)/(β) content **EMPTY** (24/24
both-flexible peels, criterion outright), so the R-node's residue is the
**achievable-decorations class statement**, the (BE-30)(ii)-analogue fibred
over the branch flags ((BE-62)). The carve-out is **negative with an exact
boundary**: the (BE-22)(vi) collapse is the checkable condition
`δ_{xy}(B − uv − e) = 0`, exhaustive at `n ≤ 6` — `K₄` passes exactly at the
disjoint edge, the **prism fails at two rungs**, so one flexible child
already suffices to leave no collapse peel ((BE-61)). The chord step is
priced the **strictly harder** coordinate for this obligation ((BE-63)).
**BWIN (ordinal 51, §"BWIN") LANDED 2026-08-29** at **the LAST ITEM in (β)** —
BSHARP's window identity `ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` as a **CLASS statement**, and it
came back as the spec's first deliverable shape: **the class statement PROVED,
by a uniform argument** ((BE-57)) — the double peel plus the **modular law**
reduce it to `W ∩ Z ⊆ ⟨ℓ_u, ℓ_v⟩` for the middle's own screw space `W`, the
ends act on `W` through **ONE hyperplane and ONE linear functional**, and
`δ₁ ≤ 4` is exactly the budget that one rank-1 functional can pay. **(b1)+(b2)+
(b3) hold at every window piece, so the ear case's (β) side is proved there on
the reduction's 87-of-91 domain**; job 3 shows the window is **NOT the
barbells** (theta chains and **R-node middles** are in it — "barbell" was the
sampler's reach), and job 2's observation lands **reframed**: no induction on
the middle exists anywhere — the middle enters as one arbitrary subspace.
**BRULE (ordinal 50, §"BRULE") LANDED 2026-08-28** at **(b3)** — *`ρ̄₁ ∩ E` is
not an opposite-ruling pencil*, the one clause of (β) never attacked, taken as a
deliberate deviation from BSHARP's successor order for the reason F26 records.
**HIT shape 1: (b3) is DECIDED — PROVED on its honest domain** by a
**separation theorem** ((BE-50)): `Π_u` and `Π_v` are members of the very ruling
`y ∧ L` lives in, so a failure either refutes (b1) or forces the sharpening at
**both** ends — and since (BE-45)'s mechanisms make the sharpening fail exactly
where the window lives, **(b3) holds throughout the window and (β)'s two
obligations are DISJOINT**. It also **corrects an inference of (BE-37)(ii)** —
*"(b3) ⟹ `lossR = 0`"* is false, `lossR ≤ lossZ` holds instead — with the
**conclusion, the 91-case enumeration and every landed measurement UNCHANGED**,
because the reduction bounds `loss` by `max(lossP, lossZ, lossR)`. The routing
question came back **CONFIRMED and extended to a third clause**, with the escape
**splitting**: (BE-32)(+) is load-bearing on the **forced** branch only. **(β) is
now down to BSHARP's window ALONE.**
**BSHARP (ordinal 49, §"BSHARP") LANDED 2026-08-28** — the ear case's **last
(β) clause**, and **HIT shape 2 with a refutation attached**: the sharpening
**`ρ̄₁ ∩ Π_u = 0` IS FALSE**, at an exact **DICHOTOMY of two identities** — a
**series end** (every `u–v` path leaves `u` by one edge, so (BE-31)(i) puts
that hinge line in `ρ̄₁`) or **path saturation** (`δ₁ = min_P dim⟨P⟩`, so
(BE-30)(iv) is an equality of spaces) — **0 mismatches over 49 pieces**. The
second mechanism needs **no** hypothesis on the first edges, so it **CORRECTS
(BE-38)(iii)'s prose clause** *"`0` wherever two `u–v` paths leave `u` by
different edges"* at six of BEARFULL's own landed `bgrass` rows, and with it
(BE-42)(iii)'s implied sufficiency — **no measurement changes**. The
coordinator's reduction is **sound and decouples**, but its limit is
`dim⟨P⟩ ≤ 5`, a **dimension count, not a proviso**; the **genericity proviso IS
DISCHARGED** where the sharpening is available (openness + irreducibility ⟹ one
exhibited witness proves a shape's stratum). **Every failure case discharges
(b2) by an already-landed route except ONE named window** — series at **both**
ends with `δ₁ ≤ 4` — where **(b2) ⟺ `ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩`**, exhibited 5/5;
reaching that window needed job 3's **first parametrization past bearcase's
shape guard**. **(β) is at (b3) plus that window**, not (b3) alone. **RESGRID (ordinal 48, §"RESGRID") LANDED
2026-08-28** — the **(K-res) scoping slice**, user-selected 2026-08-26: *does
(GR-15)/§(K-grid) transport to the `W19`-type (K-res) habitat?* **HIT shape 3,
partial transport with the boundary a step number**: the §(K-grid) **geometry
transports verbatim** and the (K-res) grid residual is **(RS-5)** — (GR-15)'s
criterion with the quantifier widened, **proven per-shape at `W19`/`S29`/
`NT21c3`** by exact rational target points — while the tight bookkeeping
((GR-16)(iv)/(GR-17)(d)/(GR-18)(i) first, then the whole (GR-21)+ uniformity
program) does **not**, and the deficient fringe is **refuted with a mechanism**
((RS-6): θ(2,3,7) provably capped at 58 < 59, exhaustive). The gap map's
umbrella sentence (*"one uniform gap serves both"*, standing since 2026-08-02)
is **CORRECTED** and §(K-res) gets its own row; the **wave stays a user call**. **BEARFULL (ordinal 47,
§"BEARFULL") LANDED 2026-08-27** — the merge inequality's real theorem is a
**SHORT-CYCLE LAW** (`girth(Q) ≥ 6`, so every cycle of length `≤ 6` forces
`δ = 0`), which **CONTAINS** (BE-32)(ii)/(iii) — **weakening** the latter's
hypothesis — and proves **(BE-32)(+) at 196 043 of 203 723** forced pairs;
**`δ = 0` is an EQUIVALENCE RELATION** by a supermodularity/join lemma; **(b2) is
a COROLLARY of (b1)**, so the ear case's (β) side loses a clause; and the
**coordinator's ear-decomposition routing hypothesis is REFUTED BY A THEOREM** —
every minimum-degree-`≥ 3` graph forces a single-edge ear, so the chord gap sits
exactly at the R-nodes it was meant to retire. **S-mark's pin STANDS.** **BEARCASE (ordinal 46,
§"BEARCASE") LANDED 2026-08-27 — HIT shape 2: (α) IS CLOSED.** The greedy's last
step is a **complete criterion** (the 2-step lemma), its bad case is non-empty
but a **scheduling artifact**, and a **reordering plus a slide** removes it — so
**(BE-33)(ii)'s reach formula is PROVED for `m ≥ 3`**, discharging BIMAGE's
headline cap. **(β) as stated is REFUTED** — unsatisfiable at `δ₁ ≥ 5` by plain
Grassmann, a **prose defect that propagated** from BIMAGE's successor ranking
into this direction's own spec and the phase note; the correct target is what
the landed driver already tests, so **no measurement changes**. Its *"every
configuration"* quantifier **collapses**, and the ear case's (β) side is down to
**one named residue, (BE-32)(+)**. **BIMAGE (ordinal 45,
§"BIMAGE") LANDED 2026-08-27** — BTWOCUT's *"nothing in the arc bounds that
image"* is now **FALSE**: for the **ear** the image is described **exactly** as
the span of a **chain on the Klein quadric** (a *bijection*, the coordinator's
hypothesis **CONFIRMED and strengthened**, with three confinement laws it did
not predict), its bad locus is **classified into exactly three mechanisms** —
each a *proved* lower bound, exactness **MEASURED** — and every trap a real
piece shows is a **configuration artifact** (607/607 escalated). Off the ear,
`ρ̄` obeys an exact **series/parallel recursion** that **REFUTES** the
coordinator's candidate path-intersection bound as an equality and leaves the
**internal R-node** as the residue. **The ear case is REDUCED, not proved;
(BE-14) OPEN and unchanged.** **BTWOCUT (ordinal 44, §"BTWOCUT") LANDED 2026-08-26
— HIT shape 2, delivered in full: the strengthened statement is **PINNED**
(S-mark closes; S-all does not, and its one gap is named), the simultaneity worry
is proved **VACUOUS**, a new elementary theorem makes the leaf base free,
BINDUC's 56 ear misses are **cleared as a constructor artifact**, and the
general-position half **dissolves on everything swept** (16/16; hunt empty at
13 484). **(BE-14) is NOT proved** — the step reduces to one geometric sentence,
the first genuinely geometric obligation the arc has reached.** **BINDUC (ordinal 42, §"BINDUC") LANDED 2026-08-26 —
the biggest single advance the arc has made on the phase target: the induction's
**BASE IS FREE** (3-connected ⇒ `def₂ = 0`, so the declined `def₂ = def₃` slice
covers the whole base), BZAVOID's asserted 2-cut `− 6` is **REFUTED** and replaced
by an exact `max`-law, and **(BE-14) is reduced to ONE named composition lemma**.
It also **scope-corrects (BE-15)(ii)**: the general forcing rule needs no triangle,
so BZAVOID's cap-free closure covers the triangle mechanism only.** **ZJACOB (ordinal 43, §"ZJACOB") LANDED
2026-08-26 — (ZH-4) **REFUTED by an EQUIVALENCE**, not an obstruction: the corank
stratification makes *"LCI of the expected codimension"* ⟺ `B_0 ≠ ∅` ∧
`codim B_k ≥ k`, and `B_0 ≠ ∅` **IS** properness, so the route's hypothesis
contains its conclusion as its weakest clause. Its refutation **absorbs (ZH-3)**
— the shelf's two "concrete" candidates were one — leaving §9 with exactly one
dispatchable candidate, (ZH-2) stratified. Both coordinator-predicted deaths were
refuted **as diagnoses**.** **BZAVOID (ordinal 40, §"BZAVOID") LANDED 2026-08-26 —
the spec's commissioned falsification arm came back **EMPTY BY AN ARGUMENT at
every graph** for the **triangle**-forced mechanism (scope-corrected at the
BINDUC landing: the general forcing rule needs no triangle, and is closed only as
measured), so BATTAIN's triangle-free premise is a special case and not the
reason; the pencil stratum is **IDENTIFIED as the planar-atom molecular
stratum**, making (BE-14) **existential rather than generic**; and **two routes
are CLOSED** — the landed Phases-24–26 `G²` apparatus (gate is the literal
negation of the pencil condition, dictionary gaps 5/4/1) and the coordinator's
own transversality count (structurally incapable). (BE-14) reduced to
2-connected graphs and still OPEN; `hbareSplit` untouched; nothing refuted, not
a PENCIL event.** **ZSHEAR (ordinal 41, §"ZSHEAR") LANDED 2026-08-26** — the
session's side line and the **first direction strategy §9's external-technique
shelf has ever produced**, and it came back a **negative HIT by a
computation-free identity**: the Witt shear **is** the translation subgroup of
`PGL(4)` on line coordinates (`Φ_S = Λ²(T_{−s})`), `Q` is its **own defining
invariant**, and the §(K-tight) criterion matrix is **literally the same matrix**
in the pushed basis — so (ZH-1)'s mechanism is **vacuous** and the candidate is
**STRUCK** from the shelf, by gauge-triviality rather than §4.6's predicted
growing-ground-set death. The coordinator's offered per-body repair was decided
negative in both readings; the owed §2.5 filter check on (ZH-2)/(ZH-3) is
**DISCHARGED**. **BATTAIN (ordinal 39, §"BATTAIN") LANDED 2026-08-26 —
the arc's first direction ever aimed at `hbareSplit`, and it paid: the motive
characterized off the Lean bodies, bare realizability proved UNCONDITIONAL,
the first universal pencil-stratum rank cap produced BY AN ARGUMENT, the
standing "no T2 producible by this harness" reading CORRECTED, and 774/774
deterministic attainment certificates with zero shortfalls. `hbareSplit` OPEN
and unchanged; not a PENCIL event.** **OGEOM (ordinal 38, §"OGEOM") LANDED 2026-08-26 — NO
disproof witness (91 260 live cores, 0 candidates), and the geometric route
is now free BY AN ARGUMENT on everything searched, with (OC-37)(ii)'s
one-unit topology dead class-uniformly and (OC-39) upgraded from sample to
theorem. §8.5's row NARROWS but does NOT close: `n(F°) ≥ 6` was never
searched.** **GMINM (ordinal 37, §"GMINM") LANDED 2026-08-26 with
the arc's most consequential routing finding: GHWIT's refutation DOES NOT
REACH THE LEDGER.** (b′) has three pairwise-inequivalent readings; the ledger
consumes the **difference of minima**, the `min_M` reading is now PROVEN, and
the per-matching reading the last four directions attacked is the one the
consumers never used. **GHWIT (ordinal 36, §"GHWIT") LANDED 2026-08-26, same
day as its dispatch — a REFUTATION BY WITNESS that goes one clause past the
spec's headline case: the half-witness clause (GR-117)(iii), the gap-2 law
(GR-117)(i) AND **(GR-104)(i) at `2k = 2` itself** are all FALSE at an
explicit habitat-gated `n_hub = 20` all-(2,2) pair of gap 4 — so
**per-matching (b′) at the constant 2 is FALSE** and (GR-86)'s gap-4 cap is
TIGHT — while a second independent finding corrects a landed boundary:
(GR-108) is false from `n = 12`, exactly, not `n = 16`. The first single
direction to run below the top rung (`recon-opus`, fable conserved), and it
hit.** **GXESC (ordinal 35, §"GXESC") LANDED 2026-08-26, same
day as its dispatch — a REFUTATION BY WITNESS, the spec's strong form:
(GR-108), the balance law, is FALSE from `n = 16` (four verified witnesses,
the first one transposition from GBLAW's strand witness) and existential
escape falls with it — while **(GR-104)(i) SURVIVES at every witness** (⟺
the gap-2 law, proven except at the all-(2,2) case, measured empty at 248
pairs); the reshaped residual is the **half-witness clause** (GR-117)(iii).** **GBLAW (ordinal 34, §"GBLAW") LANDED 2026-08-26, one
day after its 2026-08-25 dispatch — an honest OPEN reshape: (GR-108) neither
proven nor refuted, the exchange calculus its pinned proof shape called for
PROVEN in three theorems ((GR-110)–(GR-112)), the law reduced to
**existential escape** (0 failures at 1 099 swept pairs), universal escape
REFUTED at an explicit `n = 16` witness that defeats both new mechanisms
exhaustively at that pair.** **GPRICE (ordinal 33, §"GPRICE") LANDED 2026-08-25, same
day as its dispatch — a graded outcome of the third kind: (GR-104)(i) is a
theorem at `2k = 2`, every `n`, modulo the minted balance law (GR-108) alone
(measured 1 431/1 431, `n ≤ 6` sub-cell exhaustive, hunt empty to `n = 18`),
via the reversal-set normal form (GR-106) and reachability theorem (GR-107);
residual (GR-108) + the `2k ∈ {4, 6}` `O ⊄ M` corner.**
**OQRANK (ordinal 32, §"OQRANK") LANDED 2026-08-25, same
day as its dispatch — a graded HIT of the first kind: the ⋆-eigen-block
mechanism completed, the naive single-colouring form REFUTED as a class
statement (27/174, incl. the (OC-42) WALL), and the hunted form GREEN —
**input (a) holds at all 174 certified classes**, per-class-generic, with
zero (K-tight)-event rulings.** **GCHEAP (ordinal 31, §"GCHEAP") LANDED 2026-08-25, same
day as its dispatch — a graded double outcome: (GR-C2)'s every-step form
PROVEN for `n_hub < 6|δ|` via the lone-dart capacity (GR-100)/(GR-101), so
**(b′) at the constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum**, and
its per-configuration form REFUTED from `n_hub = 12` by an explicit witness
(GR-103), the boundary exact both ways; the as-posed existential survives at
every audited pair and the residual is reshaped to (GR-104)(i), the price
form.** **GFLIP (ordinal 30, §"GFLIP") LANDED 2026-08-25, same day as its dispatch —
a HIT of the first kind: (GR-R1) is PROVEN**, strengthened to the selection theorem
(GR-99) (`≥ |δ|` feasible majority flips, no habitat/`2k`/connectivity hypothesis), so
(b′)'s `n`-free `≤ 12` bound (GR-89)(ii) is now a **theorem** and (GR-C2) is the whole
constant-2 residual. The seventh fan-out (YLOC / BALB / AGLU / ZNEQ /
CIRR, §"Seventh fan-out") is
**COMPLETE** — all five directions landed 2026-08-19. The **EIGHTH fan-out** (GTMPL / GFLOW /
GCOLL / OSCHU / SIGZ, §"Eighth fan-out") is **COMPLETE** — all five landed 2026-08-19: an
exact `n_hub` boundary for ledger attack (c)'s AA-glue case (GTMPL), (b′)'s first proven
`n`-free constant (GFLOW), a **NO HIT** on the authorized disproof hunt that nonetheless
kills the counting route to a disproof (SIGZ), (a₁) reduced to one determinant (OSCHU), and
**(GR-64)(R2) REFUTED** with (R1) delivered (GCOLL).
Ordinals run 1–41 (the eighth fan-out claims 25–29; GFLIP is 30; GCHEAP is 31;
OQRANK is 32; GPRICE is 33; GBLAW is 34; GXESC is 35; GHWIT is 36; GMINM is 37; OGEOM is 38; BATTAIN is 39; BZAVOID is 40; ZSHEAR is 41; BINDUC is 42; ZJACOB is 43; BTWOCUT is 44) and were assigned at dispatch, so landing order
differs from ordinal order.

**The two architecture-testing PROBES are also both LANDED** (§"Two probes SPECCED and
AUTHORIZED 2026-08-20"). They carry **no ordinal** — they test the architecture rather
than the (K) crux, so they are outside the direction/ordinal count. **KBARE-FALSIFY**
(2026-08-20): a **HIT at tier T1**, (K-bare-ext) refuted as stated, `hbareSplit`
untouched. **C3-AVOID** (2026-08-24): the *"reduce avoiding `S`"* gate **decided** —
universal threshold **exactly `|S| ≤ 2`**, exact ceiling `2 μ(G)`, so board option **C3
is NO-GO as a crux-avoidance route**; mathematics in `notes/Pencil-strategy.md` §4.7,
§(K-avoid) never opened, **no gap-map status moved**.

**Ordinals 1–19 are archived** (2026-08-19, `notes/Pencil-structure.md` slice 2) —
their dispatch specs and landing write-ups moved verbatim to
`notes/Pencil-fanout-archive.md`. This file keeps the adjudication, the *Shared
mechanics*, the *Landing checklist*, and the seventh fan-out (ordinals 20–24) as
the worked exemplar a future wave copies from.

**What this file is:** dispatch scoping only — the specs, bars, riders, tier splits and
label reservations a direction is dispatched against, plus the per-direction landing
write-ups. It remains the **template for any future fan-out or single direction**. The
mathematics lives in `notes/Pencil-informal.md` (the (K) workbook — start from its *State
of (K)* gap map, which is authoritative for every status word). Label reservations and the
minting rule live in `notes/Pencil-labels.md`.

**Selection provenance is NOT duplicated here.** Which user adjudication or delegation
picked each direction is canonical in `notes/Pencil-adjudications.md`, as dated bullets
quoting the user verbatim (ordinals 1–44, moved out of `notes/Phase39.md` *Current state*
in two rounds, 2026-08-19 and 2026-08-26), and in each direction's own section below.
`notes/Phase39.md` *Current state* keeps only the **standing** GO/NO-GO constraints and a
compressed statement of the delegation and its selection criteria. Do not restate it in
this header — reproducing it is what grew this header to 2 139 words of changelog across
thirteen directions, stale by two whole fan-outs, and still describing the file as scoping
"three independent research directions" long after there were twenty-four.

## The adjudication that produced this

**2026-08-05, verbatim:** *"I still think we should hold off on doing more Lean
until we have an informal proof or disproof or any results that would be
significant as standalone pieces of math."* — so the W4 build stays parked
**even though it is fully decomposed and buildable**; the phase's next work is
research, and the bar is *standalone-significant*, not merely
progress-toward-(K).

**Same day, verbatim:** *"Since we're running opus, we don't have to worry quite
as much about token usage (except for the context of the coordinator). I think
we can potentially send off a few parallel research agents if there are a few
independent direcitons worth exploring"*, then, on the reorg-first question:
*"Let's do the rewire; I'm now thinking we should make the rest of this session
a planning / prep session and then do the actual fan-out in a fresh session
after this one."*

Standing kernel adjudications are **unchanged**: `hK` and `hbareSplit` stay
carried as pinned; option B (the stress-as-chart-rational-function
infrastructure) is **NOT** commissioned; W4 route 3(b) is recorded, parked.

## Shared mechanics (all three dispatches)

Rung: each is a research recon settling new mirror mathematics → **top rung**
(`recon-fable`; `recon-opus` when fable is unavailable, as in the session that
prepared this).

**Parallel dispatches must not collide on the working tree.** All five prior
research passes committed to the same files. So:

- Dispatch all three **un-named** and in parallel, as **read-only w.r.t. every
  shared file**. Each one **commits NOTHING**.
- Each may **create its own new** exact-ℚ driver at a pinned path — A:
  `notes/scripts/w4/flanks.py`, B: `notes/scripts/w4/lambda.py`, C:
  `notes/scripts/w4/pure.py` — importing the harness read-only. New files
  never collide; leave them untracked for the coordinator to gate and commit.
- Each writes its full mathematics as a **draft workbook section** to the
  session scratchpad (not the repo) at `fanout-<A|B|C>.md`, in the workbook's
  register, with an explicit confidence verdict
  (proven-informally / true-modulo-named-gap / open / refuted) and a "what
  would change this" line. Keep the **return message** to a tight verdict —
  the coordinator's context is the binding constraint this session, not tokens.
- **No agent edits** `notes/Pencil-informal.md`, `notes/Pencil-W4-informal.md`,
  `notes/Phase39.md`, `notes/Phase39-design.md` (frozen), or any existing
  script. The coordinator verifies each return and lands them **serially**,
  one commit per direction, merging the draft into the workbook and updating
  the *State of (K)* gap map row.

**Label non-collision — the document-side analogue of the tree-side mechanics
above** (added 2026-08-05, after the reorganization pass). The mechanics in this
section stop three concurrent dispatches contending for *files*; they do nothing
about three concurrent dispatches minting the **same label**, which is the
failure that produced the (C6)/(C7) fixup `86d77894`. So each direction of a
fan-out gets a **reserved label prefix and a reserved section name**, allocated
in **`notes/Pencil-labels.md`** *Reserved namespaces* and verified 0-hit across
the tree before dispatch. A dispatch prompt names its prefix; the draft uses it
for every label it mints; the coordinator can then land three returns serially
without a rename. `notes/Pencil-labels.md`'s four-clause minting rule binds every
dispatch — in particular, **qualify every citation of a label you did not mint**
with its owning section.

**Every dispatch carries these, from `notes/scripts/README.md`:** exact ℚ only;
degeneracy guards plus a rank/dimension assert on every sampled object (the
`plane_basis` precedent — a degenerate sampler silently contaminated several
passes' recorded escape-failure figures); seed all randomness; import from the
canonical layer, never reimplement (see the README's *Divergences* table for
the same-name-different-semantics traps).

> **The protocol has now been exercised twice, and the second time at a NEW
> shape (2026-08-05, second research day).** Three read-only recons ran
> concurrently with **one *committing* dispatch**, all four in a **single working
> tree**, with **zero collisions**. The general rule this exercises (serial
> coordinator landing; worktrees deliberately not used, and why) is promoted to
> **`RESEARCH-ARC.md`** §2 — read there, not here.

**And the F11 requirement** applies (dispatch-log): *each headline claim needs
a driver that tests that sentence*, with "forced"/"exhaustive"/"the only"
their own claim class. General statement and rationale: **`RESEARCH-ARC.md`**
§4 / `notes/dispatch-log.md` **F11** — not restated here.

## Landing checklist (coordinator, per returned direction)

1. Re-run **every** driver the draft cites, plus its headline **figures** — not
   just its `--validate` mode (dispatch-log 2026-08-02: a transcription error
   in a headline figure surfaced only when a later pass re-ran the pool).
2. Ask of each "proven piece": **which driver tests this sentence?** (F11.)
3. Check the draft against the sections it touches for the
   claims-stronger-than-its-own-named-gaps defect.
4. Merge the draft into `notes/Pencil-informal.md`, update the matching **State
   of (K)** gap-map row(s), add a one-line *Decisions made* entry to
   `notes/Phase39.md`, and commit the new script in the same commit.
5. Keep `notes/Phase39.md` forward-weighted and under its line cap — **now
   machine-gated: run `python3 notes/check-phase-note.py` (default mode)
   before committing**, alongside `check-gapmap-cells.py` for the row. The gap
   map is the canonical home for (K) status, so the phase note's kernel
   bullets stay thin pointers.
6. **A draft's closing *"Coordinator actions at landing"* block is
   scaffolding, not mathematics: execute it, then STRIP it — it must never
   be merged into the workbook.** Merged, it reads as an outstanding to-do
   list for work already done and will mislead the next reader into
   thinking status moves are pending. Also *audit* it while executing:
   verify each named action in tree (registry, gap map,
   `notes/scripts/README.md` §3, reserved namespaces) rather than assuming
   it was done — nothing here is gated. Four consecutive landings (E, TCOL,
   GCAP, GUNIF) merged the block verbatim, caught only by the coordinator's
   post-GUNIF verification sweep (2026-08-13). **Exact parallel to item 2 of
   the fifth fan-out's landing block** (the `notes/scripts/README.md` §3
   invocation rows), which was itself added after four consecutive landings
   skipped it — the recurring shape is a per-landing chore that no gate
   covers, so the checklist is the only mechanism.
7. **Sweep the four status surfaces as one deliberate pass**, not as a
   side effect of editing the prose around them. They go stale
   independently, they contradict each other when they do, and no gate
   covers any of them: **(i)** `notes/Phase39.md`'s top `**Status:**`
   header block — the COMPLETE roster, the date range, and its
   "next concrete task" sentence; **(ii)** the *Hand-off* next-task slot
   at the top of that section — **re-aim it, never delete it**;
   **(iii)** *Current state*'s (K)-arc paragraph — the dispatch count,
   the strategy-pass count, the date range; **(iv)** the ROADMAP Status
   cell (thin: marker + one clause); **(v)** **this file's own top
   `**Status:**` header** — the per-direction roll call, added at the
   fourteenth's prep (2026-08-18) after GPSA's landing updated its
   section's Status to LANDED and left the header still calling the
   same direction "PREPPED … not yet dispatched", the fifth instance of
   the shape and the first in *this* file. Three consecutive landings each
   missed a *different* one — GEXIST the ROADMAP cell, GORIENT the
   Hand-off slot (deleted with the prep text it replaced), GDEV the
   Status header — each caught only in coordinator verification, each
   costing a follow-up commit. Third instance of the same shape as
   item 2 of the fifth fan-out's block (`notes/Pencil-fanout-archive.md`) and item 6 above (dispatch-log
   F17). The generalization worth carrying: **a document's own header is
   a status surface, and it is precisely the part a section-scoped edit
   does not re-read.**

---

## Seventh fan-out — prepared and dispatched 2026-08-19 (directions YLOC / BALB / AGLU / ZNEQ / CIRR)

Five directions dispatched **concurrently** — **YLOC**, **BALB**, **AGLU**,
**ZNEQ**, **CIRR** — each independent, each returning its own untracked draft
(`notes/Pencil-draft-<CODE>.md`) and its own new driver, landed one at a time by
**separate serial coordinator commits**: the sixth fan-out's shape, repeated at
five directions. **User adjudication authorizing the multidispatch** — asked at
the session-start check-in how the twentieth direction's pick should be made
(delegate to a fable recon / coordinator-authored prep / multidispatch again /
coordinator picks under the standing 2026-08-07 delegation), the user elected
**"Multidispatch fan-out again"**, over a coordinator recommendation *against*
it on a 92 % `weekly_scoped` reading — then supplied the fact that overturned
the recommendation: *"weekly_scoped is only for fable so multidispatch should be
OK."* Same check-in: **rungs `sonnet` + `opus` only, top rung = opus** (fable
conserved), cap **lifted**, rescue §1 fixups **pre-authorized**. The **tier
split**, the **five directions themselves** and their **disjoint label
reservations** are **coordinator-set** — so the twelfth direction's disclosure
applies verbatim: *there is no independent top-rung ranking of the losers this
wave*, and a future top-rung recon may overturn the bars below freely.

**Roster** (updated per landing):

| direction | tier | target | status |
|---|---|---|---|
| **YLOC** | compute-licensed | input (Y), (a′)'s residual — GBAL's instrument localized to proper chunks | **LANDED 2026-08-19** — an honest MISS (§"Twentieth direction") |
| **BALB** | compute-licensed | (b′), the balance-layer bound `d_adm − d_par ≤ 2` | **LANDED 2026-08-19** — OPEN, NOT a HIT, half proven / half refuted with an exact boundary (§"Twenty-first direction") |
| **AGLU** | compute-licensed | ledger attack (c) — AA-glue realizability at `n_hub ≥ 8` | **LANDED 2026-08-19** — a HIT on the "not realizable" branch (§"Twenty-second direction") |
| **ZNEQ** | compute-licensed | (OC-19) input (a) — `Z ≠ ∅` at every class (shape, split) | **LANDED 2026-08-19** — OPEN, NOT an independent gap; it factors and one half is dominated (§"Twenty-third direction") |
| **CIRR** | derivation-first | chart irreducibility, written down once as a standalone statement | **LANDED 2026-08-19** — a HIT (§"Twenty-fourth direction") |

**Shared mechanics: §"Shared mechanics (all three dispatches)" above binds
verbatim**, at five directions instead of three, with three deltas. (1) Drafts
go to **`notes/Pencil-draft-<CODE>.md`, untracked** (the sixth fan-out's
convention, not the first's scratchpad path) — the coordinator merges and
deletes. (2) The rung is **opus**, not fable: the mapping for a research recon
settling new mirror mathematics is top rung, and top rung this session **is**
opus. (3) Each direction runs the **TERMINATION check (E1/E2/E3) and reports its
reading**; the coordinator re-runs it. **E3 is ARMED** by GBAL's entry-5 HIT, so
**YLOC can fire it** — a direction that believes it has an (a′) HIT says so and
states the E3 consequence, and does **not** fire it: firing is a coordinator
action.

### The coordinator's one routing sharpening, recorded because it overrides a landed hand-off clause

GLAW's *Step G79* hand-off recommends attacking input (Y) *"with
matching-flexibility instruments (alternating-cycle toggles on the `M`-avoiding
coset space, whose affine structure and dimension `n/2 − 1` are now exact)
rather than with local exchange."* **That clause was written blind to GBAL**,
which landed the same day in the same wave and discharged (Y)'s sibling **input
(X)** by an instrument that **absorbs the matching apparatus whole** — (GR-49)
replaces the (c, m)/coset/SDR/matching data by **one bit per branch**, (GR-50)
turns the question into a **degree-constrained orientation**, (GR-51) prices it
by a **local weight inequality**. Since (GR-56)(iv) makes (X) and (Y) the
whole-graph and proper-chunk instances of **one** inequality, the first thing to
try on (Y) is **GBAL's instrument at the chunk level**, not GLAW's suggested
toggles on the object GBAL's instrument dissolves. **YLOC is specced on that
reading**, and GLAW's clause is thereby **overridden as a routing
recommendation** — not contradicted as mathematics (the coset space's affine
structure and dimension stay exactly as (GR-55) Cor. 1 landed them, and remain
available as a fallback if the localization breaks). Same kind of override as
GPSA's of GADM's shift-metric routing clause: recorded, scoped to the routing
clause alone, and traceable.

## Twentieth direction — YLOC (seventh fan-out)

**Status: LANDED 2026-08-19 — an honest MISS, with substantial positive
content.** Second of the seventh fan-out's five directions to land, after
CIRR; one of **five** concurrent directions (BALB/AGLU/ZNEQ still in flight),
**compute-licensed** tier. §(K-grid) **extended**, **Steps G80–G85**, labels
**(GR-61)–(GR-66) CLAIMED exactly** — the full reservation consumed, nothing
returned to the pool (`(GR-64)(R1)`/`(GR-64)(R2)` are sub-items of (GR-64),
not separate mints). Driver **`notes/scripts/w4/yloc.py`** (seven modes;
`--validate` runs all seven but exceeds the 600 s foreground budget at
~890 s, so the landing gate ran three invocations instead: `--loc` alone
(274.7 s, coordinator-reproduced at landing), `--coll` alone (359.0 s,
coordinator-reproduced), and the remaining five modes together (139.7 s,
coordinator-reproduced) — `notes/scripts/README.md` §3).

**The target — input (Y), (a′)'s named residual ((GR-60)), verbatim as landed:**
*at every habitat shape there exist a perfect matching `M`, a minimum-weight
`M`-avoiding representative `y ∈ Φ`, and an injective end-selection `φ` of
`supp(y)` — together with, when `d_adm > d_par`, an `M`-avoiding matching `Z`
disjoint from `y` with `|y| + 2|Z| = d_adm` and `φ` avoiding `V(Z)` — such that
the resulting minority map `m` is balanced and satisfies, for every proper chunk
`S`, `z_mono(S) + |δ_S − σ_S| ≤ cap(S) − 6`.* (a′) is the only remaining
entry-1 attack, carries **no bar**, and is **the only thing between the arc and
E3**.

**The route to try FIRST (coordinator-pinned; the sharpening above):** push
GBAL's (GR-49)–(GR-54) chain down to the chunk level, in three steps.

1. **Re-express the (GR-56) chunk invariants `cap(S)`, `z_mono(S)`, `δ_S`,
   `σ_S` in (GR-49)'s one-bit-per-branch coordinate `z`.** GBAL proved the
   *whole-graph* instance is `δ = 0` at a balanced `z`; the question is what the
   *per-chunk* instance becomes in `z`. (GR-56)(v) already says
   admissibility and full-goodness are functions of the minority map alone, and
   (GR-49) says the minority map is `z` — so the translation should exist.
2. **Ask whether (GR-50)'s degree-constrained orientation acquires per-chunk
   in-degree constraints**, and whether **(GR-51)'s local weight inequality has
   a per-chunk analogue whose only negative term is again a
   monochromatic-pair hub.**
3. **If it does, whether (GR-53)'s exhaustion over maximal constraint
   structures still closes** with the chunk constraints added — the structures
   were 1 / 44 / 4837 at `2k = 2/4/6`, so an enlarged exhaustion is a
   compute question, not a new idea.

**The obstruction to expect, and to report exactly if it bites:** GBAL's
argument is whole-graph-only because **(GR-52)'s parity contradiction uses
`2 e_H(S)` over the whole side** — a violating hub set would have odd total
internal even-degree. At a *proper* chunk that global count is not available.
If the localization breaks there, say so in those terms and name what would
replace the parity contradiction; that is a more valuable return than a
measurement.

> **REFUTED as stated — see (GR-63)(i), recorded rather than deleted.** The
> predicted obstruction was **wrong**, and YLOC's refutation is **correct**:
> in (GR-52)'s landed proof `S` already ranges over **hub subsets** (the
> two-sided Hall violator), not chunks, and `Σ_{v∈R} a_v = 2 e_H(R)` is a
> **per-subset** double count valid at *every* `R` (305 704 pairs, 0
> failures). (GR-52) would localize for free. The chain breaks two links
> **earlier**, at (GR-50)→(GR-51): full goodness is not a function of
> `(odd pattern, in-degree vector)`, because in-degree fixes the majority
> colour `c(v)` and both chunk terms read the minority-dart identity `m(v)`.

**Calibrating opening cases** (GLAW's measurements, *Step G79*): the **965**
stratum shapes whose worst optimal cell needs the `M` rung, and the **13**
shapes at balance gap 2.

**Bars.** Do **not** re-attack (a′)'s **per-matching** variant — **REFUTED**
((GR-59): `min_M` is load-bearing, no (a′) proof may fix its anchor matching).
Do **not** re-run the bounded {T1, T2} descent (**DEMOTED by witness**,
(GR-48)(iii)) or the extended {T1, T2, K3} catalogue. Do **not** re-derive
(GR-58)'s census — it is landed and **exhaustive** at `n_hub ≤ 6` with no cap;
extend it only if a genuinely new stratum is needed, and disclose the cap if so.
**(b′) is BALB's target this wave** — report any (b′)-relevant by-product as a
finding and do not develop it (GBAL's precedent with (a′)).

**Riders, verbatim.** `Λ = ∅`, `D = 0`, and modulo (GR-4′) where a closure chain
is concerned; the `Λ ≠ ∅` closed-form analogue and the `D > 0` lift stay
**unswept**; **none of this closes (GR-15)**; an (a′) HIT **fires E3** (ARMED by
GBAL) — state the consequence, do not fire it.

**The verdict, as landed: the localization FAILS and (Y) is NOT discharged.**
**(GR-61)** carries the (GR-56) chunk invariants into the `z`-form exactly —
step 1 of the pinned route succeeds, buying notation and one structural fact
(`Z2(S) = ∅ ⟺ S = E(G°)`, the unique chunk whose inequality reads only the
odd bits) but nothing more; the localization's *premise* — every chunk
invariant a function of the odd pattern — survives on an exact **10-shape**
exceptional family (nine one-even-branch θ shapes, the all-length-3 `K4`) and
dies at all **4914** others. **(GR-62) REFUTES step 2 by witness:** full
goodness is not a function of the (GR-50) degree data — two admissible
balanced configurations share the same odd pattern and even-branch
in-degree vector yet split on full goodness (7982 of 217 468 fibres, at
1499/4924 shapes, the smallest witness rank-certified at `n_hub = 4`) — so
**no (GR-51)-shaped criterion applies to the chunk system**. **Scoped
honestly:** this excludes a *(GR-51)-shaped* criterion (feasible set cut out
by in-degree bounds), not every conceivable existence criterion — a shape's
existence question is trivially a function of its odd pattern alone. The
positive content is **(GR-64)**, the collision bound — a colouring-free
lower bound on `d_fg` pricing the coupling between (Y)'s distance quantifier
and its chunk constraints, with a **proven `≤ 2` per-chunk ceiling**
(attained), a packing form, and a **sound** 1250-of-24 671 anchor-matching
prune (incompleteness 7856 disclosed) — and **(GR-65)**, the fit identity:
`dist(m, M)` and `z_mono(S)` are the *same statistic* (the minority dart on
a prescribed selection), naming what any successor instrument must control.
**(GR-66)** measures GBAL's own certificate against (Y): it misses the
distance optimum at 3514/4924 shapes and full goodness at 651/4924.
**`min_M B(M) = 0` at every one of the 4924 inventory shapes is MEASURED,
not proven** — named as sub-target **(GR-64)(R2)**, the sharpest cheap
successor the pass produced. Input (Y) stays **OPEN**, (a′) is **NOT** hit,
**E3 (ARMED by GBAL) does NOT fire**; (GR-15) **OPEN**, no gap-map status
moves; class uniformity, `hK`, and the balance layer (route-ledger entry 5)
all untouched.

**Two coordinator adjudications on landing.** *(1)* The predicted-obstruction
refutation above is genuine, not a partial hit: the prediction was **wrong**
and (GR-63) is **right** — recorded plainly, not softened. *(2)* GLAW's
*Step G79* routing override (§"The coordinator's one routing sharpening"
above) is **SPLIT by this landing, not simply upheld**: the override was
right to try GBAL's `z`-form first and right about the **chunk/balance**
rung, but **GLAW's matching-flexibility clause is reinstated for the
*distance* rung specifically** — exactly the rung GBAL's instrument
dissolves and loses ((GR-65): distance and `z_mono` are one statistic;
(GR-66): GBAL's own certificate sits above `d_adm` at 3514/4924 shapes).
Neither clause is wrong; they address different rungs of one statement. The
successor's natural routing, carried forward to BALB/the next primary:
(GR-61)'s `z`-form for the chunk arithmetic, (GR-55)'s coset/SDR coordinates
for the distance, (GR-65)'s `fit` as the bridge, and a Hall/deficiency
condition over the tight-chunk hypergraph of exit selections (GORIENT
*Step G43*'s frame) in place of degree-constrained orientation.

**What did NOT move.** No gap-map status moves: (GR-15), class uniformity,
`hK`, the balance layer and route-ledger entry 5 are exactly where they
were. (GR-62)'s refutation is scoped honestly (excludes a (GR-51)-shaped
criterion only). (GR-64)'s prune is sound but incomplete (1250 of 24 671
kills, incompleteness 7856 — both numbers disclosed). **TERMINATION: E1, E2
and E3 all NO; E3 stays ARMED (by GBAL) and does not fire.** One
(b′)-relevant by-product reported and **not developed** (BALB's target this
wave, per the bar): (GR-65)(ii) expresses the deviation count in the same
dart-colour language (GR-49) that (GR-50) uses to decide balance, so
`d_adm − d_par` becomes a statement about two `fit` counts on one colouring.
**Not pre-empting BALB:** (GR-65)(i)'s identity (`n − #agree = #differ`) is
the general statement, for any selection `β`; BALB's independently-derived
perfect-matching-anchored instance is its own label, cross-cited from that
side, not minted here.

## Twenty-first direction — BALB (seventh fan-out)

**Status: LANDED 2026-08-19 — (b′) stays OPEN, NOT a HIT, with its
decomposition half proven and half refuted at an exact boundary.** Third
of the seventh fan-out's five directions to land, after CIRR and YLOC
(AGLU/ZNEQ still in flight), **compute-licensed** tier. §(K-grid)
**extended**, **Steps G86–G91**, labels **(GR-67)–(GR-72) CLAIMED
exactly** — the full reservation consumed, nothing returned to the pool.
Driver **`notes/scripts/w4/balb.py`** (six modes;
`--validate` runs all six inside the 600 s foreground budget, measured
~105 s).

**The target — (b′), the balance-layer bound `d_adm − d_par ≤ 2`.** OPEN and
supported (no growing gap ever found); ridden as a *secondary* three times
(GADM, GPSA, GDESC) and **never a primary**. This wave makes it one.

**Why now.** (GR-54) proves `d_adm < ∞` and says **nothing** about the gap —
GBAL's own scope line is explicit: *"It does not move (b′)."* What changed is
the instrument, not the evidence: **(GR-50)** decides balance **exactly, in
polynomial time**, over at most 20 odd-branch patterns, and **(GR-51)** prices
feasibility by a **local weight inequality**. That is the first apparatus in
the arc that could deliver a *bound* rather than a measurement.

**Two halves — keep them distinct.**

1. **Is `|δ|` at a parity-optimal map bounded by 2?** GDESC measured
   `{0: 92, 2: 2}` at parity-optimal maps over 94 odd-carrying shapes, exact
   gaps `{0: 92, 1: 2}`, 0 mechanism violations. A shape with a parity-optimal
   floor `|δ| > 2` **refutes this half** (and is E1 clause (v)'s named
   trigger — surface it as such).
2. **Does repairing balance from a parity-optimal map cost `≤ 2` deviations?**
   (GR-45) prices **one T1 at exactly 2 deviations**, so a single T1 repair
   gives exactly 2 and the question is whether one T1 always suffices —
   which **(GR-46)'s one-move transitivity makes precise** (any two
   parity-consistent minority maps differ by a single legal move, so "one
   move" is not a restriction on reachability, only on *cost*).

**What counts as a HIT** — a proof of `≤ 2`; **or** a proof of a *different*
constant **with the exact boundary named**: the (GR-29)/(GR-30) precedent makes
an exact-boundary refutation a **valued outcome, not a failure** (a theorem at
`n_hub ≤ 6`, false from `n_hub = 8`, with witnesses, is how (GR-28)(iv) landed);
**or** a witness at gap `> 2`, which moves (b′) to refuted-with-successor.

**Bars.** Entry 5 is **PROVEN** ((GR-54)) — do not re-attack it. **(a′) /
input (Y) is YLOC's target this wave** — report any (Y)-relevant by-product as a
finding and do not develop it. Do **not** re-open the bounded-deviation
selection form (**REFUTED as posed**, (GR-41)+(GR-42): `d(NK(m)) ≥ m/2`
unbounded while every member stays fully-good) — (b′) is a statement about the
*gap between two layers*, not about the deviation count, and the necklaces are a
test bed for it, not a refutation of it.

**Riders.** As YLOC's, verbatim. Additionally: the shift-metric layer is
**UNBOUNDED** ((GR-43), `d_par = d_adm = d_fg = m` exactly at the necklaces) —
so (b′) must be stated as a bound on the **difference**, never on `d_adm`, and
any figure quoting a necklace member carries that qualifier.

**The verdict, as landed: (b′) stays OPEN, NOT a HIT — its decomposition is
now half proven outright and half refuted at an exact boundary**, the
(GR-29)/(GR-30)-shaped outcome named above as a valued result, not a
failure. **(GR-67)** anchors the z-form at a perfect matching `M`: the
deviation count from `M` is a **2-factor sign-change count**, and a
one-line branch sum gives the **PARITY LAW** — every per-matching layer
gap is EVEN, so per-matching (b′) is the dichotomy *gap 0 or gap ≥ 2*, and
a counterexample must show a gap of 4, never 3. **(GR-68)** prices
**every** legal move in closed form: matching branches and whole 2-factor
cycles are FREE, and a single-path repair costs at most 2 **regardless of
its length** — this **proves (b′)'s price half outright**, at every shape,
with no cap and no length restriction. **(GR-69)** proves the imbalance
ceiling `|δ| ≤ 2·min(k, ⌊n_hub/4⌋)` from the *necessity* half of
(GR-51)(i)(a) alone, so `|δ| ≤ 2` is a **theorem at `n_hub ≤ 6`** — the
whole stratum, hence *this row's own* and GDESC's *Step G66*'s measured
`|δ|` figures there are arithmetic, not evidence — and **FALSE from
`n_hub = 8`**, realized at the Wagner habitat shape **V8** (accepted by
both `cflank.cubic_habitat` and `gdev.habitat_by_lemma`, `|δ| = 4` at 4 of
418 configurations), tight at every rung reached. **(GR-70)** reduces
per-matching (b′) to **one availability clause** (Clause A′) and verifies
it **EXHAUSTIVELY** over the whole stratum (4780 shapes, 23 939 (shape,
matching) pairs, all 96 930 unbalanced parity-optimal configurations, full
`3^n` censuses, no cap) — while **REFUTING** the landed T1-only instance of
that clause **from `n_hub = 8`**, with stuck witnesses at 32/15 088,
120/16 502 and 52/15 904 configurations at `n = 8/10/12`, every one
repaired at price **0** by a named **mixed-pair** move. **(GR-71)** carries
(b′) to 536 exact shapes at `n_hub = 8/10/12` and to cap-free per-matching
certificates at `n = 30`. **(b′) stays OPEN, NOT a HIT** — price half
proven, availability half not; **(GR-15) stays OPEN, no gap-map status
move on `hK` itself**.

**E1(v)'s named trigger does NOT fire.** The V8 `|δ| = 4` configurations
are **not parity-optimal** (they sit at `|δ| = 4` among a spectrum
`{0: 230, 2: 184, 4: 4}`, none of the four the parity-optimal member) — a
careless reading of "half 1 refuted" would think this fires it; it does
not, and the pass says so explicitly.

**Three coordinator adjudications on landing.** *(1)* **The
cross-direction duplicate is a corroboration, not a rediscovery.**
(GR-67)(i) and YLOC's landed (GR-65)(i) are **the same identity** —
`dist(m, M) = #{v : the two non-M darts differ}` is exactly
`n − #{v : they agree}` — derived independently by two directions blind to
each other in the same concurrent fan-out. (GR-67)(i) lands as the
**perfect-matching-anchored instance** of the landed (GR-65)(i), cross-cited
in that qualified form, with the independent double-certification recorded
as **corroboration** — the wave's third such convergence (after
OCON/FRES, and now YLOC/BALB here). What (GR-67) adds beyond the shared
identity is new: the parity law (ii) and the changeover parametrization
(iii), both BALB's own. *(2)* **The flagged-unverified by-product is
already verified.** BALB's report that (GR-67) Cor. 1 extends to
`d_fg(M)` — hence `d_fg(M) − d_adm(M)` even, hence GLAW's (GR-59)
per-matching (a′) witnesses must all carry a gap `≥ 2`, never exactly 1 —
is **corroborated against a landed figure**, not left unverified: GLAW's
own landed (GR-59) measurement of that very gap distribution is
`{2: 1251, 4: 27}` — every one of the 1278 gaps is already even, from a
different direction in an earlier wave. *(3)* **The retroactive
reading-downgrade lands at the figures it downgrades, not only in BALB's
own section.** (GR-69) proves `|δ| ≤ 2` is forced on the whole
`n_hub ≤ 6` stratum, so GDESC *Step G66*'s `{0: 92, 2: 2}` and this pass's
own exhaustive `{0: 4641, 2: 139}` carry **no evidential weight for
`n_hub ≥ 8`** — the figures stand, only the *reading* is downgraded, and
the annotation is recorded at *Step G66* itself in `Pencil-informal.md`,
not only here.

**The cap disclosed, with its reason.** The necklace leg stops at `m = 6`
because `gadm.dp_pref`'s table is `2^dim` (dim 16/21/26/31 at
`n = 30/40/50/60`, guarded by `assert dim ≤ 18`), and **GBAL's
`n = 40..60` reach does not transfer**: (GR-54) needs only balance
*existence*, decided polynomially by (GR-50), whereas any (b′) statement
needs `d_par(M)`, the exponential object. An exhausted table is not `∞`
and a `m = 6` leg is not an `m = 12` leg.

**TERMINATION: E1, E2, E3 all NO.** No `g`-flank (rank-free throughout,
no `d_fg` claim made); entry 5 (PROVEN, GR-54) is untouched, and (b′) —
not a ledger entry in E2's sense — leaves an open, named, dispatchable
attack either way. **E3 stays ARMED by GBAL and is neither fired nor
disarmed** — its target is entry 1, (a′), which this pass does not
attempt (YLOC's target this wave).

**The residual, named exactly: *Clause A′*, doubly-blocked sub-clause.**
The one-end-blocked case is nearly done — the mixed-pair mechanism prices
it at the unblocked T1's price, because an `M`-branch is free. The
doubly-blocked case, (GR-48)'s named kill realized at `n = 30`, is the
real gap: the chain must be followed at both ends, and (GR-68) prices it
only `≤ 4` unless both extra endpoints land on deviating hubs. **The
recommended untried alternative:** minimizing `dist(·, M)` at a *fixed*
balanced pattern is, by (GR-50), a min-cost degree-constrained
orientation — polynomial; per-matching (b′) is then an exchange argument
between two such flow problems (pattern-free vs pattern-fixed), and flow
theory's exchange machinery is untried on this arc.

**What did NOT move.** No gap-map status moves: (GR-15), class
uniformity, `hK`, entry 5 and route-ledger entry 1/(a′) are exactly where
they were. Every figure above at `Λ = ∅`, `D = 0`, modulo (GR-4′) where a
closure chain is concerned; `Λ ≠ ∅` and `D > 0` stay **unswept**.

## Twenty-second direction — AGLU (seventh fan-out)

**Status: LANDED 2026-08-19 — a HIT on the "not realizable" branch, with
one correction to the dispatch's predicted consequence.** Fifth and last
of the seventh fan-out's five directions to land, after CIRR, YLOC, BALB
and ZNEQ — **this landing closes the seventh fan-out**. Labels reserved:
`GR-` **(GR-73)–(GR-78) CLAIMED exactly**, **Steps G92–G97**; owning
section **§(K-grid)** (extends). Driver: **`notes/scripts/w4/aglu.py`**
(six modes `--pool`/`--pin`/`--kill8`/`--lam8`/`--adv`/`--val`, `--lam8`
run in three slices `--slice i/3`).

**The target — ledger attack (c): AA-glue realizability at `n_hub ≥ 8`**, the
**only surviving case** of the (GR-38) intersection kill. (GR-38)(iii): a
crossing pair of same-block binding chunks forces
`slack + defect(S ∩ S′) ≤ 1`, which forces the **AA-glue** configuration; over
the **complete** `n_hub ≤ 6` stratum that configuration has **0 instances**
(0 / 53 740 instances over 4920 shapes — binding is *provably laminar* there,
so the kill is **vacuously strong**), and whether the configuration is
**realizable** from `n_hub = 8` on is open.

**The two outcomes, and what each buys — both are wins, say which you got.**

- **NOT realizable** ⟹ the intersection kill extends past its vacuous stratum
  and **binding laminarity becomes a theorem**, which organizes the whole
  binding family that (GR-35)'s submodularity and (GR-36)/(GR-40)'s charges
  already circle.
- **Realizable** ⟹ the kill has a **real case**, and the charge apparatus must
  handle it. Name the witness exactly, **rank-certify** it, and check whether it
  is fully-good (a realized AA-glue that is still fully-good is a much weaker
  event than one that is not).

**Method.** An exhaustive-or-provably-complete search at `n_hub = 8`, using the
landed oracles rather than new ones: **(GR-25)**'s `2^{n_hub}` cut criterion as
the canonical `D = 0` membership oracle, `cflank.cubic_habitat` as the habitat
gate, `cflank.admissible` for colouring acceptance, and (GR-42)'s polynomial
habitat-membership criterion where a shortcut is wanted. **Cap disclosure is
mandatory** — the §(K-grid) cap-exhaustion hazard is a recorded gate
(`731b3e33`), and LTWO's *"4 of 8 patterns"* correction is the precedent for
what a silently-capped leg costs: **an exhausted cap is not a proof of
nonexistence.** If the search is capped, the return says "not found under cap
C", never "does not exist".

**Bars.** Do **not** re-open (GR-28)(iv)'s `g ≤ 1` cap — **REFUTED with an exact
boundary** ((GR-29) a theorem at `n_hub ≤ 6`, (GR-30) false from `n_hub = 8`
with four witnesses, per-shape (GR-15) holding at all four (GR-31)); its
`n_hub = 8` witnesses are **available as constructions to reuse**, which is the
one thing to take from it. Do **not** re-run the (GR-39)/(GR-40) fully-hot
census (landed **exhaustive** over all 4920 `n_hub ≤ 6` shapes). **(d′)** — the
corner-armed realized-binding fully-hot seed hunt past GDEV's caps — is **NOT**
this direction (E1's own clarification: not a flank by itself).

**Riders.** As YLOC's, verbatim. Every obstruction figure carries its **family
qualifier** — (GR-36)'s **binding-capable** family strictly contains the
capacity-tight one, and (GR-40)'s 815 → 573 is a **prune, not a zero**.

**The verdict.** **(GR-73)** proves `slack = 0` ⟺ no X-hub, pinning the
crossing interface to a rigid `{2,3}`-degree subgraph with two disjoint
`≥ 2`-member attachment families, and extends the J-charge from chunks to
arbitrary branch sets. **(GR-74)** proves the AA-glue configuration at
`n_hub = 8` has exactly **one** combinatorial template — `T` covers all 8
hubs at 10 branches, `R`/`R′` single branches, `S ∪ S′ = E(G°)` —
EXHAUSTIVE at all 44 premise-satisfying pairs of all 20 classes, and
explains the `n_hub ≤ 6` vacuity combinatorially, before any colouring.
**(GR-75)** proves the configuration and its whole kill residual (not just
the named case) are **NOT realizable** at `n_hub = 8` — a four-line
contradiction with (GR-32)(iii)'s balance identity, independently certified
by an EXHAUSTIVE, uncapped scan of the complete stratum (39 689 shapes,
9 617 854 admissible colourings, 0 instances) that also reproduces
(GR-38)'s own `n_hub ≤ 6` headline exactly (4 920 / 284 512 / 53 740 / 0) —
so the (GR-38) intersection kill is a **THEOREM at `n_hub = 8`,
non-vacuously**, and the **maximal** binding chunk family of each block is
laminar. **(GR-76)** derives a general-`n` charge `|W| ≥ |F₂| + q_T` that
forces `n_hub ≥ 10` with no pinning needed — an `n`-free strengthening of
(GR-75)(i) that also re-explains (GR-38)(iii)'s `n ≤ 6` vacuity — and
narrows `n_hub = 10` to exactly **three** counting-satisfiable templates.

**The correction, landed plainly, not softened.** The dispatch predicted
*"NOT realizable ⟹ the intersection kill extends past its vacuous stratum and
**binding laminarity becomes a theorem**."* **(GR-77) REFUTES that exactly as
stated:** exhaustive over the complete `n_hub = 8` stratum, there are
**3 774** crossing same-block binding chunk pairs (nested 457 244) against
**0** over the whole `n_hub ≤ 6` stratum. **Outright binding laminarity is
FALSE at `n_hub = 8`.** What (GR-75) actually buys is the **uncrossing**: the
kill is a theorem non-vacuously, so the **maximal** binding family is
laminar **per block** — 1 424 of the 3 774 pairs by exhaustive measurement
(all at `slack + defect(T) = 2` exactly), the other 2 350 by the (F-c)
charge bound, with no claim about their `(slack, defect(T))` distribution
beyond `≥ 2`. This is the **second** coordinator-predicted consequence this
wave to be refuted by the direction it primed (after YLOC's (GR-63)).

**(GR-78), a real E1 detector, not an omission.** Every one of the **39 689**
shapes of the complete `n_hub = 8` stratum carries a fully-good admissible
colouring (`a = 0 ∧ max_P g ≤ 0`); **8 543 304 / 9 833 022** (86.9 %) of
colourings are fully good, every shape `≥ 10`; `assert flank == 0` per
shape, no g-flank. This yields per-shape (GR-15) at `n_hub = 8` on the
complete stratum, **modulo (GR-4′)**, counting-side only — **no rank was
computed anywhere in this pass** — a substantial positive that is **not** a
(GR-15) status move: uniformity stays open.

**Cap disclosure.** `n_hub ≥ 10` is **OPEN with no search run there and no
cap exhausted** — (GR-76)(iv) narrows it to three templates, it does not
search it. The **592 shapes skipped by `--kill8`**'s length filter are
**proven residual-free by the (GR-36)/(F-c) charge bounds**, not budgeted
away. The `--lam8` three slices are an exhaustive **partition** of the 11
habitat-carrying classes, not a sample. The shape pool is the **complete**
stratum (every iso class of connected loopless cubic multigraph on 8 hubs ×
every excess profile, gated by the landed (GR-25) criterion). `--val` was
run by the dispatch (not re-run at landing) and reproduced item 7's
`n ≤ 6` headline exactly, which is what licenses this pass's `n_hub = 8`
numbers; `--pool`/`--pin`/`--kill8`/`--lam8` (all three slices)/`--adv`
were all independently re-run by the coordinator at landing and reproduced
every quoted figure above.

**Riders, verbatim.** Everything at `Λ = ∅`, `D = 0`, modulo (GR-4′)
wherever (GR-15) is mentioned; `Λ ≠ ∅` and `D > 0` stay **unswept**. **None
of this closes (GR-15)**; **no gap-map status move on `hK`**. Every
obstruction figure carries its **family qualifier** — (GR-36)'s
binding-capable family strictly contains the capacity-tight one, and
(GR-40)'s 815 → 573 is a **prune, not a zero**. **(GR-74)** is exhaustive
and colouring-free (all 44 premise-satisfying pairs across all 20 classes,
nothing else).

**TERMINATION: E1 does not fire (on the (GR-78) detector's evidence); E2
does not fire — attack (c) narrows rather than dies, with (GR-76) named as
its instrument, and (a′)/(b′)/(d′) stay dispatchable; E3 stays ARMED by
GBAL and is neither fired nor disarmed.** (E1) — (GR-78) is a real
exhaustive detector: every one of the 39 689 shapes carries a fully-good
colouring, so no g-flank exists at `n_hub = 8`; nothing about the 3 774
crossing pairs is a flank — they are pairs of binding chunks at
*particular* colourings, and every one of their shapes still carries ≥ 10
fully-good colourings. (E2) — attack (c) moves from "open at `n_hub ≥ 8`"
to **"settled negative at `n_hub = 8`, open at `n_hub ≥ 10` with (GR-76) as
the named instrument"** — a narrowing with a successor named, which the E2
carve-out explicitly does not fire on; attacks (a′), (b′) and (d′) are
untouched and remain dispatchable. (E3) — AGLU is a §(GR-38) pass and
touches neither entry 1 nor (a′); the arming state is unchanged from GBAL's
entry-5 HIT.

**So: no escalation from this direction. The coordinator re-runs the
check.**

**The seventh fan-out is now COMPLETE — all five directions landed
2026-08-19.** Full per-direction detail: CIRR §"Twenty-fourth direction",
YLOC §"Twentieth direction", BALB §"Twenty-first direction", ZNEQ
§"Twenty-third direction", above.

## Twenty-third direction — ZNEQ (seventh fan-out)

**Status: LANDED 2026-08-19 — input (a) is OPEN as a class-uniform statement
and is NOT an independent gap.** Fourth of the seventh fan-out's five
directions to land, after CIRR, YLOC and BALB (AGLU still in flight),
**compute-licensed** tier. §(K-out) **extended**, **Steps O19–O24**, labels
**(OC-23)–(OC-28) CLAIMED exactly** — the full reservation consumed, nothing
returned to the pool. Driver **`notes/scripts/w4/zneq.py`** (four modes,
no `--validate`; `--factor` 97 s, `--sweep` 242 s, `--reject` 76 s,
`--transfer` 106 s — run individually rather than as one foreground call,
all byte-identical under `PYTHONHASHSEED` 0 and 12345 modulo `--sweep`'s
wall-clock progress marks).

**The target — (OC-19) input (a), `Z ≠ ∅`, as a statement in its own
right:** *at every class (shape, split), the chart carries a target-rank
point with `s₀ = 0`.* OCON ranked this **#2 of its five** hand-off items and
called it *"cheap to state and would clean up several rows at once"*; it is
a prerequisite of the **whole (K-tight) criterion — not (OUT)'s to pay** —
and is currently carried **implicitly by every route on the (K-wit) row**.

**The verdict, as landed: input (a) FACTORS, and the two halves have very
different severity.** **(OC-23)** peels the pendant edge `ac` exactly the
way (OC-17) peels `ab`: `s₀ = corank R(H)` at **every** legal chart point,
`H = G − v − a`, so the `s₀` half of input (a) contains no `v`, no `a`, no
split edge — it is **independence of the far framework `H` alone**.
**(OC-24)** proves the dichotomy the chart's irreducibility buys — with
CIRR's **(CH-1)(a)** now proven rather than cited, `Z ≠ ∅ ⟺` both halves
nonempty, each **one-point witnessable** — and the sharper finding the
dispatch's wording did not anticipate: `{σ = 0} = ∅` at a class shape would
make `hK` **FALSE there** (`E(H) ⊆ E(G)`, `G` tight with `def(G) = 0`, so a
self-stress of `H` at every chart point is a self-stress of `G` that blocks
its own Tay target). That branch is a **PENCIL event** — a disproof at that
shape, §(K-flank) direction-A pivot class — **strictly stronger** than the
`{target rank} = ∅` branch, which is exactly the **(K-tight) event** the
dispatch named (routes A and B dead at that split, `hK` at the shape
untouched). So the `s₀` half is a **necessary condition** for `hK` at the
shape and can **never be the binding obstruction**: any proof of `hK`,
including the grid route, hands it over for free. **(OC-25)** shows the
target-rank half **is** §(K-tight) *Step 2* item 1's own attainment
criterion, applied one split down (`(G, v, a, b) ↦ (G′, a, b, c)`), the
regress terminating in one step because `orient`'s chain has exactly two
interior vertices. **(OC-26)** derives the closed form of that half's
failure: along the meet line `M = Π(b) ∩ Π(c)`, badness is three quadratics
in one parameter, hence generically empty, and bad-at-every-`t` is a
**disjunction** — `dim(D ∩ (M̂ ∧ W)) ≥ 3` or `M̂ ∧ w ⊆ D` for some `w ∈ W`
— both forcing a **codimension-2 Schubert jump**. **This pass refuted its
own first closed form by construction** (POOL-ZQ Case C: a nonsingular
hyperplane of `M̂ ∧ W`, `dim(D ∩ M̂ ∧ W) = 3`, **no** pencil inside it, yet
identical badness), correcting the single-containment reading to the
disjunction — adversarial work against its own claim, landed as such, not
tidied away. **(OC-27)** measures **138/138** (shape, split) witnesses of
`Z ≠ ∅` (90 companion-bearing, 48 others), no miss — witnesses, never a
rate, caps disclosed (shape cap 4/family, 6-seed window, stride 4; 142 of
190 non-companion splits uncovered). **(OC-28)** proves the shared-sub-tower
clause against §(K-chart) **(CH-2)**'s stage table (both chain interiors are
non-hubs, so stage 2's hub-only dependence makes the `H`-projections of
`G` and `G′`'s charts identical) and constructs 30/30 transfers, then shows
the `s₀` half is **dominated** by §(K-grid) (GR-10): one grid point per
shape covers **every** split at once, free at 907/907 of that pool — a
**conditional** reduction to an open gap, not a discharge, since (GR-10)
is itself open (its min-max form refuted as posed, the statement itself
staying open, per §(K-grid)'s own row). `{σ = 0}` is exhibited as a
**proper** open, not a tautology: at the (K-res) shape `P21` (fails
`hnoRigid`), 5 of 35 valid seeds sit off it, the only recorded mechanism
being a self-stress of a short theta sub-multigraph inside `H`.

**Four coordinator adjudications on landing.**

1. **The spec's wording was incomplete, and ZNEQ's correction is right.**
   The dispatch called a `Z = ∅` negative "a (K-tight) event, not an (OUT)
   event" — true only for the target-rank branch. The `s₀` branch is a
   **PENCIL event**, strictly stronger, and — the structural point — it can
   never be the *binding* obstruction, because it is implied by `hK` at the
   shape and its only known failure mechanism (§(K-flank) *F5(d)*'s theta
   sub-multigraph at `P21`) sits outside `hK`'s habitat (`hnoRigid` false
   there). This is why input (a) is **not an independent gap**: one branch
   is dominated, the other is a disproof route. (OC-8)'s residue is
   **sharpened, not shrunk** by this: the `s₀` half is dominated, and the
   target-rank half — `(a₁)`, the Schubert non-jump
   `dim(D ∩ M̂ ∧ W) ≤ 1` — remains a real open input of the same shape as
   (OC-19)(c), one-point decidable with the recipe missing.
2. **(OC-28)'s positive is CONDITIONAL, not a discharge.** §(K-grid) (GR-10)
   is itself OPEN (its min-max refuted as posed, the statement staying open
   as the strictly stronger form), so "(GR-10) ⟹ the `s₀` half at 907/907"
   is a **reduction to an open gap**, per-shape evidence rather than
   uniformity. The named cheap follow-on — a purely combinatorial cross-pool
   re-keying of §(K-grid)'s 907 against §(K-out)'s class-shape population,
   no new mathematics — is carried to the hand-off, not attempted here (the
   two pools are labelled-instance pools with different keys and are
   **not** re-keyed by this pass).
3. **The wave's THIRD cross-direction convergence, recorded as a finding
   about the fan-out shape itself.** ZNEQ wrote its mathematics **blind to
   CIRR**, which landed mid-run, flagging (OC-28)(i)'s shared sub-tower as
   "this pass's one structural input, owned by CIRR". CIRR's same-day
   **(CH-2)** — the tower written down stage by stage — then turned that
   flagged input into a proof outright, and its **(CH-1)(a)** supplied the
   ℚ-descent step (OC-28)(iii) needed. This is the **same shape** as the
   sixth fan-out's OCON/FRES pair and this wave's own YLOC/BALB pair on the
   fit identity: three independent convergences in two waves, every one a
   direction discovering it needs a fact another concurrent direction was
   independently landing, neither seeing the other. **Worth naming as a
   property of the fan-out shape**: a multidispatch surfaces cross-cutting
   dependencies a single serial dispatch would have had to name explicitly
   in advance or miss, and this wave found three without any coordinator
   foresight.
4. **The self-refutation stands, as adversarial work, not a hedge.** POOL-ZQ
   Case C is a constructed counterexample to this pass's *own* first
   derivation. It is landed in full in (OC-26)'s "refuted by construction"
   clause above, not tidied into a footnote.

**Not a dispatchable candidate — awaiting user adjudication.** *Step O24*
names a `σ > 0`-everywhere hunt at class shapes whose `H` carries a short
theta sub-multigraph as the only known failure mechanism for the necessary
half. A hit there is a **PENCIL event**, which under the direction-A pivot
rule (`notes/Pencil-fanout-archive.md` §"Direction A", *Pivot rule*) is *"a phase-redefining event for
the user to adjudicate, not a result to build on."* It is named here and in
the hand-off for completeness, and is explicitly **excluded** from the pool
a future coordinator may pick from under the standing 2026-08-07 delegation
until the user has adjudicated it.

**The cap disclosed, with its reason.** POOL-ZN's shape cap is 4 per family,
seed window 6, stride 4 on non-companion splits — 142 of 190 non-companion
eligible splits, and every shape past each family's fourth, are **not
covered**. This is a witness census, not a rate: each of the 138 hits is an
individual proof that `Z ≠ ∅` at that (shape, split), so the cap bounds
*coverage*, not *confidence* in what was measured.

**TERMINATION: E1, E2, E3 all NO.** *(E1)* no g-flank: this direction
touches no admissible colouring and exhibits no `D = 0` shape whose every
admissible colouring is binding — per-shape §(K-grid) (GR-15) is untouched.
*(E2)* the target is neither refuted nor unprovable-as-posed — it is
**reduced**, with two named, one-point-decidable, dispatchable attacks
(the re-keying job and the Schubert non-jump). *(E3)* the target is **not
proven** class-uniformly; **E3 stays ARMED by GBAL's entry-5 HIT, neither
fired nor disarmed**.

**Harness debt recorded, not paid.** `ocon.meet` — the dimension-asserting
wrapper of `lambda.span_meet` — now has **two** consumers (OCON's and this
pass's), tripping `notes/scripts/README.md` §2 rule 2's own move-down
trigger. This pass may not modify a landed file, so the move is recorded as
a **new, dated, unpaid** debt item for a successor (README *Harness debt*)
— that section is otherwise CLEARED / round CLOSED (S1–S4, 2026-08-06), and
this is a **separate** entry, not a reopening of that round.

**Riders, verbatim.** The standing **(OC-7) rule**: no `place_pencil_general`
battery may be quoted as a **rate** or as evidence about a **generic** chart
point; POOL-G figures are quoted over the **318 coincidence-free** frames,
never the raw 357. The two settled pools **POOL-G and POOL-S are pinned and
disjoint** — not aggregated, not re-sampled. ZNEQ's own **138/138** are
**witnesses, never a rate**, caps disclosed as above.

**What did NOT move.** No gap-map status moves: (OC-8), class uniformity,
`hK`, (GR-15) and route-ledger entry 5 are exactly where they were. §(K-out)'s
*State of (K)* status cell was **recomputed from scratch** (790 → 649 words)
to make room for (OC-23)–(OC-28) rather than bumped past its cap; the
close-it cell gained the two-half breakdown (323 → 438 words), still well
under cap. `notes/check-gapmap-cells.py` passes on the changed row.

## Twenty-fourth direction — CIRR (seventh fan-out)

**Status: LANDED 2026-08-19 — a HIT.** First of the seventh fan-out's five
directions to land; one of **five** concurrent directions (YLOC/BALB/AGLU/
ZNEQ still in flight), **derivation-first** tier. §(K-chart) **OPENED**,
**Steps CH1–CH8**, labels **(CH-1)–(CH-8)** claimed exactly (nothing returned
to the pool, `notes/Pencil-labels.md`). Driver `notes/scripts/w4/cirr.py`,
three modes, ~1 s total — written, contrary to this direction's "expected
unused" driver clause, because two of its sentences are sampler-behaviour
claims no amount of prose settles (F11).

**The verdict: the pencil chart is irreducible, written down once, and all
four consumers audit clean.** **(CH-1)** states it: for `Γ` loopless with
`hcard`, min degree 2 and **girth ≥ 4**, the pencil incidence locus `𝒜(Γ)` is
a nonempty, irreducible, ℚ-rational variety, and so is its image
`Chart(Γ)` — a tower of affine-linear fibres (hub points free; hub normals in
the nullspace of hub-neighbour differences; interiors on `meet_line` /
`in_plane_point` / free), with `hcard` exactly the hypothesis that keeps the
normal-space fibre nonzero. **(CH-6)** identifies the tower's
constant-fibre-dimension restriction — the clause the dispatch asked to be
made explicit — as **`IsNondegPencilRealization`'s own conjunct 3**
(`LinearIndepOn K normal (closedHubNbhd v)`, `Motive.lean:110`), which `hK`'s
hypothesis `HasGenericPencilRealization K 3 G′` and the harness guard
`repin.star_generic` both already carry about `G′`. **(CH-4)** shows the
restriction costs no closure — `𝒜(Γ) = \overline{𝒫(Γ)}`, so a legal
realization off the restriction is still a point of the same irreducible
variety, which is exactly what §(K-slide) (S1)(e) needs. **(CH-5)** is the
one correction: *Step FR13*'s stated hypotheses (girth ≥ 3) do **not** give
nonemptiness — a Λ-triangle carrying a non-hub on two of its hubs empties the
tower's stage-3 locus at **every** seed (`Γ_bad`, 0/200 placeable, the reason
asserted, not just the symptom) — and girth ≥ 4 does, free at `G′` **three**
independent ways: the girth-6 table row, `gridcol.class_shape`'s two-hub-
triangle filter, and (see below) the landed Lean theorem. **(CH-7)** audits
all four named consumers — §(K-out) (OC-19) input (b), §(K-slide) (S1)(e),
§(K-dom) (D4), §(K-ann) (ANH-9)(ii) — clean, with two needing strictly more
than bare irreducibility (rationality; the closure clause (CH-4)) and both
supplied.

**One self-correction, recorded because it is the point the duplicate check
(CH-8) itself introduced.** (CH-8) reached the coordinator as a new
incidental claim (a triangle with two adjacent hubs makes the pin infeasible)
and coordinator verification found it **subsumed by a landed,
compiler-checked theorem** — `not_pencilNondegFeasible_of_triangle_two_hubs`
(`Motive.lean:563`, not `Witness.lean`, whose hits are call sites) — in a
**strictly stronger** form (two hubs, arbitrary third vertex, no `hcard`
hypothesis at all). (CH-8) lands as a **pointer, not a claim**; this
direction's own addition there is only the chart-side contrast the landed
theorem does not state — `𝒜(Γ) ≠ ∅` at 174/200 seeds of a triangle-carrying
control while `PencilNondegFeasible` is false there — and the duplicate check
it forced across (CH-1)–(CH-7) found one further partial duplicate:
(CH-6)(i)'s hub-side mechanism runs inline inside the landed theorem's proof,
but only for the **triangle** configuration — the tower's own Λ-**path** case
(`h₁ – x – h₂`, `h₁ ≁ h₂`) is outside the landed theorem's reach, and the
driver carries a witness asserting the graph has **no** two-hub triangle so
the non-duplication is itself driver-tested.

**What did NOT move.** No gap-map status moves: (OC-8), (ANH-R1), (GR-15),
`hK`'s class uniformity, the balance layer and route-ledger entry 5 are
exactly where they were — writing down a consumed fact is insurance, not a
status move. §(K-frame) (FR-7) **stays struck** (not re-opened): (OC-17)
already struck it as unnecessary, and (CH-1) is the chart's irreducibility
that struck it, not a new foothold. Two wording-only cells the coordinator
approved: §(K-out)'s (OC-19) confidence row now reads *"(b) proven,
§(K-chart) (CH-1)"* in place of *"conditional on (b)"*; §(K-frame) (FR-16)'s
rider list gains the girth ≥ 4 correction. Every bar held: no counting /
matroid route was proposed, and (GR-15)/class uniformity/the `g`-detector/the
balance layer were not touched. The TERMINATION check fires nothing: E1 (no
g-flank, no colouring examined), E2 (entry 5 untouched) and E3 (stays ARMED
for YLOC, not fired — (CH-1) is not a ledger entry) are all unchanged.

**Compute.** Three modes, `--empty`/`--guard`/`--fibre` (`--all` runs all
three), ~1 s total, `PYTHONHASHSEED=0`; one driver added, nothing existing
modified, so the figure-invariance gate discharges by that check alone.
Invocation rows landed in `notes/scripts/README.md` §3.

### Not selected, and why — the coordinator's ranking of the losers

Disclosed per the twelfth direction's precedent: **this ranking is the
coordinator's, with no independent top-rung reader.** A future recon may
overturn any of it.

- **(OC-19) input (c), class-uniformly** (`H/X` infinitesimally rigid at one
  chart point, at every class (shape, split, length-4 companion)) — OCON ranked
  it **#1 by value** (*"This is the whole residue"*), and it is deliberately
  **not** dispatched: OCON's own verdict says it is
  **(GR-15)-flavoured, not (FR-R1)-flavoured** — a rank condition inside a
  pattern-colouring existence question — so it re-enters the arc's **oldest
  missing technology** rather than adding an independent idea. It is the natural
  primary once a working chunk-level instrument for input (Y) exists — **YLOC's
  own attempt (twentieth direction) was DEMOTED BY WITNESS, not a success**
  (§"Twentieth direction"); the missing technology is still arriving from the
  other side, just not yet.
- **§(K-out) hand-off item 3** — `T_u^{⊥_B} ∩ β_b = 0` at the **1715**
  slide-legal `b` ends, where **(OC-21) makes it an iff**; measured
  `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends and 4/4 POOL-OC ones. A
  good, cheap, well-posed target; dropped **only** because ZNEQ already occupies
  §(K-out) this wave and item 3 rides the same measurement infrastructure.
  **Queue it.**
- **§(K-out) hand-off item 4** — the one-hub-neighbour extension of the slide
  ((OC-21)'s second bullet) and its census share. A `--wide`-style leg, **too
  small to be a direction**; fold it into whichever §(K-out) direction runs
  next.
- **(d′)** — the corner-armed realized-binding fully-hot seed hunt past GDEV's
  caps. **E1's own clarification says it is not a flank by itself**, so its best
  outcome is a measurement. Lowest value of the six considered.
- **Route σ's parked Lean half** and **the W4 build** — both **BLOCKED by the
  standing 2026-08-05 Lean hold** (general, not W4-scoped). Not eligible without
  a fresh user adjudication, and **none was sought** at this session's check-in.
- **`Pencil-strategy.md` §4.6's U3** — still unrun, but the shortlist is
  **partially superseded** for the tight stratum (U2 delivered by (GR-16)'s
  reduction, U3's negative-form insight already exploited) and §5.3's own
  local-frame feasibility boundary rules out the symbolic meta-option. Two
  **durable negatives** — do not re-run.

---

## Eighth fan-out — prepared and dispatched 2026-08-19 (directions GTMPL / GFLOW / GCOLL / OSCHU / SIGZ)

Five directions dispatched **concurrently**, each independent, each returning its
own untracked draft (`notes/Pencil-draft-<CODE>.md`) and its own new driver,
landed one at a time by **separate serial coordinator commits**: the seventh
fan-out's shape repeated, the **third consecutive** multidispatch wave.

**User adjudication authorizing the multidispatch.** Asked at the session-start
check-in how the twenty-fifth direction's pick should be made (top-rung recon /
coordinator-authored prep / multidispatch again / a user-named single direction),
the user elected **"Multidispatch fan-out again"** — an **option selection, not
free text** (the GEXIST precedent for how such a pick is recorded), and against a
coordinator recommendation *for* the recon shape. Same check-in: rungs
**`sonnet` + `opus` only, top rung = opus** (fable conserved — `weekly_scoped`
read 92 % at prep, and per the seventh fan-out's settling fact that limit gates
fable alone), cap **lifted**, rescue §1 fixups **pre-authorized**.

**And this check-in DOES move a standing constraint — the first check-in of the
arc to do so since 2026-08-05.** On ZNEQ's carried `σ > 0`-everywhere item the
user elected **"Authorize the hunt"**, whose offered text — accepted as the terms
of the authorization — reads: *"Add it to the dispatchable pool. If it hits, `hK`
is false at those shapes and the phase's target needs redefinition — you would
adjudicate that at the return."* So the item leaves the awaiting-adjudication
pool and becomes direction **SIGZ**, **with the direction-A pivot rule in force**
and with the adjudication moved from *before* the dispatch to *at the return*.
Everything else stands unchanged: phase OPEN, the 2026-08-05 Lean hold, W4
PARKED, `hK`/`hbareSplit` pinned, option B un-commissioned.

**Selection disclosure — the twelfth direction's, for the third consecutive
wave.** The **five directions themselves**, the **tier split** and the **label
reservations** are **coordinator-set**, so there is **no independent top-rung
ranking of the losers** this wave either; a future top-rung recon may overturn
§"Not selected — the eighth fan-out's losers" freely. What is **not** the
coordinator's: every one of the five is a successor **named by a landed
direction's own hand-off** — GTMPL by AGLU's hand-off item 1, GFLOW by BALB's
*Clause A′ sub-clause 2* plus its untried third route, GCOLL by YLOC's
**(GR-64)(R2)**, OSCHU by ZNEQ's input-(a) hand-off item 2, SIGZ by its item 3.
The *candidate pool* is the arc's; only the ranking is the coordinator's.

**Roster** — **all five LANDED 2026-08-19; the fan-out is COMPLETE**:

| direction | ordinal | tier | owning § | target | status |
|---|---|---|---|---|---|
| **GTMPL** | 25th | compute-licensed | §(K-grid) | AA-glue realizability at `n_hub ≥ 10` — (GR-76)(iv)'s three templates | **LANDED 2026-08-19** — an EXACT BOUNDARY: impossible at every `n_hub ≤ 14`, REALIZED at 16 (§"Twenty-fifth direction") |
| **GFLOW** | 26th | derivation-first | §(K-grid) | (b′)'s availability half — *Clause A′* sub-clause 2, the doubly-blocked case | **LANDED 2026-08-19** — a HIT at a DIFFERENT CONSTANT: sub-clause 1 PROVEN, sub-clause 2 REFUTED as posed, gap `≤ 12` modulo (GR-R1) (§"Twenty-sixth direction") |
| **GCOLL** | 27th | compute-licensed | §(K-grid) | **(GR-64)(R2)** — every habitat shape carries an anchor matching with `B(M) = 0` | **LANDED 2026-08-19** — **(R2) REFUTED** by a Petersen witness family; (R1) DELIVERED (§"Twenty-seventh direction") |
| **OSCHU** | 28th | derivation-first | §(K-out) | **(a₁)** class-uniformly — the Schubert non-jump `dim(D ∩ M̂ ∧ W) ≤ 1` (+ the (a₂) re-keying leg) | **LANDED 2026-08-19** — (a₁) half-proven, half-reduced to one determinant; the (a₂) leg a HIT (§"Twenty-eighth direction") |
| **SIGZ** | 29th | compute-licensed | §(K-out) | the `σ > 0`-everywhere hunt — newly authorized, **pivot rule in force** | **LANDED 2026-08-19** — **NO HIT**, and the counting route to a disproof is DEAD as a theorem (§"Twenty-ninth direction") |

**Shared mechanics: §"Shared mechanics (all three dispatches)" above binds
verbatim**, at five directions, with the seventh fan-out's three deltas
unchanged (drafts to `notes/Pencil-draft-<CODE>.md` untracked, the coordinator
merging and deleting; rung **opus**, top rung this session; each direction runs
the **TERMINATION check (E1/E2/E3)** and reports its reading, the coordinator
re-running it). **E3 stays ARMED** by GBAL's entry-5 HIT and is **not** fired by
any of the five: GCOLL is the only one on the (a′) path and it attacks a
sub-target strictly smaller than (a′), so a HIT there does **not** fire E3 —
say so and do not fire it. **Firing is a coordinator action.**

**On the tier split, recorded honestly.** `RESEARCH-ARC.md`'s *Genuinely
unsettled* item 2 says the compute-licensed / derivation-first split is
**untested** as a predictor of dispatch risk. It is used here for framing
(what instrument a direction reaches for first), not as a rung input — all
five are opus regardless — and this wave is **not** evidence either way.

### Two status cells need a recompute inside this wave, with explicit targets

`RESEARCH-ARC.md` §6's refinement — *a cap bounds growth but cannot express
purpose; dispatch a recompute with an explicit target that leaves headroom for
landings already queued into that row* — applies to this wave before its first
landing, because two rows are carrying three and two queued landings against
thin headroom. Measured at prep (`notes/check-gapmap-cells.py`, full table, all
27 rows within cap):

- **§(K-grid)**: status **1706 / 2035** words — **329 free against three
  queued landings** (GTMPL, GFLOW, GCOLL). **The wave's FIRST §(K-grid)
  landing recomputes the status cell to `≤ 1550` words** before adding its own
  content, leaving ≥ 485 for the three. **Do not bump the cap** — the cap is
  bumped only after an honest recompute, per the script's own docstring rule.
- **§(K-out)**: status **649 / 800** words — **151 free against two queued
  landings** (OSCHU, SIGZ). **The wave's FIRST §(K-out) landing recomputes to
  `≤ 560` words**, leaving ≥ 240 for the two. ZNEQ recomputed this cell
  790 → 649 one landing ago, so the target is deliberately a modest trim, not
  a second aggressive compression.

Both recomputes **verify label preservation by a scripted set-diff, never by
eye** (§6's other clause — a coordinator hand-recompute once dropped a live
label and only a script caught it).

### GTMPL — twenty-fifth direction (eighth fan-out)

**Status: LANDED 2026-08-19 — BOTH dispatched outcomes fired, on different strata.** First of the eighth fan-out's five to land. §(K-grid) **extended**, **Steps G98–G103**, labels **(GR-79)–(GR-84) CLAIMED EXACTLY** — nothing returned to the tail. Driver **`notes/scripts/w4/gtmpl.py`** (eight modes `--charge`/`--frame`/`--tpl`/`--min`/`--wit`/`--e1`/`--lam`/`--val`, ~352 s total, each inside the 600 s foreground budget with no split needed; all eight re-run by the coordinator at landing, every quoted figure reproduced).

**The verdict.** The dispatched three-template question is **NOT realizable**, by two new `n`-free charges each of which kills all three independently: **(GR-80)** the corner charge `n_3 ≥ 2n_2 + 2q_T` (a factor-3 strengthening of (GR-74)(iii), and a **third** independent proof of (GR-75)(i)) and **(GR-81)** the X charge `|X| ≥ n_2 + 2q_T`, resting on a universal dart identity that pins `#{B-darts at X}` **exactly** — of which **(GR-76)(i) is the `≥ 0` instance**, so this is precisely the ingredient AGLU's own *What would change this* named as unexploited. **(GR-82)** chains them to the `n`-free `n_hub ≥ 4(n_2 + q_T) ≥ 16`, killing `n_hub = 10, 12, 14` as well — **a finite bound, not a contradiction, so attack (c) does NOT close outright**, the distinction the spec asked to be precise about. And **(GR-83)** shows the bound is **EXACT**: a constructed `n_hub = 16` witness, habitat-gated by (GR-25), admissible by the canonical predicate, all three charges tight, rank-certified twice over — at which **the (GR-38) kill FAILS** (proper 22-branch union of defect 4). **(GR-84)** measures what else goes: the **whole** kill residual is inhabited there and **(GR-75)(iii)'s maximal-family uncrossing does not reach `n_hub = 16`** — all three maximal binding pairs cross — which costs the charge apparatus an **organizational** tool but no ledger entry its dispatchable state. **No pool was ever built**: the spec's cost-check-first instruction was followed and the template-restricted route needed none.

**Three coordinator adjudications on landing.** *(1)* **The spec's own dichotomy was defective and the correction is right.** It asked, on the realizable branch, *"whether it is fully-good"* — but a binding chunk **is** a `g ≥ 1` obstruction, so a realized AA-glue can never sit at a fully-good colouring: the case is **empty**, not weaker. The meaningful question is E1 (does the witness *shape* still carry a fully-good colouring?), and it does — the first of its 123 740. This is the **second** consecutive wave in which a coordinator-authored spec clause needed correcting by the direction it primed (ZNEQ's `(K-tight)`-vs-PENCIL-event wording was the first), and it is inherited from AGLU's spec verbatim, which is how it survived a re-read. *(2)* **(GR-76)(iii) is SUPERSEDED, not refuted** — its proof is independent and stands; a one-line forward pointer is added at *Step G95* rather than editing it, the arc's practice for a superseded-not-refuted bound. *(3)* **The sibling-import call was the coordinator's to make and is recorded, not defaulted:** `gtmpl.py` imports seven read-only devices from `aglu.py`, none catalogued in `notes/scripts/README.md` §1 — in policy as the documented sibling-import pattern, but tripping §2 rule 2's move-down trigger, so a new dated **UNPAID** debt item is recorded there on ZNEQ's `ocon.meet` precedent.

**Cap disclosure, verified at landing.** No cap is exhausted anywhere and no negative rests on one: (GR-82) is a proof plus an exhaustive walk of a **finite** parameter box, `--min`'s `n_hub ≤ 40` is a display window over a bound proven for all `n`, and no `n_hub = 10` or `16` stratum was enumerated or claimed. (GR-83) is **one constructed witness** plus a 30-member family, not a census; **(GR-84)'s counts are at ONE colouring of ONE shape and must never be quoted as an `n_hub = 16` rate**; `--val`'s `n_hub = 8` chunk-enumerator check is a seeded 6-of-20 subsample. The witness's habitat rests on the (GR-25) oracle, `kslide.no_rigid_branch_union` being a `2^M` scan out of reach at `M = 24` — **the same dependency AGLU's exhaustive `n_hub = 8` scan already has**, cross-checked by three of `gridcol.class_shape`'s four conjuncts run directly.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: the witness shape carries a fully-good colouring, so no g-flank; binding chunks at one colouring are not flanks ((GR-77)'s distinction). E2: the target is **settled**, not unprovable, and narrows with a named successor; (a′)/(b′)/(d′) untouched. E3: GTMPL is on the §(GR-38) path, not (a′) — **stays ARMED by GBAL, not fired.**

**What did NOT move.** **(GR-15) OPEN**, unchanged in both directions; **no gap-map status move on `hK`**; class uniformity untouched; the one rank computed is a single witness's `dim Z`, not a per-shape (GR-15) claim. §(K-grid)'s gap-map status cell was **RECOMPUTED** (1706 → 1730 words while absorbing six new labels, i.e. the pre-existing content compressed ~13%) rather than bumped, with label preservation verified by a **scripted set-diff** — 79 labels in, 85 out, zero dropped; the cap stays 2035, leaving 305 words for GFLOW and GCOLL. AGLU's hand-off item 2 was **not** attempted (it needs a stratum); the datum added is that `(0,1)`/`(1,0)` occur at `n_hub = 16`, so a `= 2` law would be `n_hub = 8`-specific.

**The target — AA-glue realizability at `n_hub ≥ 10`, ledger attack (c)'s only
surviving case**, verbatim from AGLU's hand-off item 1: by **(GR-76)(iv)** the
only possible profiles are `(|F₁|, |F₂|, |W|) ∈ {(4,0,1), (2,1,2), (0,2,3)}`
with `(n_2, n_3, |X|) = (4,4,2)`, `|T| = 10`, `q_T ≤ 1`. **This is a
three-template question, not a search.** The counting side is **satisfiable**
there (a worked profile in §(K-grid) *Step G95*), so what must be added is the
**colouring** side: the 2-1 dart pattern at each of the two `X` hubs, the
mono-hub ban, and the (GR-25) cut criterion.

**Why now.** AGLU settled `n_hub = 8` **negative as a non-vacuous theorem** and
(GR-76) is an `n`-free charge that already forces `n_hub ≥ 10` with no pinning.
Attack (c) is therefore one stratum from being closed outright, and (GR-76)(iv)
is the arc's sharpest specification of a remaining case: **three templates,
enumerated, with the counting already discharged.**

**Method, and the cost check that comes FIRST.** AGLU's hand-off is explicit:
*"Estimated cost is the one thing to check first — the `n_hub = 10` labelled
enumeration is ~50× the `n_hub = 8` one, so the canonicalizer, not the scan, is
the bottleneck. A `--pin`-style colouring-free pass restricted to the three
templates avoids the pool entirely and is the cheap route."* Take that route
first. `aglu.py` is `n`-generic apart from the pool (`cubic_iso_classes(8)` →
`(10)`, `excess_profiles(12,6)` → `(15,6)` runs the same three modes), but do
**not** launch the full pool scan before the template-restricted pass has said
what it can. Use the landed oracles, not new ones: **(GR-25)**'s `2^{n_hub}` cut
criterion as the `D = 0` membership oracle, `cflank.cubic_habitat` as the habitat
gate, `cflank.admissible` for colouring acceptance, **(GR-42)**'s polynomial
habitat-membership criterion where a shortcut is wanted.

**The two outcomes, and what each buys — both are wins, say which you got.**

- **NOT realizable at `n_hub = 10`** ⟹ attack (c) closes at `n_hub ≤ 10`, and
  if the argument is `n`-free (as (GR-76)(iii) was) **attack (c) closes
  outright**. State explicitly which of the two you got: an `n = 10`-specific
  kill and an `n`-free kill are very different results.
- **Realizable** ⟹ the (GR-38) kill has a **real case** at last. Name the
  witness exactly, **rank-certify** it, say which of the three templates it
  realizes, and check whether it is fully-good (a realized AA-glue that is
  still fully-good is a much weaker event than one that is not).

**Cap disclosure is mandatory** and is the standing hazard on this leg: an
exhausted cap is **not** a proof of nonexistence. If any leg is capped the
return says **"not found under cap C"**. AGLU's own `n_hub ≥ 10` line is the
model — *"OPEN with no search run there and no cap exhausted"* — and LTWO's
"4 of 8 patterns" correction is the precedent for what a silently-capped leg
costs.

**Bars.** Do **not** re-run the `n_hub = 8` scan — (GR-75) is **exhaustive and
uncapped** over the complete stratum (39 689 shapes, 9 617 854 admissible
colourings, 0 instances) and reproduces (GR-38)'s `n ≤ 6` headline exactly.
Do **not** re-derive (GR-74)'s template classification at `n_hub = 8`
(exhaustive, colouring-free, all 44 premise-satisfying pairs of all 20
classes). Do **not** re-open (GR-28)(iv)'s `g ≤ 1` cap — **REFUTED with an
exact boundary**; its `n_hub = 8` witnesses are available as **constructions to
reuse**, which is the one thing to take from it. Do **not** attack **(d′)** (the
corner-armed realized-binding fully-hot seed hunt) — not this direction, and
E1's own clarification says it is not a flank by itself. AGLU's hand-off item 2
(the `(slack, defect(T)) = (0,2)/(1,1)` tightness) is **available as a
secondary** if the primary closes early; report it as a by-product, do not let
it displace the primary.

**Riders, verbatim.** Everything at `Λ = ∅`, `D = 0`, and **modulo (GR-4′)**
wherever (GR-15) is mentioned; `Λ ≠ ∅` and `D > 0` stay **unswept**. **None of
this closes (GR-15)**, and a counting-side result is not an `hK` status move.
Every obstruction figure carries its **family qualifier** — (GR-36)'s
binding-capable family strictly contains the capacity-tight one, and (GR-40)'s
815 → 573 is a **prune, not a zero**. **(GR-77) stands:** outright binding
laminarity is FALSE at `n_hub = 8` (3 774 crossing pairs), so do not quote
(GR-75) as laminarity — it buys the **uncrossing** of the **maximal** binding
family per block, nothing more.

**Reservation.** §(K-grid) **extends**; labels **(GR-79)–(GR-84)**, **Steps
G98–G103**; driver **`notes/scripts/w4/gtmpl.py`**. The owning section stays
authoritative. Consume fewer than reserved ⇒ **return the remainder to the
tail** in the landing commit.

### GFLOW — twenty-sixth direction (eighth fan-out)

**The target — (b′)'s availability half: *Clause A′*, sub-clause 2, the
doubly-blocked case.** Clause A′ verbatim as BALB landed it: *at every
unbalanced parity-optimal configuration there is a legal flip set `F` with
`z + χ_F` balanced and `|W(F) ∖ S| − |W(F) ∩ S| ≤ 2`.* Sub-clause 1 (the
one-end-blocked case) is **nearly done** — the mixed-pair mechanism prices it at
the unblocked T1's price because an `M`-branch is free, leaving only the far-end
side condition `m(w_β) ≠ β` for at least one of the two available `β`, *"a
short, bounded derivation"* that covers **every** stuck witness BALB found
(48/48 at `n = 8`, cheapest price 0). **Sub-clause 2 is the real residual:**
(GR-48)'s named kill, realized at `n = 30`, where the chain must be followed at
both ends, `t(F) = 2`, and (GR-68) gives only `≤ 4` unless both extra endpoints
land on deviating hubs.

**The two routes BALB names, in its order.**

1. **What would close it directly:** *a proof that at a parity-optimal
   configuration the second chain's endpoint is forced onto `S`.* (GR-68)'s own
   minimality corollary is the named input — optimality already forbids
   `Δdist < 0`, hence constrains where dart-free `F`-branches can sit.
2. **The untried alternative, and the reason this direction is
   derivation-first:** minimizing `dist(·, M)` over admissible `z` at a *fixed*
   balanced pattern is, by **(GR-50)**, a **minimum-cost degree-constrained
   orientation** — a min-cost flow, hence polynomial. Per-matching (b′) is then
   an **exchange statement between two such flow problems** (pattern-free vs
   pattern-fixed), and **flow theory's exchange machinery is untried on this
   arc.** This is the first genuinely new instrument offered to the balance
   layer since (GR-50); if it works it is worth more than the direct route,
   because an exchange argument is `n`-free by construction.

**Finish sub-clause 1 first, and say so separately.** It is a bounded
derivation, it is a *theorem* the arc does not yet have, and landing it makes the
residual exactly one clause. Do not fold it into the sub-clause-2 write-up.

**What counts as a HIT** — a proof of Clause A′ (hence, with (GR-70)(i), of
**per-matching (b′)**). Also valued, on the (GR-29)/(GR-30) precedent: a proof
of a **different constant with the exact boundary named**, or a **witness at
per-matching gap 4** (never 3 — **(GR-67) Cor. 1**'s parity law makes every
per-matching layer gap **even**), which moves (b′) to refuted-with-successor.
State which of the three you got.

**Bars.** Entry 5 is **PROVEN** ((GR-54)) — do not re-attack it. Do **not**
re-run BALB's stratum verification — **(GR-70)(ii)** is EXHAUSTIVE and uncapped
(4780 shapes, 23 939 (shape, matching) pairs, all 96 930 unbalanced
parity-optimal configurations, full `3^n` censuses). Do **not** re-derive
(GR-68)'s move pricing or (GR-67)'s parity law — landed, and they are your
inputs. Do **not** re-open the bounded-deviation **selection** form
(**REFUTED as posed**, (GR-41)+(GR-42): `d(NK(m)) ≥ m/2` unbounded while every
member stays fully-good) — (b′) is a statement about the **gap between two
layers**, and the necklaces are a test bed for it, not a refutation of it. Do
**not** attempt the `|δ| ≤ 2` half: **(GR-69)** settled it — a theorem at
`n_hub ≤ 6`, **FALSE from `n_hub = 8`** at the Wagner shape **V8** — and E1
clause (v) does **not** fire on those witnesses (they are not parity-optimal).
**(GR-64)(R2) / input (Y) is GCOLL's target this wave** — report any
(Y)-relevant by-product as a finding and **do not develop it** (YLOC/BALB's
mutual precedent).

**Riders, verbatim.** As GTMPL's, plus: the **shift-metric layer is UNBOUNDED**
((GR-43), `d_par = d_adm = d_fg = m` exactly at the necklaces), so (b′) must be
stated as a bound on the **difference**, never on `d_adm`, and any figure
quoting a necklace member carries that qualifier. **Disclose the table cap:**
BALB's necklace leg stops at `m = 6` because `gadm.dp_pref`'s table is `2^dim`
(`assert dim ≤ 18`), and **GBAL's `n = 40..60` reach does not transfer** —
(GR-54) needs only balance *existence* (polynomial by (GR-50)) whereas any (b′)
statement needs `d_par(M)`, the exponential object. An exhausted table is not
`∞`.

**Reservation.** §(K-grid) **extends**; labels **(GR-85)–(GR-90)**, **Steps
G104–G109**; driver **`notes/scripts/w4/gflow.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail.

### GFLOW — twenty-sixth direction (eighth fan-out)

**Status: LANDED 2026-08-19 — a HIT of the third kind the spec names: a
different constant, with the exact boundary named.** Second of the eighth
fan-out's five to land. §(K-grid) **extended**, **Steps G104–G109**, labels
**(GR-85)–(GR-90) CLAIMED EXACTLY**. Driver **`notes/scripts/w4/gflow.py`**
(six modes plus `--validate`; the six re-run individually by the coordinator at
landing, foreground, one at a time, all exit 0, every quoted figure reproduced
— `--validate` is exactly those six composed in one process and was not
separately re-run, the AGLU precedent).

**The verdict.** **Sub-clause 1 is PROVEN** ((GR-87)) and in a *stronger* form
than BALB projected: no far-end side condition at all, any chain length,
`γ ∈ F` doubly-blocked included — and BALB's proposed side condition is
exhaustively TRUE at `n_hub ≤ 6` but **FALSE from `n_hub = 8`** (28/2932), so
the projection would not have survived. **Sub-clause 2 is REFUTED as posed**
((GR-88)): a named, independently re-verified `n_hub = 8` witness where a
doubly-blocked *matching* branch prices **exactly 4**, with 4 the exact
ceiling. **Clause A′ itself survives** — at that very witness three other
majority-side branches price `≤ 2` — so the residual is not a *repair*
statement about a branch but a **selection** statement about the set of
branches, which is the pass's structural contribution. The instrument is
**(GR-86)**, the repair-chain theorem: a chain exists **iff** the flipped
pattern is (GR-50)-feasible (0 disagreements at 6 459 208 stratum pairs) and
its price **telescopes**, hence is **independent of chain length** — `n`-free
by construction and certified cap-free to `n_hub = 60`, which is why it reaches
past BALB's `m = 6` table. Iterated, it gives **(GR-89)**:
`d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`, **the arc's first proven
bound of (b′)'s own shape**, modulo one named clause **(GR-R1)**. **(b′) at the
constant 2 stays OPEN**, its exact residual the selection clause **(GR-C2)**.

**Four coordinator adjudications on landing.** *(1)* **The spec's route-2
instrument was wrong, and the correction is right — this is the wave's second
defective spec clause, and again an inherited one.** The spec (from BALB's
hand-off, transcribed by the coordinator) said minimizing `dist(·, M)` at a
fixed balanced pattern is "a min-cost degree-constrained orientation — a
min-cost flow, hence polynomial", and offered flow-exchange machinery as the
route. **(GR-85)** shows the objective is a **parity** count
`#{v : A(v) = 1}`, not a convex flow cost, so flow machinery does not apply on
the cost side; `--adv` (3) independently refutes the naive 2-Lipschitz law a
convex cost would give (a `0 → 4` jump at `n_hub = 4`). The direction then
supplied the exchange instrument that does work. Same shape as GTMPL's
correction one landing earlier: **an inherited hand-off clause, transcribed
into a spec, defective, caught by the direction it primed.** *(2)* **Two
landed BALB readings are corrected, both narrow and both right:** the
doubly-blocked `W`-arithmetic needs **one** deviating extra endpoint for
price `≤ 2`, not two ("both" is the price-**0** condition); and **route 1's
named input runs the wrong way** — (GR-68)'s minimality corollary *caps*
`2|W ∩ S| ≤ |W|` (0 violations at 84 368 legal flip sets), pushing against the
conclusion route 1 wanted. Route 1 is refuted **as an implication**,
independently of whether its conclusion is true. *(3)* **The bound is
`modulo (GR-R1)`, and the write-up says so everywhere** — (GR-R1) has 0 failures at
771 530 configurations and is **not proven**; the draft's own constants table
lays out all five statements with their standing, which is the presentation to
keep. *(4)* **The `n = 30..60` reach is real but narrow:** (GR-86) needs no
`d_par`, which is exactly why it transfers where GBAL's reach did not — and
**(b′) itself still needs `d_par(M)` and is still capped at `m = 6`**, which
the pass states and does not blur.

**Cap disclosure, verified at landing.** (GR-85)'s converse leg is capped at
120 shapes per leg (the forward direction uncapped and exhaustive on the
stratum); the `n = 30..60` legs are one constructed matching + 30 walks per
family, samples not censuses; the `n = 8/10/12` pools are seeded; and the
targeted (GR-C2)-failure hunt at the counting bound's first possible home is
**"not found under a 46-shape / 132-configuration cap — which is not a proof
of nonexistence"**, in the pass's own words.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: the
pass is rank-free and computes no `d_fg`; clause (v) is unfirable (`d_adm ≠ ∞`
asserted at every pair swept). E2: entry 5 is PROVEN and consumed; what is
demoted is BALB's repair route, with (GR-C2)/(GR-R1) named as successors. E3: a
(b′) result, entry 1/(a′) untouched — **stays ARMED by GBAL, not fired.**

**What did NOT move.** **(GR-15) OPEN**; **no gap-map status move on `hK`**;
class uniformity untouched; no `g`-flank (rank-free throughout). Input (Y) and
(GR-64)(R2) untouched — **GCOLL's target this wave** — with one (Y)-adjacent
by-product *reported and not developed*: (GR-85)'s `(A(v))_v` is strictly
finer than the (GR-50) degree data (GR-62) refuted, so it is offered as the
coordinate YLOC's (GR-65) fit identity said an instrument must control. A
by-product **corroboration** rather than a rediscovery: this pass computes
`d_par`/`d_adm` from the full `2^{|E|}` `z`-cube, a construction independent of
`gpsa.parity_census`/`gadm.dp_pref`, and reproduces (GR-70)(ii) exactly
(`{0: 23 444, 2: 495}` over 23 939 pairs) — the wave's first cross-direction
convergence, this time against a *landed* figure rather than a concurrent
sibling. **§(K-grid)'s gap-map status cell is now at 2019 of its 2035-word
cap**: GTMPL's recompute bought 305 words and this landing consumed 289 of
them, so **GCOLL's landing owes a genuine recompute of that cell before adding
its own content** — 16 words is not headroom.

### GCOLL — twenty-seventh direction (eighth fan-out)

**The target — (GR-64)(R2), verbatim as YLOC named it:** *"every habitat shape
carries an anchor matching `M` with `B(M) = 0`"* — **measured at all 4924
inventory shapes, open as a theorem.** YLOC called it *the sharpest cheap
successor the pass produced*, and stated exactly what it buys: **it would prove
the collision mechanism can never obstruct (a′)**, and it is *"a statement about
matchings and small-boundary hub sets alone: no colouring, no rank, no deviation
ladder."*

**Why now.** (a′) is entry 1's only remaining attack and **the only thing
between the arc and E3**, and YLOC's localization failure ((GR-62): full
goodness is not a function of the (GR-50) degree data) leaves the arc without a
chunk-level instrument. (GR-64)(R2) is the one sub-target on that path that is
**strictly smaller than (Y)**, colouring-free and rank-free — the cheapest
genuine progress toward (a′) currently on the board.

**Method.** The statistic is landed: `pack_bound` is (GR-64)'s, `dist_of` /
`fit_M` are (GR-65)'s, and `yloc.py --coll` asserts (GR-64)(i)–(v) at
**209 432 030** (shape, `z`, matching, proper chunk) instances with **3 449 374**
tight. The question is a **proof**, not a bigger sweep: the object is a matching
and the small-boundary hub sets, so the natural attacks are (a) an exchange
argument on the anchor matching (swap along an alternating cycle and show the
collision term cannot rise at every chunk simultaneously), (b) the parity
constraint **(GR-64)(v)** `coll_M(S) ≡ |W_S| (mod 2)`, and (c) the **ceiling
profile** — the per-chunk term reaches its proven maximum 2 **only** at
`(z, exc) ∈ {(3,1), (4,0)}` with `coll = z` — which is a very thin extremal
family to rule out at a well-chosen `M`.

**The second, cruder deliverable, if the theorem resists: (GR-64)(R1)** — the
large-`n` extension of the collision sweep as a **bounded-boundary enumeration**
rather than a `2^M` scan. That converts the measurement from
"exhaustive at `n_hub ≤ 6` plus four named shapes" into a statement with real
reach, and it is a compute question, not a new idea. **Say which you delivered.**

**What counts as a HIT** — a proof of (GR-64)(R2) at every habitat shape.
Also valued: a **witness shape with `B(M) ≥ 1` at every matching**, which per
YLOC's own reading turns (GR-64) into *"a genuine floor on `d_fg`"* — a
strictly informative refutation, not a failure. **A HIT here does NOT fire
E3**: (R2) is a sub-target of (Y), not (a′) itself. State the consequence for
(a′) precisely and **do not fire E3**.

**Bars.** **(b′) / Clause A′ is GFLOW's target this wave** — report any
(b′)-relevant by-product as a finding and **do not develop it**. Do **not**
re-attack (a′)'s **per-matching** variant — **REFUTED** ((GR-59): `min_M` is
load-bearing, 1278 of 24 638 pairs, so no (a′) proof may fix its anchor
matching); note the tension and use it, since (R2) is precisely a statement
about the **existence** of a good anchor, not about fixing one. Do **not**
re-run the bounded {T1, T2} descent (**DEMOTED by witness**, (GR-48)(iii)) or
(GR-58)'s census (landed **exhaustive** at `n_hub ≤ 6`, no cap). Do **not**
re-attempt the (GR-51)-shaped chunk criterion — **(GR-62) refutes it by
witness** (7982 of 217 468 fibres, at 1499/4924 shapes, smallest witness
rank-certified at `n_hub = 4`); the refutation is scoped to a
*(GR-51)-shaped* criterion only, and that scope is **not** an invitation to
re-run it.

**Riders, verbatim.** As GTMPL's. Additionally: **(GR-64)(iii)'s prune is
sound but INCOMPLETE** (1250 of 24 671 killed, incompleteness **7856**) — both
numbers travel with any figure derived from it, and **disjointness is
load-bearing** (the naive sum is unsound against a realized fully-good
distance). **(GR-65)'s fit identity is the bridge** — `dist(m, M)` and
`z_mono(S)` are the **same statistic** — and it is a landed input, not
something to re-derive.

**Reservation.** §(K-grid) **extends**; labels **(GR-91)–(GR-96)**, **Steps
G110–G115**; driver **`notes/scripts/w4/gcoll.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail.

### GCOLL — twenty-seventh direction (eighth fan-out)

**Status: LANDED 2026-08-19 — (GR-64)(R2) is REFUTED by witness, and
(GR-64)(R1) is DELIVERED. Both deliverables landed; the fifth and last of the
eighth fan-out, which this closes.** §(K-grid) **extended**, **Steps
G110–G115**, labels **(GR-91)–(GR-96) CLAIMED EXACTLY**. Driver
**`notes/scripts/w4/gcoll.py`** (nine modes; `--validate` is ~1530 s and does
**not** fit a sitting, so it ran — by the dispatch and again by the coordinator
at landing — as a recorded **four-invocation foreground split**, one at a time,
all exit 0, every quoted figure reproduced).

**The three attacks the spec named collapsed into one.** (GR-91) rewrites the
collision statistic in **slack** form: `coll_M(S) = z(S) − s_M(S)` with
`s_M(S)` **always even** (a 2-factor crosses a cut evenly), so a positive
(GR-64) term is exactly a **zero-slack** chunk and equals that chunk's demand
`r(S) ∈ {1,2}`. That collapses attack (c) — the spec's "thin extremal family"
at `(z,exc) ∈ {(3,1),(4,0)}` — into the same condition as the `r = 1` family:
**not thinner, identical**. Attack (a), the exchange argument, was never
needed, because **(GR-93)** supplies a better instrument: a violated chunk's
hub set is a **union of cycles of the 2-factor**, so violation detection at a
fixed `M` is a `2^{c(F)}` search with **no chunk scan** (max 3 subsets on the
inventory against `2^18` masks), set-equal to the landed `2^M` ground truth at
all 24 671 (shape, matching) pairs.

**The positive half is a theorem, not a measurement.** **(GR-94)**: `B(M) = 0`
whenever `M` avoids the (≤ 2) length-5 branches and either `E ∖ M` is
Hamiltonian or the cyclic edge connectivity is ≥ 6. The Hamiltonian condition
alone covers **4924/4924** inventory shapes and **39 687/39 689** of the
complete `n_hub = 8` stratum — so on both exhaustively-swept strata (R2) is
**proven**, and the refutation sits exactly where the hypothesis fails.

**The refutation.** **(GR-95)**: of the Petersen graph's **36 860** habitat
length assignments, **180** have `min_M B(M) = 1` — **every** anchor matching
pays. Certified four ways: the landed `2^M` scan reproduces `min_M B` at all
180 (0 disagreements); **`gridcol.class_shape`** — the *canonical* habitat
certificate, with the matroid rank inside rather than merely (GR-25) —
accepts all 180 (0 rejections); the matching enumeration is complete (6 of 6,
no cap); and a local criterion is asserted at all **221 160** (shape, matching)
pairs. Exactly **two** mechanisms, both demand 1. The refutation needs the
excess **spread** and is a property of the **length assignment**, not of the
graph — the same graph carries 36 680 assignments with `min_M B = 0`, which is
F13 control (6). **(GR-96)** then delivers **(GR-64)(R1)**: `min_M B(M)` exact
and uncapped on the chunk side at **81 482** shapes, including the ten cases
(GR-64) had disclosed as out of reach.

**Three coordinator adjudications on landing.**

*(1)* **The consequence for (a′) is precisely bounded, and the pass got it
right.** (R2) was *sufficient* for "the collision mechanism can never obstruct
(a′)"; its refutation removes that sufficiency and **refutes nothing about
(a′)**. The E1(iv)/E2 detector reports **0**: at every witness
`d_adm ∈ {2,3}` (exact, uncapped `z`-cube) against a floor of 1. The successor
is strictly weaker and strictly enough — **collision dominance
`min_M B(M) ≤ d_adm`**, (GR-96)(iii), **OPEN**, now with its first 180 shapes
of *non-vacuous* content and vacuous at the other 81 302. **This is a genuine
gap-map status move**, the wave's only one: (R2) → REFUTED, (R1) → DELIVERED.

*(2)* **The Plesník citation is coordinator-verified against a primary
source.** (GR-94)(iv)'s existence clause rests on **Ján Plesník,
*Connectivity of Regular Graphs and the Existence of 1-Factors*, Matematický
časopis **22** (1972), no. 4, 310–318** — checked at EUDML: author, title,
journal, volume, issue and page range all correct, and the quoted statement
("an `(m−1)`-edge-connected `m`-regular graph of even order has a 1-factor
avoiding any prescribed `m−1` edges") matches the paper's own abstract. The
pass names its own gap correctly: the theorem is stated for **graphs** while
habitat shapes are **multigraphs**, and it is **not load-bearing** — the
`X`-avoiding matching is *exhibited* at every one of the 4924 + 39 689 + 36 860
shapes touched, so (iv) is used only for the general statement. Recorded as
true-modulo-a-named-gap, which is the right standing.

*(3)* **The pass flagged the in-flight tree correctly, and did nothing about
it.** GCOLL observed six shared files carrying uncommitted changes (a sibling
landing of mine in progress) and confirmed its own label range was still 0-hit
outside reservation bookkeeping rather than assuming it. That is the serial-
landing protocol working as designed from the dispatch side.

**Cap disclosure, verified at landing.** Still capped, and stated as such:
`n_hub = 10` **beyond Petersen** and `n_hub ≥ 12` **beyond the necklaces** have
**no search run** (no enumerator; `cubic_iso_classes(8)` alone costs ~116 s).
The 180 witnesses are **not** claimed minimal at `n_hub = 10` — only Petersen
is swept there. The `2^{c(F)}` cost claim is a statement about `c(F)`,
**measured** `∈ {1,2}` on the inventory, not bounded in general. All seven F13
controls fire.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 **stays
ARMED by GBAL, not fired**; entry 1, (a′), input (Y) and (GR-15) take no status
change.

**What did NOT move.** (GR-15) OPEN; class uniformity untouched; (a′) still
open and still carrying **no bar**. One by-product **reported, not developed**:
`d_fg = d_adm` at all 180 witnesses, so **(a′) holds** at 180 `n_hub = 10`
non-Hamiltonian shapes — new territory, since (GR-58)'s census is `n_hub ≤ 6`
plus two necklaces — offered as corroboration, not a proof, with the evaluator
cross-checked against `gorient.fully_good_scan` at 5640 colourings. The (b′)
bar was respected (one noted by-product, undeveloped). §(K-grid)'s status cell
was recomputed again before this landing's content went in and its cap then
**deliberately bumped** 2035 → 2715, the row having absorbed **eighteen** new
theorems across the wave; reason recorded in `notes/check-gapmap-cells.py`.

### OSCHU — twenty-eighth direction (eighth fan-out)

**The target — (a₁) class-uniformly**, verbatim from ZNEQ's input-(a) hand-off:
*at some pencil chart point where `H = G − v − a` has independent rows,
`D = {m(b) − m(c) : m ∈ Mot(H)}` contains **no** pencil `M̂ ∧ w` with `w` on the
line `pt(b) pt(c)`* — equivalently the **Schubert non-jump**
`dim(D ∩ (M̂ ∧ W)) ≤ 1`, with `D` the far framework `H`'s relative twist space
and `W` the hub line's 2-space. **One condition, `x₁`-free, `λ`-free,
stratum-free, one-point decidable.** Measured to fail **nowhere** (GCD degree 0
and `dim(D ∩ M̂ ∧ W) = 1` at 32/32 POOL-ZF frames). **A recipe is what is
missing** — exactly as for (OC-19) input (c).

**The route to try FIRST, from the same hand-off.** `D` is the relative twist
space of `H` with **no** hinge deleted and **no** weld, so §(K-out) **(OC-18)**'s
`H/X`-rigidity criterion and `D` are **near neighbours**: `H/X` rigid forces
`W₁ = 0`, and `D` is the un-welded analogue. **Second:** `D` depends only on the
`H`-part, so **(OC-28)(i)** makes this too a statement about `G`'s **own** chart
— which is what would make it class-uniform rather than per-split.

**Why now, and why this rather than (OC-19) input (c).** Input (c) is OCON's #1
by value but is **(GR-15)-flavoured** — a rank condition inside a
pattern-colouring existence question — so it re-enters the arc's oldest missing
technology. (a₁) is the *same object class* ((OC-20)'s perp form, a
subspace-meets-subspace count in `Λ²K⁴`) with **no colouring quantifier**, and
after ZNEQ it is the **only** half of input (a) that can be the binding
obstruction: the `s₀` half is **necessary for `hK`** and therefore
**dominated** ((OC-24), (OC-28)).

**The cheap secondary leg, folded in deliberately: the (a₂) cross-pool
re-keying.** By **(OC-28)(iii)** the `s₀` half is implied by §(K-grid)
**(GR-10)** and free at **907/907** of that pool, so the cheapest genuine
progress there *"is **not** a new argument but a re-keying: check that every
§(K-out) class shape carrying a length-4 companion is in §(K-grid)'s certified
set (the two pools are keyed differently, (OC-28)(a))"* — **a combinatorial job
with no new mathematics**, and the transfer itself is already **machinery**
(`zneq --transfer` turns any target-rank chart point of `G` into a
guard-accepted point of `Z` on every eligible split's `G′`-chart, 30/30). Run
it, and state plainly that the result stays **CONDITIONAL** on (GR-10), which
is itself **OPEN** (its min-max form refuted as posed, the statement standing).
§(K-out) hand-off item 4 — the one-hub-neighbour extension of the slide,
(OC-21)'s second bullet, *"a cheap `--wide`-style leg, too small to be a
direction"* — may be folded in as a third leg if budget allows; it is the
lowest priority of the three.

**What counts as a HIT** — a class-uniform proof of (a₁) (with the (a₂) leg,
that is input (a) reduced to (GR-10) alone). Also valued: a **shape where the
non-jump fails**, which per (OC-25)/(OC-26) is a **(K-tight) event** at that
split — routes A and B dead there, `hK` at the shape **untouched** — and which
must be reported as such and **not** as a PENCIL event. Getting that distinction
right is load-bearing: ZNEQ's own spec was corrected on exactly this point.

**Bars.** Do **not** re-derive **chart irreducibility** — §(K-chart)
**(CH-1)(a)** is PROVEN, unconditional at `Γ = G′`; **cite** it. Do **not**
attack **(OC-19) input (c)** (`H/X` rigid class-uniformly) — OCON's verdict
stands and it is deliberately not this wave's. Do **not** pursue any
**counting / matroid route to (OUT)'s hypothesis** — **(OC-3)** refutes the
whole class (`{λ₁ = 0}` is nonempty at every class shape's chart). Do **not**
push a constructed point to `p⁺` (§(K-out) *What would change this* item 4),
the coupled two-end slide (item 5), or any §(K-frame) *What would change this*
item (ii)–(iv). Do **not** re-run (OC-27)'s witness census (138/138, caps
disclosed). **The `σ > 0` hunt is SIGZ's target this wave** — if a by-product
bears on it, report it as a finding and **do not develop it**.

**Riders, verbatim.** The standing **(OC-7) rule**: no `place_pencil_general`
battery may be quoted as a **rate** or as evidence about a **generic** chart
point; POOL-G figures are quoted over the **318 coincidence-free** frames,
never the raw 357. **POOL-G and POOL-S are pinned and disjoint** — not
aggregated, not re-sampled. Any census this direction runs reports **witnesses,
never a rate**, with caps disclosed. **`Z ≠ ∅` alone does NOT give (OC-8)**:
the reduction needs openness **plus** irreducibility **plus** a witness, and
`--control`'s three constructed points in `Z` with `L_b ⊆ R₁` are why.

**Harness debt, carried in and payable here if convenient.** `ocon.meet` (the
dimension-asserting wrapper of `lambda.span_meet`) now has **two** consumers,
tripping `notes/scripts/README.md` §2 rule 2's move-down trigger — a dated
**unpaid** debt item recorded by ZNEQ. This direction is the natural third
consumer; if it uses `ocon.meet`, say so and either pay the debt or re-date it.

**Reservation.** §(K-out) **extends**; labels **(OC-29)–(OC-34)**, **Steps
O25–O30**; driver **`notes/scripts/w4/oschu.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail. **Two directions
share §(K-out) this wave** (OSCHU and SIGZ) — the protection is the **disjoint
reserved range**, not the section, exactly as three directions shared §(K-grid)
at the sixth and seventh fan-outs.

### GCOLL — twenty-seventh direction (eighth fan-out)

**Status: LANDED 2026-08-19 — (GR-64)(R2) is REFUTED by witness, and
(GR-64)(R1) is DELIVERED. Both deliverables landed; the fifth and last of the
eighth fan-out, which this closes.** §(K-grid) **extended**, **Steps
G110–G115**, labels **(GR-91)–(GR-96) CLAIMED EXACTLY**. Driver
**`notes/scripts/w4/gcoll.py`** (nine modes; `--validate` is ~1530 s and does
**not** fit a sitting, so it ran — by the dispatch and again by the coordinator
at landing — as a recorded **four-invocation foreground split**, one at a time,
all exit 0, every quoted figure reproduced).

**The three attacks the spec named collapsed into one.** (GR-91) rewrites the
collision statistic in **slack** form: `coll_M(S) = z(S) − s_M(S)` with
`s_M(S)` **always even** (a 2-factor crosses a cut evenly), so a positive
(GR-64) term is exactly a **zero-slack** chunk and equals that chunk's demand
`r(S) ∈ {1,2}`. That collapses attack (c) — the spec's "thin extremal family"
at `(z,exc) ∈ {(3,1),(4,0)}` — into the same condition as the `r = 1` family:
**not thinner, identical**. Attack (a), the exchange argument, was never
needed, because **(GR-93)** supplies a better instrument: a violated chunk's
hub set is a **union of cycles of the 2-factor**, so violation detection at a
fixed `M` is a `2^{c(F)}` search with **no chunk scan** (max 3 subsets on the
inventory against `2^18` masks), set-equal to the landed `2^M` ground truth at
all 24 671 (shape, matching) pairs.

**The positive half is a theorem, not a measurement.** **(GR-94)**: `B(M) = 0`
whenever `M` avoids the (≤ 2) length-5 branches and either `E ∖ M` is
Hamiltonian or the cyclic edge connectivity is ≥ 6. The Hamiltonian condition
alone covers **4924/4924** inventory shapes and **39 687/39 689** of the
complete `n_hub = 8` stratum — so on both exhaustively-swept strata (R2) is
**proven**, and the refutation sits exactly where the hypothesis fails.

**The refutation.** **(GR-95)**: of the Petersen graph's **36 860** habitat
length assignments, **180** have `min_M B(M) = 1` — **every** anchor matching
pays. Certified four ways: the landed `2^M` scan reproduces `min_M B` at all
180 (0 disagreements); **`gridcol.class_shape`** — the *canonical* habitat
certificate, with the matroid rank inside rather than merely (GR-25) —
accepts all 180 (0 rejections); the matching enumeration is complete (6 of 6,
no cap); and a local criterion is asserted at all **221 160** (shape, matching)
pairs. Exactly **two** mechanisms, both demand 1. The refutation needs the
excess **spread** and is a property of the **length assignment**, not of the
graph — the same graph carries 36 680 assignments with `min_M B = 0`, which is
F13 control (6). **(GR-96)** then delivers **(GR-64)(R1)**: `min_M B(M)` exact
and uncapped on the chunk side at **81 482** shapes, including the ten cases
(GR-64) had disclosed as out of reach.

**Three coordinator adjudications on landing.**

*(1)* **The consequence for (a′) is precisely bounded, and the pass got it
right.** (R2) was *sufficient* for "the collision mechanism can never obstruct
(a′)"; its refutation removes that sufficiency and **refutes nothing about
(a′)**. The E1(iv)/E2 detector reports **0**: at every witness
`d_adm ∈ {2,3}` (exact, uncapped `z`-cube) against a floor of 1. The successor
is strictly weaker and strictly enough — **collision dominance
`min_M B(M) ≤ d_adm`**, (GR-96)(iii), **OPEN**, now with its first 180 shapes
of *non-vacuous* content and vacuous at the other 81 302. **This is a genuine
gap-map status move**, the wave's only one: (R2) → REFUTED, (R1) → DELIVERED.

*(2)* **The Plesník citation is coordinator-verified against a primary
source.** (GR-94)(iv)'s existence clause rests on **Ján Plesník,
*Connectivity of Regular Graphs and the Existence of 1-Factors*, Matematický
časopis **22** (1972), no. 4, 310–318** — checked at EUDML: author, title,
journal, volume, issue and page range all correct, and the quoted statement
("an `(m−1)`-edge-connected `m`-regular graph of even order has a 1-factor
avoiding any prescribed `m−1` edges") matches the paper's own abstract. The
pass names its own gap correctly: the theorem is stated for **graphs** while
habitat shapes are **multigraphs**, and it is **not load-bearing** — the
`X`-avoiding matching is *exhibited* at every one of the 4924 + 39 689 + 36 860
shapes touched, so (iv) is used only for the general statement. Recorded as
true-modulo-a-named-gap, which is the right standing.

*(3)* **The pass flagged the in-flight tree correctly, and did nothing about
it.** GCOLL observed six shared files carrying uncommitted changes (a sibling
landing of mine in progress) and confirmed its own label range was still 0-hit
outside reservation bookkeeping rather than assuming it. That is the serial-
landing protocol working as designed from the dispatch side.

**Cap disclosure, verified at landing.** Still capped, and stated as such:
`n_hub = 10` **beyond Petersen** and `n_hub ≥ 12` **beyond the necklaces** have
**no search run** (no enumerator; `cubic_iso_classes(8)` alone costs ~116 s).
The 180 witnesses are **not** claimed minimal at `n_hub = 10` — only Petersen
is swept there. The `2^{c(F)}` cost claim is a statement about `c(F)`,
**measured** `∈ {1,2}` on the inventory, not bounded in general. All seven F13
controls fire.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 **stays
ARMED by GBAL, not fired**; entry 1, (a′), input (Y) and (GR-15) take no status
change.

**What did NOT move.** (GR-15) OPEN; class uniformity untouched; (a′) still
open and still carrying **no bar**. One by-product **reported, not developed**:
`d_fg = d_adm` at all 180 witnesses, so **(a′) holds** at 180 `n_hub = 10`
non-Hamiltonian shapes — new territory, since (GR-58)'s census is `n_hub ≤ 6`
plus two necklaces — offered as corroboration, not a proof, with the evaluator
cross-checked against `gorient.fully_good_scan` at 5640 colourings. The (b′)
bar was respected (one noted by-product, undeveloped). §(K-grid)'s status cell
was recomputed again before this landing's content went in and its cap then
**deliberately bumped** 2035 → 2715, the row having absorbed **eighteen** new
theorems across the wave; reason recorded in `notes/check-gapmap-cells.py`.

### OSCHU — twenty-eighth direction (eighth fan-out)

**Status: LANDED 2026-08-19 — (a₁) is half PROVEN and half reduced to ONE
determinant; the (a₂) leg is a HIT that corrects a figure the arc has quoted
since (OC-28).** Fourth of the eighth fan-out's five to land. §(K-out)
**extended**, **Steps O25–O30**, labels **(OC-29)–(OC-34) CLAIMED EXACTLY**.
Driver **`notes/scripts/w4/oschu.py`** (five modes, all re-run by the
coordinator at landing in the foreground, one at a time, explicit timeouts, all
exit 0, every quoted figure reproduced; the census is deliberately split across
`--census1`/`--census2` because `--gtarget` alone runs 466–515 s and a combined
mode would breach the 600 s budget).

**The verdict.** **(OC-29)** shows the Schubert 4-space is not a new object at
all: `M̂ ∧ W = L_b ⊕ L_c`, §(K-out)'s **own** hub pencils, with Klein perp
`⟨C(M), C(bc)⟩` — from which `dimK ≥ 1` **always** (3 + 4 > 6), and §(K-tight)
*Step 2* item 5's `★r ∥ C(M)` falls out inside the dictionary. **(OC-30)**
identifies the bad set on `M` **exactly** — the transversals of `M` and `bc`
lying in `D` — in a five-row classification that recovers (OC-26)(ii) by a
route disjoint from ZNEQ's and is asserted equal to its ℚ[t]-GCD at every
frame. **(OC-31)** is the pass's sharpest positive: at **every** target-rank
chart point of the **whole graph `G`**, (CH-2)'s tower gives `pt(v) ∈ Π(b)` and
`pt(a) ∈ Π(c)`, so `C(vb) ∈ L_b` and `C(ac) ∈ L_c` come **for free** — two
lines of a projective plane always meet — forcing **`dimK ≤ 2`**. Hence **`hK`
at ONE chart point of `G` kills (OC-26)(ii)'s `dimK ≥ 3` disjunct at every
eligible split of that shape simultaneously**, and **(OC-32)** shows a third
such generator is structurally unavailable, so the bound is exact rather than
merely observed. **(OC-33)** reduces what is left to **one 3×3 determinant**:
the surviving disjunct forces `Q|_D` degenerate, so `rank(Q|_D) = 3` at one
target-rank `G`-point **implies input (a)** at that (shape, split) —
`x₁`-free, `λ`-free, stratum-free, and evaluated at a point the grid route
already constructs.

**Four coordinator adjudications on landing.**

*(1)* **Two more defective spec clauses, both accepted — taking the wave to
five.** First: the spec restated (a₁) as *"equivalently the Schubert non-jump
`dim(D ∩ M̂ ∧ W) ≤ 1`"*. Given (OC-29)'s `dimK ≥ 1`, that reads as `dimK = 1`
exactly, which is **strictly sufficient, not equivalent**; the honest form is
`dimK ≤ 2` **and** no ruling in `D`, and the pass constructs `dimK = 3` with
`rank(Q|_D) = 3` all-bad to show (OC-33) genuinely needs (OC-31). This clause
was **inherited from ZNEQ's landed hand-off** and transcribed by the
coordinator — the same provenance as GTMPL's and GFLOW's. Second: the spec
instructed the (a₂) leg to *"state plainly that the result stays CONDITIONAL on
(GR-10)"*. **That is wrong at the shapes the pass certifies directly** —
(OC-28)(iii) makes the `s₀` half free wherever a certificate is *exhibited*,
and exhibiting it is precisely what (OC-34) does at 155 classes. Only the
**class-uniform** statement still needs (GR-10). This one is the coordinator's
own, written at prep.

*(2)* **The (a₂) leg is a HIT, and it corrects an arc-wide figure.** §(K-grid)'s
907 *labelled* certified shapes are only **75 isomorphism classes**, and they
cover just **19** of §(K-out)'s **174** length-4-companion classes — **a factor
of nine** smaller than the raw count suggests. The remaining **155 are
certified directly, 155/155, 0 misses, 0 cap hits**, class predicate asserted
per shape. So the `s₀` half is free at **all 174**, and the re-keying the
coordinator commissioned as "cheap bookkeeping, no new mathematics" turned out
to matter: quoting 907 as coverage of §(K-out)'s population was a category
error between labelled shapes and isomorphism classes.

*(3)* **The residue's cheapest attack stops on a FIELD obstruction, not a
missing idea, and that is a design decision referred up.** What remains is
`rank(Q|_D) = 3` class-uniformly. If `D` is `⋆`-invariant it splits into `±`
eigen-blocks with `B = ±⟨·,·⟩`, so over a **real** field nondegeneracy is two
lines — and `D` **is** `⋆`-invariant at a σ-fixed grid configuration
((AC-2)/(AC-4)) — but those grids are **ℚ(i)-only** and no real σ-fixed
configuration exists. The route therefore needs `closure.Gauss` (the arc's only
non-`ℚ` scalar class, deliberately private to `closure`) moved down, which
`notes/scripts/README.md` §2 explicitly calls a deliberate design choice rather
than a mechanical move-down. Recorded as a **design item**, unpaid, and the
route is labelled a route, not a result — it carries **no driver**, the harness
being ℚ-only. **The harness half is UNBLOCKED as of 2026-08-20:** the design
item was adjudicated (move it down) and PAID by the harness move-down round —
`Gauss` now lives in `exactcore`, re-exported by `closure`, so this route may
use exact `ℚ(i)` directly. Everything else about it is unchanged: still a
route, still driverless.

*(4)* **The pass's criticism of the SIGZ landing is factually wrong, and the
wording that invited it is the coordinator's.** OSCHU reports that "the wave's
mandated §(K-out) status-cell recompute did not happen", reading the cell's end
state (666) against the spec's "≤ 560". The recompute **did** happen: at SIGZ's
landing the pre-existing content went **649 → 431 words, a 34 % reduction**,
well past the target, after which SIGZ's own 235-word block brought the cell to
666. The misreading is invited by the coordinator's own asymmetric wording —
the §(K-grid) obligation said "recompute … **before adding its own content**"
and the §(K-out) one omitted that clause — so the fix is to the spec, not to
the landing. OSCHU is nonetheless right that the cell was tight, and this
landing pays for itself: a further ~65 words came off the oldest
(OC-1)–(OC-25) material before its own content was added.

**Cap disclosure, verified at landing.** Every figure is a **witness, never a
rate**; POOL-G/POOL-S untouched; POOL-OS/OQ/OG/OR/OC2 pinned and disjoint from
every earlier pool. The E1 detector is real, not a formality — 155 certificate
hunts, each carrying a filter-passing both-block-certified colouring, probe cap
48 disclosed, 0 misses. The `--gtarget` and census legs take the **first**
guard-accepted target-rank point per class, which is a witness per class and
not a sample of the fibre.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: no
g-flank, on a real detector. E2: the target is **reduced**, not refuted or
unprovable-as-posed. E3: **stays ARMED by GBAL, neither fired nor disarmed.**

**Event classification, as the spec required and the pass got right.** A
non-jump failure is a **(K-tight) event at that split** — routes A and B dead
there, `hK` at the shape **untouched** — and **not** a PENCIL event; only
`{σ = 0} = ∅` is PENCIL. (OC-31) sharpens the (K-tight) side: wherever `hK`
holds at even one point, the `dimK ≥ 3` route to failure is **closed**, leaving
only `rank(Q|_D) ≤ 2`.

**What did NOT move.** **No gap-map status moves**; `hK`, (OC-8), (GR-15) and
class uniformity are exactly where they were. §(K-out)'s status cell was
recomputed a second time in one day and then, the section having absorbed
**eleven** new theorems ((OC-29)–(OC-39)) between SIGZ and OSCHU, its cap was
**deliberately bumped** 800 → 950 with the reason recorded in
`notes/check-gapmap-cells.py` — recompute first, twice, then bump, which is the
script's own sanctioned order.

### SIGZ — twenty-ninth direction (eighth fan-out)

**Newly authorized this session, and the arc's first authorized DISPROOF
direction.** It is ZNEQ's input-(a) hand-off item 3, held out of the
dispatchable pool since 2026-08-19 pending adjudication, released by the
user's **"Authorize the hunt"** selection at this session's check-in on the
terms quoted in this fan-out's header. **The direction-A pivot rule is in
force**, verbatim: *"If half 2 fails at any shape, **stop and report
immediately**: the phase's target theorem would be false … That is a
phase-redefining event for the user to adjudicate, not a result to build on."*
Read for this direction: **a hit is reported and NOT built on.**

**The target.** By **(OC-23)**, `s₀ = corank R(H)` at **every** legal chart
point, so `{σ = 0}` is the locus where the far framework `H = G − v − a` has
independent rows. By **(OC-24)**, **`{σ = 0} = ∅` at a class shape makes `hK`
FALSE there** (`E(H) ⊆ E(G)`, `G` tight with `def(G) = 0`, so a self-stress of
`H` at every chart point is a self-stress of `G` blocking its own Tay target).
The hunt: **is there a class shape — inside `hK`'s habitat — at which
`σ > 0` everywhere?** The only known failure mechanism is a **self-stress of a
short theta sub-multigraph inside `H`** (§(K-flank) *F5(d)*: at `P21`, 5 of 35
valid seeds, support the theta `{12, 13, 23a, 23b}`, **12 edges, line rank 6**,
forcing `dim R_a = 0`).

**The obstruction the hunt must confront head-on, and why this direction has
two valuable outcomes rather than one.** `P21` **fails `hnoRigid`** — it is a
**(K-res) residual, not a tight class member** — so *Step O24*'s only recorded
mechanism sits **outside** `hK`'s habitat. And the gap map's `P21` row records
more than that: **(S5)'s `(3,3)` row-dependence mechanism is proven impossible
inside tight + `hnoRigid`**, because `C_k` rigid for `k ≤ 6` forces
`ℓ₁ + ℓ₂ ≥ 7`. So:

- **A HIT** — a class shape (tight, `def(G) = 0`, `hnoRigid`) with
  `{σ = 0} = ∅` — is a **PENCIL event**: `hK` is FALSE there, the phase's
  target needs restating, and the return **stops** at that and reports. Name
  the shape, the split, the stress support, its line rank, and **rank-certify**
  it; then stop. Do **not** develop consequences, do **not** re-plan the arc,
  do **not** touch any gap-map status.
- **A PROOF THAT THE MECHANISM CANNOT OCCUR inside tight + `hnoRigid`** —
  i.e. pushing the `ℓ₁ + ℓ₂ ≥ 7` bound (or its theta-multigraph generalization)
  to exclude *every* `H`-supported theta stress at a class shape — makes
  **(a₂) free at class shapes unconditionally**, which is **strictly stronger
  than (OC-28)'s conditional reduction** (that one is conditional on (GR-10),
  itself open). **Say which of the two you got**, and if neither, say exactly
  which theta lengths remain uncovered.

**Method.** Exact ℚ throughout; the object is a self-stress space, so a
**rank/corank assert on every sampled framework** is mandatory (the
`plane_basis` precedent — a degenerate sampler silently contaminated several
passes' recorded escape-failure figures). Enumerate class shapes by the theta
sub-multigraphs their `H` can carry rather than by sampling seeds blindly: the
theta's branch-length triple is the natural index, `ℓ₁ + ℓ₂ ≥ 7` is the landed
constraint, and §(K-Λ) **(Λ4)**'s branch calculus reduces class membership to a
finite statement about the hub multigraph `G°` alone. `{σ = 0}` is a **proper
open** — witnessed as such at `P21` (5 of 35 valid seeds off it) — so
`{σ = 0} = ∅` is a **closed** condition to certify, never something a finite
sample can establish: a shape where every *sampled* seed has `σ > 0` is
**"not found under cap C"**, not a hit. **State that boundary explicitly in the
return.** A hit needs an argument (or an exhaustive, uncapped chart-level
certificate), not a tally.

**Bars.** Do **not** re-derive §(K-chart) (CH-1)/(CH-2) — landed; cite. Do
**not** work the target-rank half of input (a) — **(a₁) is OSCHU's target this
wave**; report by-products as findings and do not develop them. Do **not** move
any gap-map status: `{σ = 0}`'s row, (OC-8), (GR-15), class uniformity and `hK`
all stay exactly where they are, **whatever this direction finds** — a status
move on a PENCIL event is a user adjudication, not a landing. Do **not** re-run
the `P21` battery (`flanks.py --rzero`, landed: 30/5/5 seeds, `dim U = 1`, 8/8
placements fail).

**Riders, verbatim.** As OSCHU's, plus: every figure is a **witness, never a
rate**, with the cap disclosed; and `P21` figures carry the **`hnoRigid`-false
qualifier** in every sentence that quotes them, because the whole question is
whether the mechanism crosses into the habitat.

**Reservation.** §(K-out) **extends**; labels **(OC-35)–(OC-40)**, **Steps
O31–O36**; driver **`notes/scripts/w4/sigz.py`**. Owning section stays
authoritative; return any unconsumed remainder to the tail.

### GCOLL — twenty-seventh direction (eighth fan-out)

**Status: LANDED 2026-08-19 — (GR-64)(R2) is REFUTED by witness, and
(GR-64)(R1) is DELIVERED. Both deliverables landed; the fifth and last of the
eighth fan-out, which this closes.** §(K-grid) **extended**, **Steps
G110–G115**, labels **(GR-91)–(GR-96) CLAIMED EXACTLY**. Driver
**`notes/scripts/w4/gcoll.py`** (nine modes; `--validate` is ~1530 s and does
**not** fit a sitting, so it ran — by the dispatch and again by the coordinator
at landing — as a recorded **four-invocation foreground split**, one at a time,
all exit 0, every quoted figure reproduced).

**The three attacks the spec named collapsed into one.** (GR-91) rewrites the
collision statistic in **slack** form: `coll_M(S) = z(S) − s_M(S)` with
`s_M(S)` **always even** (a 2-factor crosses a cut evenly), so a positive
(GR-64) term is exactly a **zero-slack** chunk and equals that chunk's demand
`r(S) ∈ {1,2}`. That collapses attack (c) — the spec's "thin extremal family"
at `(z,exc) ∈ {(3,1),(4,0)}` — into the same condition as the `r = 1` family:
**not thinner, identical**. Attack (a), the exchange argument, was never
needed, because **(GR-93)** supplies a better instrument: a violated chunk's
hub set is a **union of cycles of the 2-factor**, so violation detection at a
fixed `M` is a `2^{c(F)}` search with **no chunk scan** (max 3 subsets on the
inventory against `2^18` masks), set-equal to the landed `2^M` ground truth at
all 24 671 (shape, matching) pairs.

**The positive half is a theorem, not a measurement.** **(GR-94)**: `B(M) = 0`
whenever `M` avoids the (≤ 2) length-5 branches and either `E ∖ M` is
Hamiltonian or the cyclic edge connectivity is ≥ 6. The Hamiltonian condition
alone covers **4924/4924** inventory shapes and **39 687/39 689** of the
complete `n_hub = 8` stratum — so on both exhaustively-swept strata (R2) is
**proven**, and the refutation sits exactly where the hypothesis fails.

**The refutation.** **(GR-95)**: of the Petersen graph's **36 860** habitat
length assignments, **180** have `min_M B(M) = 1` — **every** anchor matching
pays. Certified four ways: the landed `2^M` scan reproduces `min_M B` at all
180 (0 disagreements); **`gridcol.class_shape`** — the *canonical* habitat
certificate, with the matroid rank inside rather than merely (GR-25) —
accepts all 180 (0 rejections); the matching enumeration is complete (6 of 6,
no cap); and a local criterion is asserted at all **221 160** (shape, matching)
pairs. Exactly **two** mechanisms, both demand 1. The refutation needs the
excess **spread** and is a property of the **length assignment**, not of the
graph — the same graph carries 36 680 assignments with `min_M B = 0`, which is
F13 control (6). **(GR-96)** then delivers **(GR-64)(R1)**: `min_M B(M)` exact
and uncapped on the chunk side at **81 482** shapes, including the ten cases
(GR-64) had disclosed as out of reach.

**Three coordinator adjudications on landing.**

*(1)* **The consequence for (a′) is precisely bounded, and the pass got it
right.** (R2) was *sufficient* for "the collision mechanism can never obstruct
(a′)"; its refutation removes that sufficiency and **refutes nothing about
(a′)**. The E1(iv)/E2 detector reports **0**: at every witness
`d_adm ∈ {2,3}` (exact, uncapped `z`-cube) against a floor of 1. The successor
is strictly weaker and strictly enough — **collision dominance
`min_M B(M) ≤ d_adm`**, (GR-96)(iii), **OPEN**, now with its first 180 shapes
of *non-vacuous* content and vacuous at the other 81 302. **This is a genuine
gap-map status move**, the wave's only one: (R2) → REFUTED, (R1) → DELIVERED.

*(2)* **The Plesník citation is coordinator-verified against a primary
source.** (GR-94)(iv)'s existence clause rests on **Ján Plesník,
*Connectivity of Regular Graphs and the Existence of 1-Factors*, Matematický
časopis **22** (1972), no. 4, 310–318** — checked at EUDML: author, title,
journal, volume, issue and page range all correct, and the quoted statement
("an `(m−1)`-edge-connected `m`-regular graph of even order has a 1-factor
avoiding any prescribed `m−1` edges") matches the paper's own abstract. The
pass names its own gap correctly: the theorem is stated for **graphs** while
habitat shapes are **multigraphs**, and it is **not load-bearing** — the
`X`-avoiding matching is *exhibited* at every one of the 4924 + 39 689 + 36 860
shapes touched, so (iv) is used only for the general statement. Recorded as
true-modulo-a-named-gap, which is the right standing.

*(3)* **The pass flagged the in-flight tree correctly, and did nothing about
it.** GCOLL observed six shared files carrying uncommitted changes (a sibling
landing of mine in progress) and confirmed its own label range was still 0-hit
outside reservation bookkeeping rather than assuming it. That is the serial-
landing protocol working as designed from the dispatch side.

**Cap disclosure, verified at landing.** Still capped, and stated as such:
`n_hub = 10` **beyond Petersen** and `n_hub ≥ 12` **beyond the necklaces** have
**no search run** (no enumerator; `cubic_iso_classes(8)` alone costs ~116 s).
The 180 witnesses are **not** claimed minimal at `n_hub = 10` — only Petersen
is swept there. The `2^{c(F)}` cost claim is a statement about `c(F)`,
**measured** `∈ {1,2}` on the inventory, not bounded in general. All seven F13
controls fire.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 **stays
ARMED by GBAL, not fired**; entry 1, (a′), input (Y) and (GR-15) take no status
change.

**What did NOT move.** (GR-15) OPEN; class uniformity untouched; (a′) still
open and still carrying **no bar**. One by-product **reported, not developed**:
`d_fg = d_adm` at all 180 witnesses, so **(a′) holds** at 180 `n_hub = 10`
non-Hamiltonian shapes — new territory, since (GR-58)'s census is `n_hub ≤ 6`
plus two necklaces — offered as corroboration, not a proof, with the evaluator
cross-checked against `gorient.fully_good_scan` at 5640 colourings. The (b′)
bar was respected (one noted by-product, undeveloped). §(K-grid)'s status cell
was recomputed again before this landing's content went in and its cap then
**deliberately bumped** 2035 → 2715, the row having absorbed **eighteen** new
theorems across the wave; reason recorded in `notes/check-gapmap-cells.py`.

### OSCHU — twenty-eighth direction (eighth fan-out)

**Status: LANDED 2026-08-19 — (a₁) is half PROVEN and half reduced to ONE
determinant; the (a₂) leg is a HIT that corrects a figure the arc has quoted
since (OC-28).** Fourth of the eighth fan-out's five to land. §(K-out)
**extended**, **Steps O25–O30**, labels **(OC-29)–(OC-34) CLAIMED EXACTLY**.
Driver **`notes/scripts/w4/oschu.py`** (five modes, all re-run by the
coordinator at landing in the foreground, one at a time, explicit timeouts, all
exit 0, every quoted figure reproduced; the census is deliberately split across
`--census1`/`--census2` because `--gtarget` alone runs 466–515 s and a combined
mode would breach the 600 s budget).

**The verdict.** **(OC-29)** shows the Schubert 4-space is not a new object at
all: `M̂ ∧ W = L_b ⊕ L_c`, §(K-out)'s **own** hub pencils, with Klein perp
`⟨C(M), C(bc)⟩` — from which `dimK ≥ 1` **always** (3 + 4 > 6), and §(K-tight)
*Step 2* item 5's `★r ∥ C(M)` falls out inside the dictionary. **(OC-30)**
identifies the bad set on `M` **exactly** — the transversals of `M` and `bc`
lying in `D` — in a five-row classification that recovers (OC-26)(ii) by a
route disjoint from ZNEQ's and is asserted equal to its ℚ[t]-GCD at every
frame. **(OC-31)** is the pass's sharpest positive: at **every** target-rank
chart point of the **whole graph `G`**, (CH-2)'s tower gives `pt(v) ∈ Π(b)` and
`pt(a) ∈ Π(c)`, so `C(vb) ∈ L_b` and `C(ac) ∈ L_c` come **for free** — two
lines of a projective plane always meet — forcing **`dimK ≤ 2`**. Hence **`hK`
at ONE chart point of `G` kills (OC-26)(ii)'s `dimK ≥ 3` disjunct at every
eligible split of that shape simultaneously**, and **(OC-32)** shows a third
such generator is structurally unavailable, so the bound is exact rather than
merely observed. **(OC-33)** reduces what is left to **one 3×3 determinant**:
the surviving disjunct forces `Q|_D` degenerate, so `rank(Q|_D) = 3` at one
target-rank `G`-point **implies input (a)** at that (shape, split) —
`x₁`-free, `λ`-free, stratum-free, and evaluated at a point the grid route
already constructs.

**Four coordinator adjudications on landing.**

*(1)* **Two more defective spec clauses, both accepted — taking the wave to
five.** First: the spec restated (a₁) as *"equivalently the Schubert non-jump
`dim(D ∩ M̂ ∧ W) ≤ 1`"*. Given (OC-29)'s `dimK ≥ 1`, that reads as `dimK = 1`
exactly, which is **strictly sufficient, not equivalent**; the honest form is
`dimK ≤ 2` **and** no ruling in `D`, and the pass constructs `dimK = 3` with
`rank(Q|_D) = 3` all-bad to show (OC-33) genuinely needs (OC-31). This clause
was **inherited from ZNEQ's landed hand-off** and transcribed by the
coordinator — the same provenance as GTMPL's and GFLOW's. Second: the spec
instructed the (a₂) leg to *"state plainly that the result stays CONDITIONAL on
(GR-10)"*. **That is wrong at the shapes the pass certifies directly** —
(OC-28)(iii) makes the `s₀` half free wherever a certificate is *exhibited*,
and exhibiting it is precisely what (OC-34) does at 155 classes. Only the
**class-uniform** statement still needs (GR-10). This one is the coordinator's
own, written at prep.

*(2)* **The (a₂) leg is a HIT, and it corrects an arc-wide figure.** §(K-grid)'s
907 *labelled* certified shapes are only **75 isomorphism classes**, and they
cover just **19** of §(K-out)'s **174** length-4-companion classes — **a factor
of nine** smaller than the raw count suggests. The remaining **155 are
certified directly, 155/155, 0 misses, 0 cap hits**, class predicate asserted
per shape. So the `s₀` half is free at **all 174**, and the re-keying the
coordinator commissioned as "cheap bookkeeping, no new mathematics" turned out
to matter: quoting 907 as coverage of §(K-out)'s population was a category
error between labelled shapes and isomorphism classes.

*(3)* **The residue's cheapest attack stops on a FIELD obstruction, not a
missing idea, and that is a design decision referred up.** What remains is
`rank(Q|_D) = 3` class-uniformly. If `D` is `⋆`-invariant it splits into `±`
eigen-blocks with `B = ±⟨·,·⟩`, so over a **real** field nondegeneracy is two
lines — and `D` **is** `⋆`-invariant at a σ-fixed grid configuration
((AC-2)/(AC-4)) — but those grids are **ℚ(i)-only** and no real σ-fixed
configuration exists. The route therefore needs `closure.Gauss` (the arc's only
non-`ℚ` scalar class, deliberately private to `closure`) moved down, which
`notes/scripts/README.md` §2 explicitly calls a deliberate design choice rather
than a mechanical move-down. Recorded as a **design item**, unpaid, and the
route is labelled a route, not a result — it carries **no driver**, the harness
being ℚ-only. **The harness half is UNBLOCKED as of 2026-08-20:** the design
item was adjudicated (move it down) and PAID by the harness move-down round —
`Gauss` now lives in `exactcore`, re-exported by `closure`, so this route may
use exact `ℚ(i)` directly. Everything else about it is unchanged: still a
route, still driverless.

*(4)* **The pass's criticism of the SIGZ landing is factually wrong, and the
wording that invited it is the coordinator's.** OSCHU reports that "the wave's
mandated §(K-out) status-cell recompute did not happen", reading the cell's end
state (666) against the spec's "≤ 560". The recompute **did** happen: at SIGZ's
landing the pre-existing content went **649 → 431 words, a 34 % reduction**,
well past the target, after which SIGZ's own 235-word block brought the cell to
666. The misreading is invited by the coordinator's own asymmetric wording —
the §(K-grid) obligation said "recompute … **before adding its own content**"
and the §(K-out) one omitted that clause — so the fix is to the spec, not to
the landing. OSCHU is nonetheless right that the cell was tight, and this
landing pays for itself: a further ~65 words came off the oldest
(OC-1)–(OC-25) material before its own content was added.

**Cap disclosure, verified at landing.** Every figure is a **witness, never a
rate**; POOL-G/POOL-S untouched; POOL-OS/OQ/OG/OR/OC2 pinned and disjoint from
every earlier pool. The E1 detector is real, not a formality — 155 certificate
hunts, each carrying a filter-passing both-block-certified colouring, probe cap
48 disclosed, 0 misses. The `--gtarget` and census legs take the **first**
guard-accepted target-rank point per class, which is a witness per class and
not a sample of the fibre.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: no
g-flank, on a real detector. E2: the target is **reduced**, not refuted or
unprovable-as-posed. E3: **stays ARMED by GBAL, neither fired nor disarmed.**

**Event classification, as the spec required and the pass got right.** A
non-jump failure is a **(K-tight) event at that split** — routes A and B dead
there, `hK` at the shape **untouched** — and **not** a PENCIL event; only
`{σ = 0} = ∅` is PENCIL. (OC-31) sharpens the (K-tight) side: wherever `hK`
holds at even one point, the `dimK ≥ 3` route to failure is **closed**, leaving
only `rank(Q|_D) ≤ 2`.

**What did NOT move.** **No gap-map status moves**; `hK`, (OC-8), (GR-15) and
class uniformity are exactly where they were. §(K-out)'s status cell was
recomputed a second time in one day and then, the section having absorbed
**eleven** new theorems ((OC-29)–(OC-39)) between SIGZ and OSCHU, its cap was
**deliberately bumped** 800 → 950 with the reason recorded in
`notes/check-gapmap-cells.py` — recompute first, twice, then bump, which is the
script's own sanctioned order.

### SIGZ — twenty-ninth direction (eighth fan-out)

**Status: LANDED 2026-08-19 — NO HIT on the disproof, and the second outcome
delivered as a THEOREM in its counting half.** Third of the eighth fan-out's
five to land, and **the arc's first authorized disproof direction**. §(K-out)
**extended**, **Steps O31–O36**, labels **(OC-35)–(OC-39) CLAIMED** with
**(OC-40) returned UNUSED** to the tail. Driver
**`notes/scripts/w4/sigz.py`**; `--validate` measured 693–747 s, so it ran as a
**recorded two-invocation foreground split** (`--reduce --spans --budget
--slack --theta --p21`, then `--hunt`) — both re-run by the coordinator at
landing, exit 0, every quoted figure reproduced.

**The pivot rule did NOT trigger.** There is no hit: no class shape with
`σ > 0` everywhere was found, and — the point of the spec's boundary clause —
none could have been *certified* by a sample anyway, which the pass states and
respects throughout. `--slack` is the search that would have fired it (a
single negative-`slack` support is a combinatorially forced stress, i.e. a
PENCIL event); it returns **0** over 215 906 enumerated supports.

**The verdict, and it is the spec's second outcome in its counting half.**
**(OC-35)** re-derives the pencil self-stress space of any min-degree-≥2
subgraph as a **Kirchhoff flow on its topological paths** valued in the
chain-span perps — §(K-pure) *P0*'s limit carrier read **off** the slide
limit, which is the whole delta and is what lets §(K-Λ) (Λ4) be spent on `σ`.
**(OC-36)** turns that into the closed form
`corank R(F) = Σδ_Q + ρ_F − slack(F)`. **(OC-37)** is the theorem: at a class
shape `slack(F) ≥ 0`, **with equality iff `F` is a cycle or a bouquet of
cycles**, so a stress needs `Σδ + ρ ≥ 2` at **every other topology, thetas
included** — hence **no `H`-supported self-stress anywhere in `hK`'s habitat
is combinatorially forced, and the counting route to a disproof is DEAD.** It
is the general form of the gap map's own `ℓ₁ + ℓ₂ ≥ 7` at `P21` and of
§(K-dom) (D3)'s `k ≥ 4`: the whole family of such exclusions is one
inequality, and it never fails. The theta corollary `Σ min(ℓᵢ, 6) ≥ 13` is
**tight** (measured minimum exactly 13), and the honest answer to the spec's
"which theta lengths remain uncovered" is **none, at the level of the count**.
**(OC-39)** then certifies `{σ = 0} ≠ ∅` with an exact-ℚ **full-row-rank
certificate at 3368/3368** class (shape, split) pairs over the **exhaustive
`K4` stratum** — per-pair proofs, not a census.

**Three coordinator adjudications on landing.**

*(1)* **The spec's second-outcome clause was too strong, and the pass was
right to decline it — the wave's THIRD defective spec clause, and this one is
the coordinator's own.** The spec said a proof that the mechanism cannot cross
into tight + `hnoRigid` "makes **(a₂) free at class shapes
unconditionally**". It does not: (OC-37) closes the **counting** half, while
the **geometric** half — no forced chain-span drop and no Kirchhoff drop — is
*measured* free (444/444 paths at `dim S = min(ℓ,6)`, 978/978 `c ≤ 2` supports
at corank 0) and stays **open class-uniformly**, one-point decidable per
shape, in (OC-8)'s own object class. So **(OC-28)(iii)'s reduction to (GR-10)
remains the best uniform statement on the `s₀` half, unchanged**, and the
draft says so. Unlike GTMPL's and GFLOW's, this clause was not inherited from
a landed hand-off — it was written by the coordinator at prep, which makes it
the cleanest instance of the wave's recurring shape.

*(2)* **The harness finding is accepted, and the reading correction is made at
every site — the adjudication SIGZ referred up.** **(OC-38)**(iii) reports a
**set equality**: §(K-flank) *F5(d)*'s five σ-jump seeds at `P21` are
**exactly** the five at which `localtest.plane_basis` degenerates at hub `c`,
each with the single coincident pair `(c, 113, 115)` that drops the length-6
topological path's span from 6 to 5. So the arc's **only** exhibited instance
of the `{σ = 0}`-failure mechanism sits on the degeneracy locus that
`notes/scripts/README.md` §4 convention 1, *Harness debt* item 4 and §(K-out)
**(OC-7)** all name; under the composite gate `repin.star_generic`, `σ = 0` at
**all 360** gate-accepted seeds (cap 500, disclosed). **What survives:** the
mathematics of *F5(d)* is untouched — the five seeds are **legal** chart points
(`flanks.nondeg_conjuncts` green at all five, a coincident hinge pair not being
excluded by `IsNondegPencilRealization` — (OC-7)'s own finding), `dim U = 1`,
and §(K-tight) *Step 2.3*'s prediction holds at them exactly as recorded; and
**(OC-28)(iv)'s *proper-open* claim stands**. **What falls:** its
*quantitative* reading, *"the complement of `{σ = 0}` is not thin in the
sampler's rational range (5/35)"* — at `P21` that complement **is** the
coincidence locus, a proper closed subset, and the ≈ 14 % rate is a property
of `plane_basis`, not of the variety. **Coordinator ruling on quotation, since
SIGZ asked for one:** every future quotation of "5 of 35" carries the
`plane_basis`-degeneracy qualifier in the same sentence. The correction is
propagated to **all six sites** in this landing (dispatch-log **F12**'s
discipline — a map correction is presumptively a body-prose correction too):
§(K-flank) *F5(d)*'s own bullet and its *Step F7* item 6 (which asked exactly
this question and is now **closed as posed**), the §(K-out) *Step O24* text,
**(OC-28)(iv)** itself, and the gap map's `P21` row and `(K-tight)`-adjacent
mention.

*(3)* **`P21` is quantitatively one unit short, which is why it never
threatened the habitat.** (OC-38)(i)/(ii): the recorded theta support has
`slack = 0` at **two** nodes — which (OC-37)(ii) forbids in the class — and
its `σ = 1` decomposes as `(slack, Σδ, ρ) = (0, 1, 0)`. Inside the class the
same support needs `Σδ + ρ ≥ 2`; the mechanism supplies **1**, and the missing
unit is exactly what `hnoRigid` buys. The single failing inequality is
`(Λ4)(iii)` at the pair `{23a, 23b}` (`3 + 3 = 6 < 7`), i.e. a rigid `C₆` —
`hnoRigid` failing, precisely.

**Cap disclosure, verified at landing.** `--slack` **enumerates and does not
sample** — no rng, no placement, no cap on the supports (2614 shapes, 215 906
(support, split) instances), which is what makes the `slack < 0` zero a real
negative rather than an unexhausted search. `--hunt` resolves **0 pairs under
cap**. The `repin.star_generic` leg is a **witness count at cap 500**, never a
rate. The geometric-half figures (444/444, 978/978) are **measurements**, and
the draft never upgrades them to the class-uniform statement.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: nothing
on the `D = 0` line. E2: a MISS on a *disproof* direction is the expected
outcome, not refuted-with-no-successor — (a₁) (OSCHU) and (a₂)-via-(GR-10) stay
dispatchable. E3: **stays ARMED by GBAL, neither fired nor disarmed.**

**What did NOT move.** `hK`, (OC-8), (GR-15), `{σ = 0}`'s row and class
uniformity are exactly where they were; **no gap-map status move**, and none
was available to a pass with no hit. §(K-out)'s status cell was **RECOMPUTED**
(649 → 666 words while absorbing five new labels, i.e. the pre-existing content
compressed ~23 %; zero labels dropped by scripted set-diff) rather than bumped,
discharging the obligation the wave's spec placed on its first §(K-out)
landing and leaving 134 words for OSCHU. Two (a₁)-adjacent by-products
**reported and not developed** (OSCHU's target): the flow form survives
welding, giving (OC-18)'s `H/X` criterion a `G°`-level form, and `D` is dual to
the flow (`dim D = 3 + σ`), so an (a₁) recipe must control a `ρ`-style
deficiency at `H°`'s nodes.

### Not selected — the eighth fan-out's losers

Disclosed per the twelfth direction's precedent: **this ranking is the
coordinator's, with no independent top-rung reader** (third consecutive wave).
A future recon may overturn any of it.

- **(OC-19) input (c), class-uniformly** — OCON's **#1 by value** and, for the
  second consecutive wave, deliberately **not** dispatched, on OCON's own
  grounds: it is **(GR-15)-flavoured, not (FR-R1)-flavoured**, so it re-enters
  the arc's oldest missing technology rather than adding an independent idea.
  YLOC's chunk-level instrument attempt was **DEMOTED BY WITNESS**
  ((GR-62)), so the technology is still not arriving. **GCOLL is this wave's
  bet on that supply line** — (GR-64)(R2) is the smaller sub-target on the
  same path.
- **§(K-out) hand-off item 3** — `T_u^{⊥_B} ∩ β_b = 0` at the **1715**
  slide-legal `b` ends, where **(OC-21)** makes it an **iff**; measured
  `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends and 4/4 POOL-OC ones. A
  good, cheap, well-posed target, **queued for the second consecutive wave**
  and dropped for the same reason — §(K-out) already carries two directions
  (OSCHU, SIGZ) and item 3 rides the same measurement infrastructure. **Queue
  it again**, and note that a third §(K-out) direction is the cheapest thing
  on the board once one of this wave's two lands.
- **§(K-out) hand-off item 4** — folded into **OSCHU** as its lowest-priority
  third leg, per the seventh fan-out's own instruction to *"fold it into
  whichever §(K-out) direction runs next."*
- **AGLU hand-off item 2**, the `(slack, defect(T)) = (0,2)/(1,1)` tightness —
  folded into **GTMPL** as an optional secondary. If it is a theorem the
  (GR-38) kill has an exact form (`= 2`, not `≥ 2`) on the candidate family.
- **(d′)** — the corner-armed realized-binding fully-hot seed hunt past GDEV's
  caps. **E1's own clarification says it is not a flank by itself**, so its
  best outcome is a measurement. Lowest value for the third consecutive wave;
  at some point it should either be dispatched cheaply or struck.
- **(GR-64)(R1)** — folded into **GCOLL** as its cruder fallback deliverable.
- **Route σ's parked Lean half** and **the W4 build** — both **BLOCKED by the
  standing 2026-08-05 Lean hold** (general, not W4-scoped). Not eligible
  without a fresh user adjudication, and none was sought at this check-in:
  the check-in's one standing-constraint move was the `σ > 0` hunt, nothing
  else.
- **`Pencil-strategy.md` §4.6's U3** — still unrun; the shortlist is
  **partially superseded** for the tight stratum and §5.3's own local-frame
  feasibility boundary rules out the symbolic meta-option. Two **durable
  negatives** — do not re-run.

---

## Two probes SPECCED and AUTHORIZED 2026-08-20 — **BOTH LANDED** (KBARE-FALSIFY 2026-08-20; C3-AVOID 2026-08-24)

Both are **read-only recons**, both **docs+scripts-only**, and neither touches
the Lean hold. They exist because the eighth fan-out closed with the phase
UNROUTED and a user question exposed that the *architecture* had never been
tested — only extended. **User adjudication, 2026-08-20:** asked what to do
next, the user chose to clear the structural items first (done: slices 1–2),
then, on being told `hbareSplit` was carried rather than settled, said *"I think
we should plan to investigate hbareSplit as well; if it turns out that it's
false then that weakens the case for working on hK as well"* — and, on the
option space, *"Let's keep all these options that we discussed around and clear
for a future session"* (the option board is `notes/Pencil-strategy.md` §8).

**Dispatch order is not free: run KBARE-FALSIFY first.** Its answer can moot
C3-AVOID and a great deal else — that is the whole point of running it.
**Both have now landed** — KBARE-FALSIFY 2026-08-20 (a T1 hit; it did **not**
moot the second), C3-AVOID 2026-08-24 (the gate decided at threshold
`|S| ≤ 2`). Per-probe records in the two subsections below.

**LANDED 2026-08-20 (KBARE-FALSIFY, opus, one commit).** Outcome: a **HIT at
tier T1** — **(K-bare-ext) is REFUTED as stated**, `hbareSplit` **untouched**
and still carried as pinned. Verdict, mathematics and every figure:
`notes/Pencil-informal.md` §(K-bare-ext) *Steps BE1–BE8*; driver
`notes/scripts/kbare/breakhunt.py`. It does **not** moot C3-AVOID: the hit is a
statement about route A's *seed* quantifier, not about the reduction, so
C3-AVOID's purely combinatorial question stands exactly as specced. Four
things this spec asked for that the landing answers, recorded so the next
dispatch does not re-ask them: (a) larger stressed-stratum skeletons — now a
**census** (216 index-1 members on `≤ 6`-hub skeletons, DZ one of them) with
the stratum proved **complete** at `corank(G′) ≤ 3`; (b) the `index ≥ 2`
existence search — subsumed, and the index bound makes `index ≥ 3` **empty**;
(c) DZ's `0/15` off-line — **broken by construction**, and the reason the
sampling figure was never evidence is recorded (the locus is a curve); (d) the
one-gadget caveat on C1 — **second gadget run**, C1 corroborated per stratum
and refuted as a principle. One correction to this spec's own framing: a **T2**
witness would falsify `PencilPair`'s unconditional second conjunct — i.e.
`PencilPair K 3 G` itself, the phase's *target motive* — so it would be a
**PENCIL event** rather than "not a PENCIL event" as written above. It would
**not** break the headline theorem, which *derives* `PencilPair` from the three
carried hypotheses and so would merely become true-and-unusable with
`hbareSplit` refuted; the PENCIL-event reading comes from the target failing,
not from the theorem failing — nothing turned on it (no T2 candidate
exists in the arc's gadget stock), but a future dispatch should price it that
way.

### Probe KBARE-FALSIFY — is `hbareSplit` actually true?

**The question.** `hbareSplit` has been carried pinned since 2026-07-30 on
evidence the recon itself scopes as *"one gadget, one sampler family"*. **Try to
break it.** The target is **(K-bare-ext)**, the arbitrary-seed insertion lemma
(§"(K-bare) extension-route recon" in `notes/Phase39-design.md`): for **every**
bare pencil realization of `G′` attaining `target(G′)`, is there a placement
`pt(v)` — off `line(pt a, pt b)`, inside the hub end's star plane when an end is
a hub — whose induced realization of `G` attains `target(G)`?

**Why this direction and this order.** Two independent reasons converge, and the
coordinator should state both in the spec so the dispatch does not treat this as
routine evidence-gathering: **(i)** `hbareSplit` is the **less-tested** of the
two carried kernels — `hK` has 37 directions and 907/907 censuses behind it;
`hbareSplit` has the gate's seven gadgets (all count-**independent**, a scope the
recon flags itself) plus **DZ** as its single stressed-stratum witness. **(ii)**
It is the one whose failure is **fatal to the route regardless of `hK`** — the
induction's infeasible branch cannot be discharged without it. Weakest link,
load-bearing.

**What a hit means, stated before the run so it is not over-read.** A
counterexample to (K-bare-ext) **does not refute the pencil conjecture.** It
refutes *this induction*, so the consequence is re-architecture (§8.3's C3, or a
different move set), not a dead target. It is therefore **not** a PENCIL event
in the direction-A pivot rule's sense and does **not** stop the loop — but it
**is** a phase-shape event and goes to the user with estimates.

**Where to look, from the recon's own structure.** The evidence is thin exactly
where the mathematics is hardest, so aim there. **(a)** New **stressed-stratum**
gadgets beyond DZ — the recon's skeleton arithmetic gives the construction
recipe (subdivide a cubic multigraph skeleton; `f`-constraints become per-sub-
skeleton length bounds: every 2EC skeleton edge `≤ 4`, skeleton cycles through
two apex edges `≥ 7` total, sub-thetas `≥ 13`), and it notes the `K3,3` skeleton
is arithmetically **excluded at index 2**, so **larger skeletons are unprobed**.
**(b)** The **`index ≥ 2`** danger-gadget existence search that option C left
open. **(c)** Off-line failure-locus mapping past DZ: is the failure set
**exactly** the line at corank ≥ 2, or does an off-line failure exist? DZ gave
**0/15**; that is the number to try to break. **(d)** The **one-gadget** caveat
on option C's C1 finding (target-rank policing the local chain degeneracy) —
a second gadget either corroborates or kills it.

**Bars.** Do **not** attempt option B (the insertion calculus) — un-commissioned
and research-scale; this probe is a falsification hunt, not a proof attempt. Do
**not** re-run the landed gate (seven gadgets, PASSED) or re-derive DZ's
certification. Do **not** touch the Lean hold. Report **caps honestly**: an
exhausted search is *"not found under cap C"*, never "`hbareSplit` is true" —
the whole point is that the existing evidence was over-read once already.

**Deliverable.** A draft workbook section (untracked
`notes/Pencil-draft-<CODE>.md`), extending the design doc's (K-bare) section or
a new workbook section as the coordinator reserves; a new driver at a reserved
`notes/scripts/kbare/` path; an explicit confidence verdict; and the TERMINATION
reading. **Rung: opus** (it settles a carried kernel's fate). Labels and section
name to be reserved at prep per `notes/Pencil-labels.md` — **note that
`notes/scripts/kbare/` is a different layer from `w4/`**, so §2's layering rule
applies afresh.

### Probe C3-AVOID — is the mixed-stratum target reachable? (**LANDED 2026-08-24, opus, one commit**)

**The question, and it is purely combinatorial.** `notes/Pencil-strategy.md`
§4's **C3** weakens the target: pin only a subset `S` of bodies to pencils,
generic elsewhere. If at each reduction step the split vertex can be chosen
**outside `S`**, KT's full freedom is intact there and the geometric crux never
arises. So: **can the combinatorial reduction always avoid a prescribed subset
`S`?** The risk C3 names itself is that *the reduction consumes vertices, so it
may be forced into `S`* — a *"reduce avoiding `S`"* theorem is the thing to
check, and it is a question about the **already-formalized** generation theorem
(Thm 4.9, Phase 20), not about pencils.

**Why it is worth a probe even though C3 is weaker than the target.** `S = V`
recovers the full conjecture, so C3 is a **filtration, not a retreat** — a proof
for general `S` *is* the theorem, and a proof for small `S` is a real result on
the way. It is also the **chemically realistic** statement, since real molecules
have some sp²-planar atoms rather than all. And it is the only option on the
board that **relocates** the hard case instead of attacking it, which is why it
survives the two filters that kill the invariant-strengthening candidates: it
proposes no new invariant and no new ground set.

**What a verdict looks like.** **GO** — a "reduce avoiding `S`" statement, with
the constraint on `|S|` or on `S`'s structure that makes it true, plus the
smallest `S` for which it fails. **NO-GO** — a configuration where every legal
reduction is forced into `S`, which prices C3 out and is equally valuable.
Either way, state the `|S|` threshold: C3's value is graded by how large an `S`
survives, and *"only `|S| = 1`"* is a very different result from *"any
independent `S`"*.

**Bars.** Purely combinatorial — do **not** compute a rank, place a
realization, or touch `hK`/`hbareSplit`. Do **not** re-derive the generation
theorem; consume it. Do **not** widen scope into proving C3 itself: this probe
prices its **gate**, nothing more.

**Deliverable.** A draft design-pass section for `notes/Pencil-strategy.md` §4's
C3 entry (or a new workbook section if the mathematics warrants one), a driver
only if a search is needed, and an explicit verdict with the `|S|` threshold.
**Rung: opus** (it can re-route the phase). Labels reserved at prep.

**The verdict, as landed: the gate is DECIDED, and the threshold is EXACTLY
`|S| ≤ 2`.** Mathematics, proofs, figures and caps: **`notes/Pencil-strategy.md`
§4.7** (the canonical home — labels **(AV-1)–(AV-8)**, ***Steps AV1–AV6***);
driver `notes/scripts/w4/avoidgen.py` (seven modes, `--all` ~36 s,
byte-identical at `PYTHONHASHSEED` 0 and 12345). **§(K-avoid) was NOT opened**
and returns to the pool unopened: the mathematics is about the *generation
theorem*, not kernel (K), so it has no gap-map row and moves no gap-map status.
Headline chain:

* **(AV-1)** the LOCAL gate never fails — at every Case-II node
  `#{deg = 2} ≥ ⌈((D−3)|V|+4)/(D−1)⌉`, i.e. **more than half** the vertices at
  `D = 6` (0 violations over the 140-node `μ ≤ 3` census, tight at 6).
* **(AV-2)/(AV-4)** a **conservation law** decides it instead: every reduction
  tree has `#leaves = μ(G) = |E|−|V|+1` (so `#contractions = μ−1`,
  `#splits = |V|−μ−1`), each leaf holds 2 vertices, hence
  **`capacity(G) ≤ 2 μ(G)`** — verified with 0 violations over the pool **and**
  exhaustively over all **476** simple 2EC minimal `0`-dof graphs at `|V| ≤ 6`
  (451 attain equality).
* **(AV-3)** **GO at `|S| ≤ 2`, unconditionally; NO-GO from `|S| = 3`** —
  the counterexamples being `C_3 … C_6`, where **every** 3-subset fails.
* **(AV-5)** **no structural hypothesis on `S` lifts the threshold** (the
  independent triples `{0,2,4}`, `{1,3,5}` of `C_6` are as unavoidable as
  `{0,1,2}`) — so the spec's *"any independent `S`"* end of the calibration is
  **refuted**, and the answer sits at the *"only `|S| = 1`"* end.
* **(AV-6)** the contraction-free reductions are **exactly** the cycles
  (`μ` is split-invariant, the base has `μ = 1`), which is why the `|S| = 3`
  counterexamples are exactly `C_3 … C_6` and every other graph already has
  ceiling `≥ 4`.
* **(AV-7)** — the honest scope line — **the gate is necessary, not
  sufficient.** `splitOff`'s definition body rewires the incidences of *both
  neighbours* `a`, `b`, so an `S`-body next to a split vertex has its pencil
  condition re-imposed anyway; and every capacity unit above 2 is bought by a
  **Case-I gluing** whose pencil-compatibility is geometry this probe is barred
  from. That arm is the live successor.
* **(AV-8)** board verdict: **C3 is NO-GO as a crux-avoidance route** and stays
  on the board only **re-scoped**, with `μ` grading what it buys.

**One guess of the pass's own, refuted by its own driver and recorded rather
than smoothed over.** (AV-1)'s Case-II count suggests `5|E| ≤ 6(|V|−1) + 4` in
general, which would cap `μ ≤ (|V|+3)/5` and give a quotable *"at most ~40 % of
the bodies"*. Exhaustively at `|V| ≤ 6` the count reaches `10` and the capacity
ratio reaches **80 %**, so the guess is **FALSE** without the
no-proper-rigid-subgraph hypothesis and the `|V|`-relative headline is
withdrawn; only the exact `2μ` ceiling stands.

**Caps.** Case-II census exhaustive **for `μ ≤ 3` only** (`|V| ≤ 16`); the
`--betti`/`--count` sweeps exhaustive over **simple 2EC graphs on `|V| ≤ 6`**;
the per-`S` avoidance sweep runs to `|V| ≤ 12`. `μ ≥ 4` was not searched — an
exhausted cap is not a nonexistence claim. Everything at `D = 6`; (AV-1) and
(AV-3) are the only claims stated for general `D`.

**Bars honoured.** No rank computed, no realization placed, `hK`/`hbareSplit`
untouched, **no `.lean` edited**, the generation theorem consumed and not
re-derived, and scope kept to the gate — C3 itself is not attempted. **TERMINATION: E1, E2, E3 all NO**; E3 stays ARMED by GBAL,
neither fired nor disarmed (this probe touches neither entry 1 nor (a′)).

---

## GFLIP — thirtieth ordinal, the thirty-eighth direction (single dispatch, prepped 2026-08-25)

**Selection provenance:** the standing 2026-08-07 delegation; shape adjudicated
at the 2026-08-25 check-in — **"Single direction, cheapest first"** (an option
selection; `notes/Pencil-adjudications.md`, the 2026-08-25 bullet). Cheapest
first is §8.1's own ranking: **(GR-R1)**, the cheapest item on the option
board. Dispatched **un-named, single, top rung** (`recon-fable` — fable is
dispatchable this session per the same check-in; the fan-out mechanics' rung
rule applies unchanged to a single direction). Derivation-first tier. **The
shared mechanics and landing checklist above apply in full** — read-only
w.r.t. every shared file, commit nothing, draft to the untracked
`notes/Pencil-draft-GFLIP.md`, tight return verdict.

**The target — (GR-R1), the flip-availability clause; proving it upgrades the
arc's first `n`-free (b′)-shaped bound from *modulo a named clause* to a
theorem.** Verbatim as GFLOW landed it (§(K-grid) *Step G108*(ii)):

> **(GR-R1)** at every unbalanced admissible configuration, some
> majority-side odd branch has a (GR-50)-feasible flip.

Measured with **0 failures** at all 701 382 unbalanced stratum configurations
(exhaustive on the stratum), at V8, and at 47 628 + 21 204 configurations of
seeded `n = 8/10` habitat shapes — and **not proven**. Given (GR-R1),
(GR-89)(ii)'s `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12` is a theorem
(`n`-free), and with (GR-C1) on its `n_hub ≤ 6` stratum the constant-4 form
follows ((GR-86) + one descent step). (b′) at the constant 2 is **NOT** this
direction's target — its residual is (GR-C2), a separate board entry.

**The named route (G108's own, stated as the residual's item 2):** (GR-R1) is
a **(GR-51)-shaped statement** — flipping a majority-side odd branch `γ` from
A to B can only create **B**-monochromatic-pair hubs — so **(GR-52)**'s parity
contradiction and **(GR-53)**'s exhaustion over maximal constraint structures
(§(K-grid) *Step G71*) are the natural instruments. The route sketch to attack
or refute: an unbalanced configuration has a majority side with `≥ |δ|/2 + k`
odd branches; show the (GR-51) local weight inequality cannot block **all** of
them at once, by the (GR-52) counting mechanism. Treat the sketch as a
candidate, not a pin — if it dies, say where.

**What counts as a HIT** — a proof of (GR-R1). Also valued, on the
(GR-29)/(GR-30) precedent: a **refutation by witness** (which demotes
(GR-89)(i)/(ii) back to a measured bound and reshapes the residual — state
exactly what survives, in particular whether the greedy-descent evidence
localizes the failure), or a **proof under a restricted quantifier with the
exact boundary named** (e.g. parity-optimal configurations only — which is all
(GR-89)(ii)'s descent actually consumes at its first step — or a stratum
bound). State which of the three you got.

**Bars.** Do **not** attack (GR-C2) — a separate board item; report any
by-product as a finding and do not develop it (the YLOC/BALB mutual
precedent). Entry 5 is **PROVEN** ((GR-54)) — do not re-attack. Do **not**
re-derive (GR-49)–(GR-54), (GR-67)–(GR-70), or (GR-85)–(GR-90) — landed, and
they are your inputs. Do **not** re-run the exhaustive censuses ((GR-70)(ii),
G108's 701 382-configuration sweep) — cite them; a *new* driver mode that
tests a *new* sentence is fine, a re-measurement of a landed figure is not.
(GR-15) and class uniformity are out of scope. No `.lean` is touched (the
standing Lean hold).

**Riders, verbatim from the eighth fan-out's.** TERMINATION check E1/E2/E3 at
the return (E3 is ARMED by GBAL — firing is the coordinator's action; report,
never fire). Cap disclosure: an exhausted cap is *"not found under cap C"*,
never nonexistence. F11: every headline claim needs a driver that tests that
sentence, and "exhaustive"/"forced"/"the only" are their own claim class. The
shift-metric layer is UNBOUNDED ((GR-43)) — any bound is on a **difference**.
All figures exact ℚ, seeded, degeneracy-guarded, imported from the canonical
layer (`notes/scripts/README.md` binds; the *Divergences* table names the
same-name-different-semantics traps).

**Driver — conditional, at the pinned path `notes/scripts/w4/gflip.py`.** A
purely derivational proof consuming only landed figures needs no new driver —
then state that disposition explicitly in the draft. Any new measured or
exhaustion claim (a (GR-53)-style case analysis included) mints the driver at
the pinned path, importing the harness read-only, left untracked for the
coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GFLIP"): §(K-grid) **extends** — no new section; labels **(GR-97)–(GR-101)**,
**Steps G116–G120**; owning section stays authoritative; return any
unconsumed remainder to the tail.

### GFLIP — landing write-up (LANDED 2026-08-25, recon-fable, one serial coordinator commit)

**Verdict: a HIT of the first kind — (GR-R1) is PROVEN, with no restricted
quantifier**, and strengthened: at every unbalanced admissible configuration at
least `|δ| ≥ 2` majority-side odd branches have (GR-50)-feasible flips, as the
corollary of a **selection theorem** ((GR-99): at any feasible pattern of any
cubic loop-free hub multigraph, at most `b` A-branches are blocked and at most
`a` B-branches — no habitat gate, no `2k` cap, no connectivity). Chain: the
**demand form** (GR-97) (feasibility ⟺ `inc_H(S) ≥ max(N_A(S), N_B(S))`,
certified against the (GR-50) oracle at 57 232 pairs at BOTH quantifier levels,
0 disagreements), the **counting lemma** (GR-98) (`b ≥ n₁(S) − s(S)` off
cubicity alone, 3 458 768 triples), and the submodular-union argument closing
(GR-99) (0 violations at 57 586 feasible patterns over six legs; tight at 18
stratum instances per side). **Consequences:** (GR-89)(ii)'s `n`-free `≤ 12`
bound loses its one named gap and is a THEOREM; (GR-90)'s constant-4 row drops
to *modulo (GR-C1) alone* (a full theorem on `n_hub ≤ 6`); the greedy descent's
0-stall record becomes a theorem. **Bars honoured:** (GR-C2) not attacked (one
sharpened hypothesis reported, no figure); rank-free throughout; entry 5 /
(GR-64) rows / (GR-15) untouched; no `.lean` touched. **E1/E2 NO; E3 stays
ARMED by GBAL, not fired** (the HIT is on (b′)'s availability layer, not
entry 1). Canonical home: §(K-grid) *Steps G116–G119*
(`notes/Pencil-informal-grid.md`); driver `w4/gflip.py` (five modes, ~44 s);
labels (GR-97)–(GR-99) claimed, (GR-100)/(GR-101)/Step G120 returned.

**One spec clause found defective, corrected at *Step G118* (the fourth
consecutive wave-or-single with at least one — F22's pattern holds).** The
spec's route note quoted *Step G109* residual item 2's gloss — *"flipping `γ`
A → B can only create B-monochromatic-pair hubs"* — which is **incomplete**:
the flip can also create a **B-monochromatic triple** at a `q_v = 3` end, and
that singleton case is the stratum's *dominant* blocking mechanism (15 804 of
32 608 minimal violators). Corrected in place at *Step G109* with a marker.
The named instruments ((GR-52)/(GR-53)) also turned out not to be the proof's
— the spec's "treat the sketch as a candidate, not a pin" clause did its job:
the direction recorded where the sketch dies (a sufficient-condition calculus
cannot see merely-feasible hypotheses) and found the demand-form route instead.

**Coordinator verification at landing:** `--validate` re-run in full plus
`--form` separately (all headline figures reproduced: 57 232 / 3 458 768 /
45 592 / 32 608 / the anatomy histogram / minimum 2 / tight 18 per side); the
(GR-98)/(GR-99) derivations re-walked line-by-line (the cubic count, coverage
submodularity, lone-A-end injectivity); label set-diff scripted, L6 grep
clean; `check-gapmap-cells.py` green on the recomputed §(K-grid) row.

---

## GCHEAP — thirty-first ordinal, the thirty-ninth direction (single dispatch, prepped 2026-08-25)

**Selection provenance:** the standing 2026-08-07 delegation; shape adjudicated
at the **second** 2026-08-25 check-in — **"Single direction, cheapest first"**
(an option selection; `notes/Pencil-adjudications.md`, the second 2026-08-25
bullet). Cheapest first is §8.1's own ranking with (GR-R1) struck by GFLIP:
**(GR-C2)**, now the cheapest item on the option board. Dispatched **un-named,
single, top rung** (`recon-fable` — fable is dispatchable this session per the
same check-in). Derivation-first tier. **The shared mechanics and landing
checklist above apply in full** — read-only w.r.t. every shared file, commit
nothing, draft to the untracked `notes/Pencil-draft-GCHEAP.md`, tight return
verdict.

**The target — (GR-C2), the selection clause; it is the whole gap between the
proven constant 4 and (b′)'s target constant 2.** Verbatim as GFLOW landed it
(§(K-grid) *Step G108*(iv), restated at *Step G109* residual item 1):

> **(GR-C2)** at some parity-optimal configuration with `|δ| ≤ 2`, some
> majority-side odd branch is **cheap** — its flip is feasible and it is not
> a doubly-blocked matching branch.

Measured with **0 failures** at all **96 930** unbalanced parity-optimal
`|δ| = 2` configurations of the stratum (exhaustive), 0 at 2114 seeded
`n = 8` and 0 at 371 seeded `n = 10` — and **not proven**. What a proof buys,
per (GR-90)'s constant table: with (GR-C1), **(b′) at the constant 2**
((GR-C1) is GPSA's landed first clause, a theorem at `n_hub ≤ 6` by (GR-69),
open beyond — so a full constant-2 theorem on that stratum); and the
**every-step variant** (the analogue of how (GR-R1) entered the descent)
makes the `n`-free `d_adm − d_par ≤ 2·min(k, ⌊n_hub/4⌋) ≤ 6` a theorem
**outright**, (GR-R1) being proven. State explicitly WHICH form any proof
delivers (as-posed / at every descent step).

**The named inputs (landed; consume, do not re-derive).** (i) **(GR-89)(iii)'s
counting bound** proves (GR-C2) below `n_hub = 3k + 5|δ|/2` — the whole
`n_hub ≤ 6` stratum — and pins the first possible failure to `n_hub = 8`,
`2k = 2`, **both** odd branches doubly-blocked matching branches (*Step
G108*(v)'s cell, swept empty under a 46-shape / 132-configuration cap).
(ii) **GFLIP's sharpened hypothesis** (*Step G119*, offered to this successor
with no figure): (GR-99)(ii) gives `≥ |δ| ≥ 2` *feasible* majority branches
at every unbalanced configuration, so a (GR-C2) failure needs **every one**
of them to be a doubly-blocked matching branch — the "every **feasible**
majority branch" variant of (GR-89)(iii) is **OPEN** and is the natural first
attack. (iii) The **demand form** (GR-97) and **counting lemma** (GR-98) are
the landed instruments (GR-R1)'s proof actually used; (GR-52)/(GR-53) are a
sufficient-condition calculus that **cannot see merely-feasible hypotheses**
(*Step G118*'s post-mortem — do not repeat that detour). Treat the sketch as
a candidate, not a pin — if it dies, say where.

**What counts as a HIT** — a proof of (GR-C2), either form (name it). Also
valued, on the (GR-29)/(GR-30) precedent: a **refutation by witness** — a
parity-optimal `|δ| ≤ 2` configuration at which every feasible majority-side
odd branch is a doubly-blocked matching branch (this demotes the constant-2
route back to a measured bound and leaves the proven 4 standing — state
exactly what survives, in particular whether (GR-89)(iii)'s counting
localizes the failure); or a **proof under a restricted quantifier with the
exact boundary named** (e.g. a stratum bound past `n_hub = 8`, or a
matching-branch-count-bounded case). State which of the three you got.

**Bars.** Do **not** attack (GR-C1) — a separate residual (GPSA's first
clause). (GR-R1) is **PROVEN** ((GR-99)) — consume, do not re-attack. Do not
re-derive (GR-49)–(GR-54), (GR-67)–(GR-72), (GR-85)–(GR-90), or
(GR-97)–(GR-99) — landed, and they are your inputs. Do **not** re-run the
exhaustive censuses ((GR-89)(iv)'s 96 930-configuration census, G108's
701 382-configuration sweep, (GR-70)(ii)) — cite them; a *new* driver mode
that tests a *new* sentence is fine, a re-measurement of a landed figure is
not. (GR-15) and class uniformity are out of scope. No `.lean` is touched
(the standing Lean hold).

**Riders, verbatim from GFLIP's.** TERMINATION check E1/E2/E3 at the return
(E3 is ARMED by GBAL — firing is the coordinator's action; report, never
fire). Cap disclosure: an exhausted cap is *"not found under cap C"*, never
nonexistence. F11: every headline claim needs a driver that tests that
sentence, and "exhaustive"/"forced"/"the only" are their own claim class. The
shift-metric layer is UNBOUNDED ((GR-43)) — any bound is on a **difference**.
All figures exact ℚ, seeded, degeneracy-guarded, imported from the canonical
layer (`notes/scripts/README.md` binds; the *Divergences* table names the
same-name-different-semantics traps) — **the balance layer is now
`w4/gridbal_common`** (moved down 2026-08-25, §1-catalogued): import the
eleven moved devices from there directly, not via the sibling re-exports.

**Driver — conditional, at the pinned path `notes/scripts/w4/gcheap.py`.** A
purely derivational proof consuming only landed figures needs no new driver —
then state that disposition explicitly in the draft. Any new measured or
exhaustion claim mints the driver at the pinned path, importing the harness
read-only, left untracked for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GCHEAP"): §(K-grid) **extends** — no new section; labels
**(GR-100)–(GR-104)**, **Steps G120–G124**; owning section stays
authoritative; return any unconsumed remainder to the tail.

### GCHEAP — landing write-up (LANDED 2026-08-25, recon-fable, one serial coordinator commit)

**Verdict: a graded outcome of the third kind AND the second kind
simultaneously — (GR-C2) proven under a restricted quantifier with the exact
boundary named in both directions, plus the spec's named refutation witness
at that boundary.** The lone-dart identity + blocked-end capacity (GR-100)
and the selection corollary (GR-101) — consuming (GR-99)(ii) as the
feasibility supply — prove the **every-step form for `n_hub < 6|δ|`** (all
of `n ≤ 10` at `|δ| = 2`; the landed 96 930/2 114/371 censuses become
theorems; *Step G108*(v)'s hunt cell provably empty; **(b′) at the constant
2 a THEOREM on the whole `n_hub ≤ 6` stratum**, modulo (GR-C1) alone at
`n = 8, 10`); an explicit `cubic_habitat`-gated, full-cube-verified
parity-optimal witness at `n_hub = 12 = 6|δ|` **refutes the
per-configuration form**, the boundary exact both ways. The as-posed
existential **survives at every audited pair** (per-matching gap 0, the
stalled flips price `[0, 0]`), so the residual is reshaped to
**(GR-104)(i), the price form** (theorem at `n ≤ 10`, measured intact at
`n = 12`, OPEN beyond), plus the stall tax (GR-102) and the descent
interpolation (GR-104)(ii) (row 5's `2·min(k, ⌊n/4⌋) ≤ 6` outright at
`n ≤ 10`). **Bars honoured:** (GR-C1) consumed, not attacked; rank-free
throughout; no landed census re-run (the driver's quantifiers are strictly
larger, and gflow's denominators are reproduced from an independent
construction); (GR-15) / class uniformity untouched; no `.lean` touched.
**E1/E2 NO; E3 stays ARMED by GBAL, not fired** (the HITs are on (b′)'s
selection layer, not entry 1). Canonical home §(K-grid) *Steps G120–G124*
(`notes/Pencil-informal-grid.md`); driver `w4/gcheap.py` (four modes,
~40 s); labels (GR-100)–(GR-104) and Steps G120–G124 all claimed, none
returned.

**One landed inference found incomplete, corrected in place (the FIFTH
consecutive wave-or-single with at least one — F22's pattern holds), and
this time the SPEC inherited it verbatim:** the spec's input clause
*"(GR-89)(iii) proves (GR-C2) below `3k + 5|δ|/2` … first possible failure
`n_hub = 8`"* conflated the all-majority-DBM hypothesis with the
feasible-majority-DBM one a (GR-C2) failure actually gives (they coincide
only at `b = 0`); corrected at *Step G108*(v)'s marker, every conclusion
re-proven true by (GR-101) with the LARGER boundary `6|δ|`. The offered
route sketch — *Step G119*'s "every **feasible** majority branch" counting
variant — is exactly what landed, at a new dart level (all three darts, the
`M`-inclusive analogue of (GR-85)(iv)'s `T`-identity).

**Coordinator verification at landing:** `--validate` re-run in full at
`PYTHONHASHSEED` 0 AND 999 (byte-identical modulo wall-clock; all headline
figures reproduced: 449 446 / 154 750 / 874 244 / 23 939 / 701 382 / gap-0
attainment on every leg / min #cheap 2 on the stratum / the witness
`dist = 4 = d_par(M)` / three full-cube audits at 4 stalls each, prices
`[0, 0]`); the (GR-100)/(GR-101)/(GR-102) derivations re-walked
line-by-line (the branchwise-vs-hubwise A-dart count, the blocked-end
injection, the deviation-set algebra, the interpolation arithmetic); the
L6 bare-token grep clean on the merged draft; `check-gapmap-cells.py`
green on the recomputed §(K-grid) row (trimmed to a current-state
statement per the checker's own guidance, no cap bump needed); the
driver's import list verified against the file itself (one consumer-list
correction made in the recorded *Harness debt* item: `perfect_matchings`).

---

## OQRANK — thirty-second ordinal, the fortieth direction (single dispatch, prepped 2026-08-25)

**Selection provenance:** the standing 2026-08-07 delegation; two option
selections at the third 2026-08-25 check-in (`notes/Phase39.md` *Current
state*, the third 2026-08-25 bullet): first **"Top-rung recon-first"** —
producing the eighth strategy-only pass's board re-rank (`f72cbb35`,
strategy §8's dated re-rank block) — then **"Rank 1: O29 ℚ(i) leg"**,
accepting that re-rank's front-runner. Dispatched **un-named, single, top
rung** (`recon-fable`). Derivation-first with a **ℚ(i)-compute-licensed
leg** (exact `ℚ(i)` is a base-layer primitive since the 2026-08-20
move-down: `exactcore.Gauss`). **The shared mechanics and landing checklist
above apply in full** — read-only w.r.t. every shared file, commit nothing,
draft to the untracked `notes/Pencil-draft-OQRANK.md`, tight return verdict.

**The target — (a₁)'s one-determinant residue, at the ⋆-eigen-block route
Step O29 names; a HIT closes input (a) at all 174 certified classes.**
Verbatim as OSCHU landed it (§(K-out) *Step O29*, (OC-33)(ii)): at a
target-rank chart point of `G`,

> `rank(Q|_D) = 3` ⟹ some point of `M` is good ⟹ **input (a) holds at
> that (shape, split)** —

a single `3 × 3` determinant: `x₁`-free, `λ`-free, stratum-free, one-point
decidable, evaluable at the very point the grid route constructs. Measured
`rank(Q|_D) = 3` at **570/570** points (104 POOL-OS + 292 POOL-OG + 174
POOL-OC2) and **174/174** isomorphism classes — witnesses, never a rate
((OC-7) discipline) — and **not proven**. A HIT chains with CIRR's chart
irreducibility ((CH-1)(a)) through (OC-19) into (OC-8)/(K-wit) per-class,
by a *mechanism* (the ⋆-eigen-block decoupling), the pitch route's first
recipe-shaped positive.

**The named route (Step O29's own "route, not a result" paragraph —
consume, complete, or kill it; if it dies, say where).** At a σ-fixed grid
configuration `D` is ⋆-invariant ((AC-2)/(AC-4)'s decoupling applied to
`Mot(H)`), so `D = D₊ ⊕ D₋` inside the `±1` eigenspaces of `⋆` ((FR-2)(iii))
with `B|_D = ⟨·,·⟩|_{D₊} ⊕ (−⟨·,·⟩|_{D₋})`, the blocks `B`-orthogonal. Over
`ℝ` definiteness would finish in two lines, but the grids are **`ℚ(i)`-only**
((AC-2) needs isotropic vectors; no σ-fixed real configuration exists) — so
the residue splits into **two independent per-eigen-block nondegeneracy
conditions**, and whether those are combinatorial at a grid point in
(FR-3)'s sense is **the genuine open piece**: `D` is a motion-derived space,
not a span of hinge lines, so (FR-3) does not apply as stated. That
per-block nondegeneracy argument is this direction's informal-proof
component; the compute leg is exact `ℚ(i)` (`exactcore.Gauss`), which the
O29-landing pass did not have.

**What counts as a HIT** — a proof of `rank(Q|_D) = 3` at (at least) one
target-rank chart point of **every** certified class (state the exact
quantifier delivered; the **class-uniform** statement of input (a) is NOT
the target and stays out of scope). Also valued: a **refutation by
witness** — the arc's first `rank(Q|_D) ≤ 2` class point ("What would
change this (Steps O25–O30)" item 1: if it also carries the ruling
`M̂ ∧ w` with `w` off `{pt(b), pt(c)}`, and at **every** `σ = 0` chart
point of that shape, it is the arc's first **(K-tight) event** — routes A
and B dead at that split, `hK` at the shape **untouched**, NOT a PENCIL
event; report the reading, fire nothing); or a **proof under a restricted
quantifier with the exact boundary named** (e.g. a per-eigen-block result
on a named sub-population). State which you got.

**Bars.** (OC-29)–(OC-34), (OC-31)'s tower input, (CH-1)/(CH-2),
(AC-1)–(AC-8), (FR-2)/(FR-3) — landed; consume, do not re-derive. Do
**not** re-run the landed pools (the 570-point record, the 174-class
census (OC-34)) — cite them; new sentences at new points are fine.
`place_pencil_general` batteries are never quoted as a rate or as evidence
about a generic chart point ((OC-7)); `repin.star_generic` gates any seed
you draw. Input (a)'s class-uniform statement, (GR-15) and class
uniformity are out of scope. No `.lean` is touched (the standing Lean
hold).

**Riders, verbatim from GCHEAP's.** TERMINATION check E1/E2/E3 at the
return (E3 is ARMED by GBAL — report, never fire). Cap disclosure: an
exhausted cap is *"not found under cap C"*, never nonexistence. F11: every
headline claim needs a driver that tests that sentence, and
"exhaustive"/"forced"/"the only" are their own claim class. All figures
exact (ℚ or `ℚ(i)` via `exactcore.Gauss`), seeded, degeneracy-guarded,
imported from the canonical layer (`notes/scripts/README.md` binds; a
symbolic (M2) leg, if any, adds `notes/scripts/m2/README.md`).

**Driver — conditional, at the pinned path `notes/scripts/w4/oqrank.py`.**
A purely derivational proof consuming only landed figures needs no new
driver — then state that disposition explicitly in the draft. Any new
measured or exhaustion claim mints the driver at the pinned path, importing
the harness read-only, left untracked for the coordinator to gate and
commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
OQRANK"): §(K-out) **extends** — no new section; labels
**(OC-40)–(OC-44)** ((OC-40) is SIGZ's returned label, re-claimed as the
head of the tail), **Steps O37–O41**; owning section stays authoritative;
return any unconsumed remainder to the tail.

### OQRANK — landing write-up (LANDED 2026-08-25, recon-fable, one serial coordinator commit)

**Verdict: a graded HIT of the first kind, with the exact quantifier
stated.** The ⋆-eigen-block route Step O29 named is **completed as a
mechanism**: at a σ-fixed target-rank grid point `D` splits ⋆-invariantly
with a **forced (1,2) profile** ((OC-40)), the one-determinant residue
factors as `rank(Q|_D) = [Q(g) ≠ 0] + rank Gram(D_Y)` with a full
Veronese/apolarity dictionary and parameter-free secant positives
((OC-41)), and the `X`-condition hits a **combinatorial WALL** — a
single-class `b`–`c` `X`-path forces `rank(Q|_D) = 2` at every draw
((OC-42)) — so the **naive first-colouring route is REFUTED as a class
statement** (27 of 174: 7 by the proven wall, 20 by a second,
uncharacterized confinement, persistent 4/4 draws each). The **hunted
route is GREEN at 174/174**: every certified class carries an exact ℚ(i)
σ-fixed target-rank grid chart point with `rank(Q|_D) = 3`, all in the
parameter-free secant/secant configuration, never past the fourth
colouring ((OC-43)); openness lifts each witness to every sufficiently
generic draw of its colouring, so **input (a) holds at every certified
class, per-class/per-exhibited-colouring-generic** ((OC-44)) — NOT
class-uniform (out of scope), NOT every-colouring (refuted). The `Y`-block
never degenerated (297/297); **zero rulings, so the (K-tight)-event branch
never fires** — every rank-2 point still individually witnesses input (a)
via (OC-30)(ii). New named residuals: the **wall-avoiding-colouring
existence** ((OC-44)(iii), the (GR-10)-shaped successor) and the **second
confinement's mechanism**. **Bars honoured:** landed chains consumed, not
re-derived; no pool re-run (the new pool is POOL-OQ2, the landed 570/174
figures cited); (OC-7) witness-not-rate discipline; no `.lean`. **E1/E2/E3
all NO — E3 stays ARMED by GBAL, not fired.** Canonical home §(K-out)
*Steps O37–O41* (`notes/Pencil-informal.md`); driver `w4/oqrank.py`
(controls + nine-chunk census); labels (OC-40)–(OC-44) all claimed.

**Two process exceptions at this dispatch, recorded (dispatch-log rows
follow at the wave close):** (i) the dispatch initially parked its census
in a **background run with a monitor** — the recurring F6 park shape, here
on a *research* dispatch whose prompt carried the foreground mandate in
prose but not the validated one-line F6 reminder; the coordinator's
resume message killed the background run and mandated the chunked
foreground split, and **every quoted figure comes from foreground runs
witnessed complete** (the agent's own disclosure, verified). (ii) The
dispatch was also killed once mid-turn by a **spend limit** and resumed
rung-stable after reset (the F4/F5 killed-dispatch-resume pattern, second
use this session after the debt-payment builder's API-timeout kill).

**Coordinator verification at landing:** `--controls` re-run (4/4
must-rejects) and the census re-run IN FULL as the nine foreground
`--range` chunks, each with an explicit timeout (one chunk re-issued
alone after a shared-budget cut) — aggregate figures reproduced exactly:
174 probed / 174 rank-3 witnesses / 0 misses; hit rows all
`(3, T, 2, 1, F, secant, secant)`; naive first-point rows 147 / 7 (wall)
/ 20 (second confinement). The (OC-40) eigen-split dimension count, the
(OC-41) Veronese Gram argument, the (OC-42) telescoping confinement and
the (OC-44) openness lift re-walked line-by-line; the scope line's
no-(K-tight)-event reading independently confirmed against POOL-OC2's
landed rank-3 ℚ-points; the L6 bare-token grep clean on the merged
draft; `check-gapmap-cells.py` green on the recomputed §(K-out) row
(trimmed to a current-state statement, no cap bump); the Section index's
19 stale line ranges recomputed as a rider.

---

## GPRICE — thirty-third ordinal, the forty-first direction (single dispatch, prepped 2026-08-25)

**Selection provenance:** the standing 2026-08-07 delegation; shape adjudicated
at the **fourth** 2026-08-25 check-in — **"Single direction,
front-runner-first"** (an option selection; `notes/Pencil-adjudications.md`,
the fourth 2026-08-25 bullet). Front-runner-first is the 2026-08-25 re-rank's
own order with its rank 1 (the O29 ℚ(i) eigen-block leg) landed by OQRANK:
**(GR-104)(i)**, the re-rank's rank 2 and the board's highest unlanded entry
(`notes/Pencil-strategy.md` §8). Dispatched **un-named, single, top rung**
(`recon-fable` — fable is dispatchable this session per the same check-in).
Derivation-first tier. **The shared mechanics and landing checklist above
apply in full** — read-only w.r.t. every shared file, commit nothing, draft to
the untracked `notes/Pencil-draft-GPRICE.md`, tight return verdict.

**The target — (GR-104)(i), the price form of the selection clause; it is the
whole remaining gap between the proven constant 4 and (b′)'s target constant
2.** Verbatim as GCHEAP minted it (§(K-grid) *Step G124*,
`notes/Pencil-informal-grid.md`):

> **(i) The price form.** *At some parity-optimal configuration with
> `|δ| ≤ 2` — balanced ones qualifying vacuously — some majority-side flip
> has `f(p + χ_γ) ≤ f(p) + 2`.*

This is what the constant 2 actually consumes ((GR-C2) was only ever its
sufficient certificate, via (GR-86)); it strictly relaxes (GR-C2) — a
doubly-blocked matching branch is allowed if its two repair chains happen to
price `≤ 0`. Standing: a **theorem at `n ≤ 10`** (by (GR-101)(ii) + (GR-86));
at the three audited `n = 12` stall pairs it holds with **price 0 at the
stalled configurations themselves** (measured, NOT a theorem); **OPEN from
`n = 12`**. What a proof buys (*Step G124*'s own what-would-change-this
(iii)): **(b′) at the constant 2, modulo (GR-C1) alone, at every `n`** — the
last constant gap on the GFLOW descent chain.

**The named inputs (landed; consume, do not re-derive).** (i) **(GR-100)'s
lone-dart identity + blocked-end capacity** and **(GR-101)'s selection
corollary** prove the `n < 6|δ|` half, the boundary exact by (GR-103).
(ii) **(GR-102), the stall tax** `dist(z, M) ≥ |a_M − b_M + δ|`: a refuting
(shape, M) pair needs ALL parity-optimal configurations unbalanced and ALL
price-stalled, and (GR-102) forces `d_par(M) ≥ 2|δ| − b_M` at such a pair —
none of the three audited pairs comes close (all have balanced optima in
bulk). (iii) **The adversarial control**: the `n = 12`, `2k = 2` stall pairs
((GR-103), driver `w4/gcheap.py --bnd`, shapes/matchings/`z` printed for
independent reconstruction) are where any hunt should grow from. (iv) **The
open mechanism question is the natural first attack** (*Step G124*'s
what-would-change-this (iii)): the audits suggest the stalled configurations'
repair chains may *always* price `≤ 0` at parity-optimality — *why* is the
open question; the price `f` and the repair chains are §(K-grid)'s defined
terms, and the demand form (GR-97) / counting lemma (GR-98) / selection
theorem (GR-99) are the landed instruments the (GR-R1) and (GR-C2)(every-step)
proofs actually used. Treat any sketch as a candidate, not a pin — if it
dies, say where.

**What counts as a HIT** — a proof of (GR-104)(i) unconditional in `n` (state
the exact quantifier delivered: per-configuration price bound, existential
over flips, any hypotheses carried). Also valued, on the (GR-29)/(GR-30)
precedent: a **refutation by witness** — a (shape, M) pair whose
parity-optimal configurations are ALL unbalanced and ALL price-stalled (this
kills the constant-2 route and leaves the proven 4 standing — state exactly
what survives, in particular whether (GR-102)'s confinement localizes the
failure and what the interpolation (GR-104)(ii) still gives); or a **proof
under a restricted quantifier with the exact boundary named** (e.g. a bound
past `n = 12`, a `2k` stratum, or a sharper price constant between 0 and 2).
State which of the three you got.

**Bars.** Do **not** attack (GR-C1) — a separate residual (GPSA's first
clause; (GR-69) its exact `n ≤ 6` boundary). (GR-R1) and (GR-C2)'s settled
halves are **landed** — consume, do not re-attack; the per-configuration
refutation (GR-103) stands — do not try to repair it. Do not re-derive
(GR-49)–(GR-54), (GR-67)–(GR-72), (GR-85)–(GR-90), or (GR-97)–(GR-104)'s
landed parts. Do **not** re-run the exhaustive censuses or the three
full-cube audits — cite them; a *new* driver mode that tests a *new* sentence
is fine, a re-measurement of a landed figure is not. (GR-15) and class
uniformity are out of scope. No `.lean` is touched (the standing Lean hold).

**Riders, verbatim from GCHEAP's.** TERMINATION check E1/E2/E3 at the return
(E3 is ARMED by GBAL — firing is the coordinator's action; report, never
fire). Cap disclosure: an exhausted cap is *"not found under cap C"*, never
nonexistence. F11: every headline claim needs a driver that tests that
sentence, and "exhaustive"/"forced"/"the only" are their own claim class. The
shift-metric layer is UNBOUNDED ((GR-43)) — any bound is on a **difference**.
All figures exact ℚ, seeded, degeneracy-guarded, imported from the canonical
layer (`notes/scripts/README.md` binds; the *Divergences* table names the
same-name-different-semantics traps) — **the balance layer is
`w4/gridbal_common`**: import the moved devices from there directly, never
via the sibling re-exports (GCHEAP's residual sibling imports are already a
recorded *Harness debt* item — do not extend it).

**Driver — conditional, at the pinned path `notes/scripts/w4/gprice.py`.** A
purely derivational proof consuming only landed figures needs no new driver —
then state that disposition explicitly in the draft. Any new measured or
exhaustion claim mints the driver at the pinned path, importing the harness
read-only, left untracked for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GPRICE"): §(K-grid) **extends** — no new section; labels
**(GR-105)–(GR-109)**, **Steps G125–G129**; owning section stays
authoritative; return any unconsumed remainder to the tail.

### GPRICE — landing write-up (LANDED 2026-08-25, recon-fable, one serial coordinator commit)

**Verdict: a graded outcome of the third kind — (GR-104)(i) proven under a
restricted quantifier with the restriction exactly named — plus an empty
refutation hunt to `n = 18`.** The colour-swap identity (GR-105), the
reversal-set normal form (GR-106) (`dist = n − |R|` exact at every `O ⊆ M`
pair; `f` computable in `2^n`, reaching `n = 18` where the cube stops at 12)
and the reachability theorem (GR-107) (affine pattern-subspaces; the linkage
obstruction to price `≤ 0`) prove: (GR-104)(i) holds **outright at `2k = 2`,
every `n`, whenever some odd branch is off `M`**, and at the `O ⊆ M` cell it
is a **theorem modulo the minted balance law (GR-108) alone** — every
`2k = 2` failure of the price form is a **gap-4** failure of (GR-108) at an
`O ⊆ M` pair. (GR-108) itself is **measured, not proven**: 0 violations at
1 431 swept pairs (the `n ≤ 6` sub-cell EXHAUSTIVE at 1 034; the spec's
refutation object — all optima unbalanced ∧ all price-stalled — NOT FOUND,
every swept pair carrying a balanced optimum outright), its strong form
failing from exactly `n = 12` (65/101 at the (GR-103) control), so a proof
must exchange between maximum reversal sets — the re-aimed mechanism
question. Residual, in successor order: prove (GR-108); the `2k ∈ {4, 6}`
`O ⊄ M` corner (untouched beyond the landed `n ≤ 10`); (GR-C1) past the
stratum. **Bars honoured:** (GR-C1)/(GR-103)/(GR-99) consumed, not attacked;
rank-free throughout; no landed census or full-cube audit re-run (the
driver's quantifiers are the NEW `O ⊆ M` cell decomposition and new
`n = 14/16/18` pools); (GR-15) / class uniformity untouched; no `.lean`
touched. **E1/E2 NO; E3 stays ARMED by GBAL, not fired** (the movement is on
(b′)'s selection layer, not entry 1). Canonical home §(K-grid) *Steps
G125–G129* (`notes/Pencil-informal-grid.md`); driver `w4/gprice.py` (five
modes, ~67 s); labels (GR-105)–(GR-109) and Steps G125–G129 all claimed,
none returned.

**One scope note recorded at landing (no defect in the operative claims):**
the draft's reduction prose reads "a (GR-104)(i) failure at `2k = 2` is
exactly a failure of (GR-108)"; the operative direction is
(GR-108) ⟹ (GR-104)(i) (the (GR-109) status table's "modulo (GR-108)
alone"), and the converse holds in the **gap-4 form** the draft itself
states — a gap-**2** failure of (GR-108) would leave (GR-104)(i) intact
(the flip prices exactly 2). No swept pair exhibits any nonzero gap, so
nothing measured turns on the distinction.

**Coordinator verification at landing:** every mode re-run individually in
the foreground (`--cell`/`--seed`/`--mech`/`--hunt`) plus `--validate` at
`PYTHONHASHSEED` 0 AND 999 (byte-identical modulo wall-clock; all headline
figures reproduced: 1 034 stratum pairs / gap `{0: …}` on every leg /
`f`-spread histograms / the control's `d_par = 4`, prices `[0, 0]` /
65/101 and 32/66 strong-form ratios / 373 hunt pairs, 0 candidates); the
(GR-105) involution and (GR-106) orientation/reversal-point derivations
re-walked; the driver's import list verified against the file itself
(direct `gridbal_common`, rank-free — `fully_good_rank` absent); the L6
bare-token grep clean on the merged draft; `check-gapmap-cells.py` green
on the recomputed §(K-grid) row (trimmed to a current-state statement per
the checker's own guidance, no cap bump).

## GBLAW — thirty-fourth ordinal, the forty-second direction (single dispatch, prepped 2026-08-25)

**Selection provenance:** the standing 2026-08-07 delegation; shape adjudicated
at the **fifth** 2026-08-25 check-in — **"Single direction,
front-runner-first"** (an option selection; `notes/Pencil-adjudications.md`,
the fifth 2026-08-25 bullet). With the 2026-08-25 re-rank's ranks 1 and 2 both
landed the same day (OQRANK / GPRICE), the front-runner is GPRICE's own
residual #1, the head of *Step G129*'s successor order and the first entry of
`notes/Phase39.md` *Hand-off*'s candidate list: **(GR-108), the balance law**
— the whole remaining gap to (GR-104)(i) at `2k = 2`. The same check-in
scoped the GCHEAP/GPRICE harness-debt payment to precede this dispatch (paid,
`782e8bcd`). Dispatched **un-named, single, top rung** (`recon-fable` — fable
is dispatchable this session per the same check-in). Derivation-first tier —
the proof shape is pinned and the sweeps are landed; new measurement is the
conditional, not the default. **The shared mechanics and landing checklist
above apply in full** — read-only w.r.t. every shared file, commit nothing,
draft to the untracked `notes/Pencil-draft-GBLAW.md`, tight return verdict.

**The target — (GR-108), the balance law; it is the whole remaining gap to
(GR-104)(i) at `2k = 2`, every `n`.** Verbatim as GPRICE minted it
(§(K-grid) *Step G128*, `notes/Pencil-informal-grid.md`):

> *At every perfect matching `M` of a cubic loop-free hub multigraph with
> all odd branches inside `M`, the parity optimum is attained at a
> **balanced** pattern:* `d_adm(M) = d_par(M)`.

In the (GR-106) model this says some structurally-maximum reversal set
reaches a balanced pattern ((GR-107)(ii) with `M* = n − d_par`). Standing:
**minted, measured, NOT a theorem** — 0 violations at all 1 431 swept
`O ⊆ M` pairs (the `n ≤ 6` stratum sub-cell EXHAUSTIVE at 1 034,
cube-asserted; V8; the (GR-103) control; seeded `n = 8`–`14`; the
cell-targeted sampler to `n = 18`, `2k ∈ {2, 4}`). What a proof buys
((GR-109)'s successor list, entry 1): **(GR-104)(i) becomes a theorem at
`2k = 2`, every `n`, unconditionally** — with the off-`M` case already
proven outright ((GR-107)(iii)), this closes the `2k = 2` stratum entirely,
leaving (b′) at the constant 2 resting on (GR-C1) plus the `2k ∈ {4, 6}`
`O ⊄ M` corner alone.

**The named inputs (landed; consume, do not re-derive).** (i) **The
reversal-set normal form (GR-106)**: at an `O ⊆ M` matching an admissible
configuration IS a set `R` of reversal hubs meeting every `F`-cycle evenly,
sink/source alternately labelled, no even matching pair mono-labelled, each
A-end a source / B-end a sink, with `dist(z, M) = n − |R|` — the exact
combinatorial carrier the proof works in. (ii) **The reachability theorem
(GR-107)**: the patterns at which one reversal set stays valid form an
affine subspace `p ⊕ L` (`L` spanned by end-free branches and block flips);
its clause (v) is half the freedom inventory — **adjacent-pair removal is
free**, and at a maximum `R` every same-gap through-pair insertion is
blocked only by a matching obstruction — the two moves a surgery would
combine. (iii) **The colour-swap identity (GR-105)** — the global
bit-complement is a dist-preserving admissibility involution at every
matching, so `f(p) = f(p̄)`; any balance argument gets this symmetry free.
(iv) **The strong form's exact boundary (GR-108)(iii) is the pinned proof
shape and the reason nothing per-set works**: *every* structurally-maximum
`R` reaches balance at all 1 034 stratum pairs, but only 65/101 at the
(GR-103) control (`n = 12`, worst seeded ratio 32/66) — the γ-linked
maximum family is exactly the stalled-optimum family and first inhabits
`n = 12`, the same boundary (GR-101)/(GR-103) pinned. **Any proof must
produce the balance-reaching maximum from a linked one — an exchange
between maximum reversal sets.** (v) **The adversarial control**: the
`n = 12` (GR-103) pairs and the 36/101 strong-form failures there are where
any refutation hunt or exchange-blocking analysis should grow from
(`w4/gprice.py --mech` prints the maximum-family balance census; shapes /
matchings / `z` reconstructible via `w4/gcheap.py --bnd`). Treat any
exchange sketch as a candidate, not a pin — if it dies, say where.

**What counts as a HIT** — a proof of (GR-108) (state the exact quantifier
delivered: which maximum reversal set is produced, what the exchange
consumes, any hypotheses carried beyond `O ⊆ M` + cubic loop-free). Also
valued, on the (GR-29)/(GR-30) precedent: a **refutation by witness** per
(GR-108)(iv) — an `O ⊆ M` pair at which every structurally-maximum `R`
fails (GR-107)(ii) (at `2k = 2`: every maximum `R` linked with forced-equal
colours) — which by (GR-107)(iii) refutes (GR-104)(i) as well and by
(GR-102) needs `d_par(M) ≥ 2|δ| − b_M` at its stalled optima (state exactly
what survives, in particular the proven `n ≤ 10` theorem and the constant-4
chain); or a **proof under a restricted quantifier with the exact boundary
named** (e.g. a `2k` stratum, an `n` bound past 12, or the strong form
restored under a named structural hypothesis on the linked family). State
which of the three you got.

**Bars.** Do **not** attack (GR-C1) — a separate residual (GPSA's first
clause; (GR-69) its exact `n ≤ 6` boundary). Do **not** attack the
`2k ∈ {4, 6}` `O ⊄ M` corner — it is (GR-109)'s successor entry 2, a
separate direction needing its own model extension. (GR-105)–(GR-107) and
(GR-97)–(GR-104)'s landed parts are **landed** — consume, do not re-derive;
the (GR-103) per-configuration refutation stands — do not try to repair it.
Do not re-derive (GR-49)–(GR-54), (GR-67)–(GR-72), or (GR-85)–(GR-90). Do
**not** re-run the exhaustive censuses, the full-cube audits, or GPRICE's
1 431-pair sweep — cite them; a *new* driver mode that tests a *new*
sentence is fine, a re-measurement of a landed figure is not. (GR-15) and
class uniformity are out of scope. No `.lean` is touched (the standing Lean
hold).

**Riders, verbatim from GPRICE's.** TERMINATION check E1/E2/E3 at the return
(E3 is ARMED by GBAL — firing is the coordinator's action; report, never
fire). Cap disclosure: an exhausted cap is *"not found under cap C"*, never
nonexistence. F11: every headline claim needs a driver that tests that
sentence, and "exhaustive"/"forced"/"the only" are their own claim class. The
shift-metric layer is UNBOUNDED ((GR-43)) — any bound is on a **difference**.
All figures exact ℚ, seeded, degeneracy-guarded, imported from the canonical
layer (`notes/scripts/README.md` binds; the *Divergences* table names the
same-name-different-semantics traps) — **the balance layer is
`w4/gridbal_common`**, extended 2026-08-25 by the GCHEAP/GPRICE debt payment
(the (GR-49)/(GR-50) z-form surface, `majority_of`, and the cube
combinatorics `adm_cube`/`block_ends_at`/`f_layers` all live there now):
import the moved devices from there directly, never via the sibling
re-exports, and record any new §2-rule-2 trip as a *Harness debt* item —
do not make the move.

**Driver — conditional, at the pinned path `notes/scripts/w4/gblaw.py`.** A
purely derivational proof consuming only landed figures needs no new driver —
then state that disposition explicitly in the draft. Any new measured or
exhaustion claim mints the driver at the pinned path, importing the harness
read-only, left untracked for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GBLAW"): §(K-grid) **extends** — no new section; labels
**(GR-110)–(GR-114)**, **Steps G130–G134**; owning section stays
authoritative; return any unconsumed remainder to the tail.

### GBLAW — landing write-up (LANDED 2026-08-26, recon-fable, one serial coordinator commit)

**Verdict: an honest OPEN reshape — none of the spec's three HIT shapes as
posed; (GR-108) is neither proven nor refuted.** What lands is the exchange
calculus the pinned proof shape called for, PROVEN in three theorems: the
**arc-transversal normal form** (GR-110) (at a fixed sink set the maximum
family IS an independent-transversal family, `|R| = 2|K|`, sources sliding
freely inside sink-arcs), the **recombination theorem** (GR-111) (two maxima
exchange along glued difference components, both recombinants again valid
maxima, the maximum family recombination-connected — and the `2k = 2`
refutation shape sharpens to **universal linkage**), and the **escape
lemma** (GR-112) (imbalance intervals move by at most one notch per fine
move, so no fine move crosses the balance layer and **(GR-108) ⟸
existential escape**). The measured layer (GR-113): the `n ≤ 6` stratum has
**no pos/neg-forcing maximum at all** (12 448/12 448, exhaustive — strictly
stronger than (GR-108)(iii)'s landed stratum half); **universal escape**
holds through `n = 14` and **FAILS at exactly one `n = 16` pair** (the
`strand_witness`: single 16-cycle 2-factor, 152 maxima, two stranded pure
components of 32, safe flips included — the second localization of (GR-108)
to fail at a finite boundary); **existential escape** — the reduction's
hypothesis and the new named open kernel — has **0 failures at all 1 099
swept pairs**; and the (GR-111)(v) separation criterion rescues 36/36 at
the control but **0/48 at the witness, exhaustively** — the witness is
universally linked while the law holds there via natively balanced maxima,
so the two mechanisms are incomparable and **any proof must produce the
balance-reaching maximum globally, not by repairing an arbitrary maximum**.
Two sub-claims minted-and-killed inside the pass (law untouched): universal
escape as a per-component locality; separation as a complete proof route.
A Haxell-type sufficient condition rides as a non-headline remark (citation
verified at landing: P. E. Haxell, *A note on vertex list colouring*,
Combin. Probab. Comput. **10** (2001), no. 4, 345–347). Canonical home
§(K-grid) *Steps G130–G134* (`notes/Pencil-informal-grid.md`); driver
`w4/gblaw.py` (five modes, ~25 s); labels (GR-110)–(GR-114) and Steps
G130–G134 all claimed, none returned; the (GR-109) successor list's entry 1
revised in place per (GR-114). TERMINATION: E1/E2 not fired; E3 stays ARMED
(by GBAL) and does not fire — the movement is on (b′)'s selection layer,
not entry 1.

**Coordinator verification at landing:** every mode re-run individually in
the foreground (`--form`/`--conn`/`--recomb`/`--strand`) plus `--validate`
at `PYTHONHASHSEED` 0 AND 999 (byte-identical modulo wall-clock; all
headline figures reproduced: 6 294 (pair, sink set) cells / 6 426 triples /
the stratum's 12 448-0-forcing counter / existential escape 0 failures /
the witness profile 88 = 56 + 16 + 16 plus 32 + 32 stranded / separation
0/32 and 0/16 over all 48 partners); the (GR-110) counting, the (GR-111)
gluing argument and the (GR-112) notch bound re-walked; the driver's import
list verified against the file itself (direct `gridbal_common`, rank-free —
`fully_good_rank` absent; five `gprice` devices recorded as the new
*Harness debt* item); the L6 bare-token grep clean on the merged draft;
`check-gapmap-cells.py` green on the recomputed §(K-grid) row (the close-it
cell recomputed to a current-state statement per the checker's own
guidance, no cap bump; the status cell's stale (GR-R1)/(GR-C2) tail
repaired to current standing in the same pass).

## GXESC — thirty-fifth ordinal, the forty-third direction (single dispatch, prepped 2026-08-26)

**Selection provenance:** the standing 2026-08-07 delegation; shape adjudicated
at the **sixth** check-in of the 2026-08-25/26 session — **"Single direction,
front-runner-first"** (an option selection; `notes/Pencil-adjudications.md`,
the 2026-08-26 bullet). With the 2026-08-25 re-rank's ranks 1 and 2 landed
(OQRANK / GPRICE) and GBLAW landed 2026-08-26, the front-runner is GBLAW's own
sharpened residual, the head of *Step G134*'s successor order and the first
entry of `notes/Phase39.md` *Hand-off*'s candidate list: **existential
escape** — the whole remaining gap to (GR-108), hence to (GR-104)(i) at
`2k = 2`. Dispatched **un-named, single, top rung** (`recon-fable`).
Derivation-first tier — the calculus is proven and the sweeps are landed; new
measurement is the conditional, not the default. **The shared mechanics and
landing checklist above apply in full** — read-only w.r.t. every shared file,
commit nothing, draft to the untracked `notes/Pencil-draft-GXESC.md`, tight
return verdict.

**The target — existential escape, (GR-112)(v)'s hypothesis; it is the whole
remaining gap to (GR-108) at `2k = 2`, every `n`.** Verbatim as GBLAW minted
it (§(K-grid) *Step G132*, `notes/Pencil-informal-grid.md`):

> *At every pair whose maximum family contains a pos-forcing member, some
> pos-forcing maximum admits a fine-move walk out of the pos class* (pairs
> with no pos/neg-forcing maxima satisfy the law vacuously — every maximum
> is balance-valid; pos and neg members come in (GR-105) pairs).

Standing: **measured, NOT a theorem — 0 failures at all 1 099 GBLAW-swept
`O ⊆ M` pairs** (stratum EXHAUSTIVE at 1 034 with no forcing maximum at all,
V8, the (GR-103) control, seeded cell pools to `n = 16`), at move levels
L2/L3 (slides alone already fail one `n = 14` pair). What a proof buys: by
the escape lemma (GR-112)(v) it proves **(GR-108)**, hence — with
(GR-107)(iii) — **(GR-104)(i) becomes a theorem at `2k = 2`, every `n`,
unconditionally**, leaving (b′) at the constant 2 resting on (GR-C1) plus
the `2k ∈ {4, 6}` `O ⊄ M` corner alone. **An unconditional proof of
(GR-108) by the OTHER live shape — a global/extremal construction of a
balance-valid maximum ((GR-114) residual shape (b)) — counts identically;
state which shape you delivered.**

**The named inputs (landed; consume, do not re-derive).** (i) **The
arc-transversal normal form (GR-110)**: the maximum family stratifies by
sink set into independent-transversal families of size `2|K|`, sources
sliding freely inside sink-arcs — the parametrization any global
construction works in; its Haxell-type remark ((GR-110)(iv), Haxell CPC 10
(2001) 345–347) is the one unconditional large-arc criterion currently
proven. (ii) **The recombination theorem (GR-111)** — proven
maximum-preserving; its (v) separation criterion is REFUTED as a *complete*
route (0/48 at the witness) but stays a valid per-pair instrument.
(iii) **The escape lemma (GR-112)**: the imbalance-interval classification
(bal/pos/neg), the notch bound, and the reduction itself — the fine-move
calculus is slides + adjacent-pair teleports + safe flips, all proven
maximum-preserving. (iv) **The (GR-113) witness is the adversarial
control**: at the `n = 16` strand witness existential escape HOLDS — the
big component's 16 pos maxima reach balance-valid company; the stranded 32
are exactly the maxima a proof may NOT be forced to start from, so any
selection argument must be able to avoid them. `w4/gblaw.py --strand`
prints the witness in full; `--conn` the fine-move census. (v) *Step
G134*'s freedom inventory and *What would change this* (iii): a **fourth
move class** (multi-pair moves; removal of non-adjacent pairs) could
restore even universal escape — the witness is the exact test case and
`gblaw`'s move generators are the harness for it. Treat any walk-selection
or construction sketch as a candidate, not a pin — if it dies, say where.

**What counts as a HIT** — a proof of existential escape, or of (GR-108)
directly by global construction (state the exact quantifier delivered:
which pos-forcing maximum starts the walk / which balance-valid maximum is
constructed, what selects it, any hypotheses carried beyond `O ⊆ M` + cubic
loop-free + `M` perfect). Also valued, on the (GR-29)/(GR-30) precedent: a
**refutation by witness** — a pair whose every fine component of forcing
maxima is stranded AND whose balance-valid stratum is empty refutes
(GR-108) outright (*Step G134*'s hunt shape: grow `strand_witness`-like
single-cycle pairs and test `bal = 0`); a weaker witness killing
existential escape alone (all pos-forcing maxima stranded, balance-valid
maxima existing elsewhere) kills only the (GR-112)(v) route — the law
survives, state exactly what does; or a **proof under a restricted
quantifier or an extended move class with the exact boundary named** (e.g.
a fourth move restoring universal escape, a `2k` stratum, an `n` bound).
State which you got.

**Bars.** Do **not** attack (GR-C1) or the `2k ∈ {4, 6}` `O ⊄ M` corner —
separate residuals. (GR-105)–(GR-114) and (GR-97)–(GR-104)'s landed parts
are **landed** — consume, do not re-derive; the (GR-113) witness's figures
are cap-free at that pair — do not try to repair or re-derive them. Do
**not** re-run the exhaustive censuses, GPRICE's 1 431-pair sweep, or
GBLAW's 1 099-pair escape census — cite them; a *new* driver mode that
tests a *new* sentence is fine, a re-measurement of a landed figure is not.
(GR-15) and class uniformity are out of scope. No `.lean` is touched (the
standing Lean hold).

**Riders, verbatim from GBLAW's.** TERMINATION check E1/E2/E3 at the return
(E3 is ARMED by GBAL — firing is the coordinator's action; report, never
fire). Cap disclosure: an exhausted cap is *"not found under cap C"*, never
nonexistence. F11: every headline claim needs a driver that tests that
sentence, and "exhaustive"/"forced"/"the only" are their own claim class. The
shift-metric layer is UNBOUNDED ((GR-43)) — any bound is on a **difference**.
All figures exact ℚ, seeded, degeneracy-guarded, imported from the canonical
layer (`notes/scripts/README.md` binds; the *Divergences* table names the
same-name-different-semantics traps) — **the balance layer is
`w4/gridbal_common`**: import the moved devices from there directly, never
via the sibling re-exports. The five `gprice` devices and `gblaw`'s whole
device set are sibling leaves — a sideways import is in policy but trips §2
rule 2's recorded-debt rule: extend the existing GBLAW *Harness debt* item's
consumer list in your draft (the coordinator records it), do NOT make any
move.

**Driver — conditional, at the pinned path `notes/scripts/w4/gxesc.py`.** A
purely derivational proof consuming only landed figures needs no new driver —
then state that disposition explicitly in the draft. Any new measured or
exhaustion claim mints the driver at the pinned path, importing the harness
read-only, left untracked for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GXESC"): §(K-grid) **extends** — no new section; labels
**(GR-115)–(GR-119)**, **Steps G135–G139**; owning section stays
authoritative; return any unconsumed remainder to the tail.

### GXESC — landing write-up (LANDED 2026-08-26, recon-fable, one serial coordinator commit)

**Verdict: REFUTATION BY WITNESS — the spec's named refutation shape in its
strong form. (GR-108), the balance law, is FALSE from `n = 16`, and
existential escape ((GR-112)(v)'s hypothesis, the dispatch target) is FALSE
with it.** Four explicit single-`F`-cycle `O ⊆ M`, `2k = 2` habitat pairs
(two at `n = 16`, two at `n = 20`; `refut_specs` in the driver) have maximum
families that are pure pos + neg with **no balance-valid member** and
`d_adm − d_par = 2`; with no bal maximum, no fine-move walk can leave the
pos class ((GR-112)(iv)), so neither of GBLAW's two live shapes can exist.
The first witness, **mut16, is ONE even-chord endpoint transposition from
the (GR-113) strand-witness diagram** (odd chords identical, asserted) —
found by the exact hunt shape *Step G134* pinned. Every figure re-derived
through THREE independent exact models, two of them landed
(`gprice.rmodel_f`; at `n = 16` `gblaw.enum_family`) — the (GR-83)/(GR-113)
verification bar. **What survives:** **(GR-104)(i) holds at all four
witnesses** (both one-flip prices exactly +2); the pass proves it is
**exactly the gap-2 law** `d_adm ≤ d_par + 2` at this cell ((GR-117)(i))
and **proves the law wherever some maximum is balance-valid or
half-resident** ((GR-117)(ii), a one-pair-removal surgery); the one open
case — every maximum forcing with both branches fully resident — is
measured EMPTY at all 248 hunted pairs, and a gap-4 pair (a genuine
(GR-104)(i) refutation) would have to live there. New proven instrument:
the **reversal-label ledger** (GR-115) (`Σ c_j + h = 0`; **M-closed ⟹
balance-valid at every `2k`**). Bonus finding ((GR-118)(v)): under interval
flips at dip 2 the (GR-113) witness's 32 "stranded" maxima all reach bal
company — the strandedness was the L1–L3 move set's artifact, answering
*Step G134*'s fourth-move question at its test case (and moot for the law).
**The reshaped residual is the HALF-WITNESS CLAUSE** ((GR-117)(iii)): every
pos-carrying `O ⊆ M` pair has a maximum that is balance-valid or
half-resident — strictly weaker than the dead (GR-108), with a proven
mechanism, closing (GR-104)(i) at `2k = 2` unconditionally if proven.
Canonical home §(K-grid) *Steps G135–G139* (`notes/Pencil-informal-grid.md`);
driver `w4/gxesc.py` (six modes, ~250 s); labels (GR-115)–(GR-119) and Steps
G135–G139 all claimed, none returned; (GR-109)'s and (GR-114)'s superseded
rows and successor entries revised in place per (GR-119). GPRICE's
1 431/1 431 and GBLAW's 1 099-pair records stand as statements about their
pools — the witnesses are new pairs outside both, in the cell those
samplers rarely draw. TERMINATION: E1 not fired; E2 not fired (the refuted
(GR-108) is not a ledger entry and arrives with its successor named — the
carve-out); E3 stays ARMED (by GBAL) and does not fire.

**Coordinator verification at landing:** every mode re-run individually in
the foreground (`--ledger`/`--closure`/`--strand`/`--verify`/`--hunt`) plus
`--validate` at `PYTHONHASHSEED` 0 AND 999 (byte-identical modulo
wall-clock; all headline figures reproduced: the four witnesses'
`(M*, N, pos, neg, bal, gap)` profiles through all three models / the
248-pair gap histogram `{0: 244, 2: 4}` with `all22` = 0 and gap-4 = 0 /
the 39 642-config exhaustive ledger assert / the dip-2 32/32
reconnection); the (GR-115) ledger identity and the (GR-117)(ii) surgery
re-walked against the landed (GR-106)/(GR-107) statements; the driver's
import list verified against the file itself (direct `gridbal_common`,
rank-free — `fully_good_rank` absent; the twelve `gprice`/`gblaw` sibling
imports recorded as the GBLAW debt item's extension); the L6 bare-token
grep clean on the merged draft; `check-gapmap-cells.py` green on the
recomputed §(K-grid) row.

## GHWIT — thirty-sixth ordinal, the forty-fourth direction (single dispatch, prepped 2026-08-26)

**Selection provenance:** the standing 2026-08-07 delegation; shape adjudicated
at the **seventh** check-in (the 2026-08-26 session) — **"Single direction,
front-runner-first"** (an option selection; `notes/Pencil-adjudications.md`,
the 2026-08-26 seventh-check-in bullet). With GXESC landed 2026-08-26, the
front-runner is GXESC's own reshaped residual, the head of *Step G139*'s
successor order and the first entry of `notes/Phase39.md` *Hand-off*'s
candidate list: the **half-witness clause** (GR-117)(iii) — the whole
remaining gap to (GR-104)(i) at `2k = 2`, every `n`, unconditionally.

**Rung — read this before calibrating the return.** Dispatched **un-named,
single**, at **`recon-opus`, NOT the top rung**: at the same check-in the
user's session-config selection left "all four rungs dispatchable"
**unselected**, so fable is conserved this session (`weekly_scoped` 92 %
critical corroborates), and opus is the playbook's nearest available rung at
or above the mapping. **GHWIT is the first of the seven single directions
GFLIP–GHWIT not to run at `recon-fable`** — the six predecessors' returns are
the calibration baseline, and a thinner return here is a rung artifact to
report, not a property of the target. Derivation-first tier — the surgical
mechanism is proven and the hunt is landed; new measurement is the
conditional, not the default. **The shared mechanics and landing checklist
above apply in full** — read-only w.r.t. every shared file, commit nothing,
draft to the untracked `notes/Pencil-draft-GHWIT.md`, tight return verdict.

**The target — the half-witness clause, (GR-117)(iii).** Verbatim as GXESC
minted it (§(K-grid) *Step G137*, `notes/Pencil-informal-grid.md`):

> *Every pos-carrying `O ⊆ M` pair has a maximum that is balance-valid or
> half-resident.*

Equivalently, in the contrapositive form the landed hunt already tests: **no
`O ⊆ M` pair has every maximum forcing with both odd branches fully
resident** (residency (2,2), `|h| = 4`).

Standing: **minted and measured, NOT a theorem — 0 all-(2,2) pairs and 0
gap-4 pairs among all 248 gated single-cycle pairs hunted** ((GR-117)(iii),
(GR-118)(i); caps disclosed at *Step G138*, pools to `n = 20`), including all
four (GR-116) refutation witnesses. What a proof buys: with (GR-117)(ii)'s
proven surgery it makes the **gap-2 law** — equivalently, by (GR-117)(i),
(GR-104)(i) at `2k = 2`, `O ⊆ M` — a theorem; with (GR-107)(iii)'s proven
off-`M` half, **(GR-104)(i) becomes a theorem at `2k = 2`, every `n`,
unconditionally**, leaving (b′) at the constant 2 resting on (GR-C1) plus the
`2k ∈ {4, 6}` `O ⊄ M` corner alone.

**The named inputs (landed; consume, do not re-derive).** (i) **The
reversal-label ledger (GR-115)** — proven: `Σ_j c_j + h = 0`; M-closed ⟹
balance-valid at every `2k`; at `2k = 2`, `|h| ≤ 1` forces balance-validity
and pos-forcing forces `h ≤ −2`; and (GR-115)(iii), **the sharpest instrument
pointed straight at the target** — the `h = −2` pos maxima are *automatically*
half-resident on both branches. Since the open case is exactly `|h| = 4`, the
clause to beat reduces to **"some maximum has `|h| = 2`"**; start there and
say explicitly if it fails. (ii) **The surgery (GR-117)(ii)** — proven: one
(GR-107)(v) adjacent-pair removal at the lone resident end frees the branch at
`|R| = M* − 2`, giving gap ≤ 2. The mechanism is *done*; what is missing is
only the **existence** of a maximum it can be applied to. (iii) **The
arc-transversal normal form (GR-110)** — the maximum family stratifies by sink
set into independent-transversal families of size `2|K|`, sources sliding
freely inside sink-arcs; its Haxell-type remark ((GR-110)(iv), Haxell, *Comb.
Probab. Comput.* **10** (2001) 345–347) is the one unconditional large-arc
criterion proven. This is the parametrization any existence or extremal
construction works in. (iv) **(GR-111) recombination** (proven
maximum-preserving; its (v) separation criterion is REFUTED as a *complete*
route but stays a valid per-pair instrument), **(GR-112)**'s fine-move
calculus (slides, adjacent-pair teleports, safe flips — all proven
maximum-preserving), and **(GR-118)(v)'s interval flips** at dip 2, which
reconnected the (GR-113) witness's 32 stranded maxima: the fourth move class
*Step G134* asked for is now known to exist at that pair. (v) **The four
(GR-116) witnesses are the adversarial control** — pure pos + neg with **no
balance-valid member**, and the clause nevertheless HOLDS at each (every
maximum there is half-resident). They are exactly the pairs where the clause
is tight and the refuted (GR-108) is false: a proof must be one they do not
kill, and a refutation must beat them. `w4/gxesc.py --verify` prints them in
full; `--hunt` is the landed hunt cell.

**What counts as a HIT.** A **proof of the half-witness clause** — state the
exact quantifier delivered: which maximum is exhibited, what selects it, and
any hypotheses carried beyond `O ⊆ M` + cubic loop-free + `M` perfect +
`2k = 2`. **Or a proof of the gap-2 law by any other route**, which counts
identically and is strictly better: the law is the actual target and the
clause is one *sufficient* hypothesis for it, not a necessary one — do not
force the argument through the clause if a direct route appears. Also valued,
on the (GR-116) precedent: a **refutation by witness**, i.e. an all-(2,2)
pair. If you find one, report **immediately and separately** whether its gap
is **2** (the clause dies, the gap-2 law survives and needs a new route) or
**4** — a gap-4 pair **refutes (GR-104)(i) itself at `2k = 2`**, moves (b′)'s
constant, and is a coordinator-surfacing event, so state it as the headline
and do not bury it in a summary. Or a **proof under a restricted quantifier or
an extended move class with the exact boundary named** (an `n` bound, a
residency hypothesis, a fourth move class). State which you got.

**Bars.** Do **not** attack (GR-C1) or the `2k ∈ {4, 6}` `O ⊄ M` corner —
separate residuals. (GR-105)–(GR-118) are **landed** — consume, do not
re-derive; the (GR-116) witnesses' figures are cap-free at those pairs — do
not try to repair or re-derive them. Do **not** re-run GPRICE's 1 431-pair
sweep, GBLAW's 1 099-pair escape census, or GXESC's 248-pair hunt / 1 100-pair
closure census — cite them; a *new* driver mode that tests a *new* sentence is
fine, a re-measurement of a landed figure is not. (GR-15) and class uniformity
are out of scope. No `.lean` is touched (the standing Lean hold).

**Riders, verbatim from GXESC's.** TERMINATION check E1/E2/E3 at the return
(E3 is ARMED by GBAL — firing is the coordinator's action; report, never
fire). Cap disclosure: an exhausted cap is *"not found under cap C"*, never
nonexistence. F11: every headline claim needs a driver that tests **that
sentence**, and "exhaustive"/"forced"/"the only" are their own claim class.
The shift-metric layer is UNBOUNDED ((GR-43)) — any bound is on a
**difference**. All figures exact ℚ, seeded, degeneracy-guarded, imported from
the canonical layer (`notes/scripts/README.md` binds; the *Divergences* table
names the same-name-different-semantics traps) — **the balance layer is
`w4/gridbal_common`**: import the moved devices from there directly, never via
the sibling re-exports. The `gprice`, `gblaw` and `gxesc` device sets are
sibling leaves — a sideways import is in policy but trips §2 rule 2's
recorded-debt rule: **extend the existing GBLAW/GXESC *Harness debt* item's
consumer list in your draft** (the coordinator records it), do NOT make any
move.

**Driver — conditional, at the pinned path `notes/scripts/w4/ghwit.py`.** A
purely derivational proof consuming only landed figures needs no new driver —
then state that disposition explicitly in the draft. Any new measured or
exhaustion claim mints the driver at the pinned path, importing the harness
read-only, left untracked for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GHWIT"): §(K-grid) **extends** — no new section; labels
**(GR-120)–(GR-124)**, **Steps G140–G144**; owning section stays
authoritative; return any unconsumed remainder to the tail.

### GHWIT — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: REFUTATION BY WITNESS — the spec's named refutation shape, and it
reaches one clause further than the spec's headline case.** The spec asked
for the half-witness clause and flagged an all-(2,2) **gap-4** pair as the
coordinator-surfacing outcome. GHWIT found exactly that.

**The witness.** `refut20`: a **habitat-gated** (`cflank.cubic_habitat`)
single-`F`-cycle `O ⊆ M`, `2k = 2` pair at `n_hub = 20` — even chords
`{15,6} {13,1} {17,11} {18,16} {7,2} {5,3} {9,4} {0,8}`, odd chords
`γ₁={10,14}`, `γ₂={12,19}`, `ℓ = 4` on `F`-branches `(3,4)`/`(16,17)`,
`ℓ = 3` on both odd chords, `ℓ = 2` elsewhere. `M* = 16`; maximum family
`64 = 32 pos + 32 neg + 0 bal`, **every member residency (2,2)**,
`min|h| = 4`; `f = {AA:4, AB:8, BA:8, BB:4}`, so `d_par = 4`, `d_adm = 8`,
**gap 4**. By (GR-117)(i)'s *proven* equivalence the price form falls with
the law — this is not a fresh price computation. Not isolated: 12 all-(2,2)
pairs at `n = 20`, 8 habitat-gated, 3 at gap 4; and a second pinned gated
all-(2,2) pair `clause20` at gap **2** separates the clause failure from the
law failure — **both occur**.

**Second, independent finding — a landed figure corrected.** (GR-108) is
FALSE from **`n = 12`**, not `n = 16`: three habitat-gated single-cycle
`n = 12` witnesses, with `n ≤ 10` exhaustively enumerated over every
`F`-cycle type and chord diagram and no habitat-realizable gap-2 instance.
So **12 is exact**, and (GR-116)(iv)'s boundary sentence plus its "third
localization boundary" gloss are superseded in place. GXESC's caps
disclosure was correct — only the inference from it failed, which is the
disclosure discipline working as designed.

**Proven, new and unconditional.** (GR-120), the **(2,2) budget**: at any
`O ⊆ M` pair, any `2k`, any number of `F`-cycles, a forcing maximum with
residency (2,2) forces `h_k = h_s + 4`, `e_f + 2h_s + f_0 = n/2 − 6` and
`dist = 2h_s + 4 + 2f_0`, hence `n ≥ 12` and `d_par ≥ 4` — so **the clause,
the gap-2 law and (GR-104)(i) at `2k = 2` are theorems at every `n ≤ 10` and
at every pair with `d_par(M) ≤ 2`**. (GR-121), the **slide gate**, is proven
as a criterion and **refuted as a route** (20/40).

**The coordinator's own shaping block was refuted.** The dispatch asserted
that the clause reduces to *"some maximum has `|h| = 2`"*. False: the landed
witness `rand20b` is pos-carrying with `min|h| = 3` across its whole family.
The correct reduction is `|h| ≤ 3`, and `refut20` defeats even that. This is
the **second** instance in the phase of a coordinator-authored prediction
refuted by the direction it primed (`RESEARCH-ARC.md` lists that as a
watched candidate, not yet a rule) — logged at `notes/dispatch-log.md`.

**Verification the coordinator re-ran.** `--validate` re-run in full: exit 0,
ALL LEGS OK, 337 s, every headline figure reproduced. **One defect was caught
and returned before landing:** the draft claimed *four* independent exact
models and pinned a `max|R|` quadruple, but the shipped driver implemented
three (its own docstring said so) and nothing in the tree produced that
figure — an attestation with no evidence, tripping F11 and the harness's hard
"every script the project runs is committed" rule. The continuation landed
the fourth model (`naive_family`, self-contained, no project device)
**asserting** `M*`, family size, the whole `f`-table, the gap and the
all-(2,2) verdict at all five pinned witnesses, and tested byte-stability by
a measured two-run diff (16 lines, all `[Ns]` wall-clock). Re-verified by the
coordinator at `--verify`.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E1: no
flank opened or closed; the pass is rank-free. E2: the target is **settled**,
negatively, with a named successor. E3: **stays ARMED by GBAL, not fired** —
nothing here touches (a′), `d_fg` or input (Y); no rank is computed anywhere.
**(GR-15) does not move; `hK` is untouched.**

**Successors, in order.** (1) What replaces the constant 2 in (b′): the
ceiling **4** is proven ((GR-86)) and now *attained*, so whether the ledger's
downstream consumers run at 4 is a **ledger-side routing call**. (2) The
**untested `min_M` reading** — at `refut20`'s shape 25 of 26 matchings have
`O ⊄ M` and satisfy (GR-104)(i) outright by (GR-107)(iii); (GR-59) is the
precedent that `min_M` can be load-bearing. (3) The exact `n` of the first
clause failure: 16, 18 or 20 (20 exhibited; 16/18 clean under disclosed caps).

## GMINM — thirty-seventh ordinal, the forty-fifth direction (single dispatch, prepped 2026-08-26)

**Selection provenance:** the **2026-08-26 widened delegation** — the user
put the *pick* itself, not merely its shape, in the coordinator's hands for
the rest of the session, with two stated criteria: explore different paths
rather than getting bogged down, and prefer examples that could kill whole
directions or counterexample the target (`notes/Pencil-adjudications.md`,
the seventh check-in's second bullet, quoted verbatim there). **This is a
coordinator pick; the twelfth's disclosure applies — no independent top-rung
ranking of the alternatives.** Dispatched **un-named, single**, at
**`recon-opus`** (fable conserved; `weekly_scoped` critical).

**Why this and not a fresh section — stated honestly, because it is the
fifth consecutive §(K-grid) direction.** It is picked *against* the
diversity criterion on purpose and for one reason: GHWIT's landed headline
— *"per-matching (b′) at the constant 2 is FALSE"* — has an **unmeasured
escape hatch**, and until it is closed we do not know whether the arc just
killed the constant or only one reading of it. (GR-59) is the standing
precedent that this is a real hatch, not a quibble: the per-matching variant
of **(a′)** was refuted exactly this way and `min_M` turned out to be
load-bearing. So this is a **correctness check on our own just-landed
claim**, cheap and decisive, not another attempt to prove the thing GHWIT
buried. It is bounded to one dispatch; the next pick goes off §(K-grid).

**The target — two questions, both required.**

**(Q1) Does the `min_M` reading survive?** At `2k = 2`, is
`min_M (d_adm(M) − d_par(M)) ≤ 2` true at the habitat shapes where the
per-matching form is refuted — starting with `refut20` and the other 11
all-(2,2) pairs GHWIT's `--build` found at `n = 20` (8 habitat-gated, 3 at
gap 4; `ghwit.py --build`)? At `refut20`'s shape the arithmetic is already
suggestive and **must be checked, not assumed**: 26 perfect matchings, of
which exactly **one** has `O ⊆ M` (the witness), the other 25 having
`O ⊄ M` and satisfying (GR-104)(i) outright by (GR-107)(iii). If that
pattern is general, `min_M` survives and GHWIT's kill is confined to the
per-matching reading. **The refutation shape is the valuable one:** a
habitat shape where **every** matching prices `≥ 4` kills (b′)'s constant at
*every* reading — that is a strictly bigger kill than GHWIT's and is the
outcome to hunt hardest.

**(Q2) Which reading does the ledger actually consume?** GHWIT called this
"a ledger-side routing call, the coordinator's" — it is being routed here,
because it is a question about landed statements and not a preference. Read
(b′)'s **downstream consumers** and report, with the decl/step pointers,
whether they need the per-matching form, the `min_M` form, or the constant
only. If they run on `min_M`, GHWIT refuted a statement the ledger never
used, and that must be said plainly. If they need per-matching, then
whether they can be re-routed at the **proven** constant **4** ((GR-86),
now *attained* by (GR-122)) is the live question — answer it if the reading
is cheap, and say so if it is not.

**The named inputs (landed; consume, do not re-derive).** (GR-122) and
`refut20` with its 11 siblings (`ghwit.py --build`/`--verify`); (GR-120)'s
budget, which already makes the price form a theorem at `n ≤ 10` and
wherever `d_par(M) ≤ 2` — so **any `min_M` counterexample lives at `n ≥ 12`
with every matching at `d_par ≥ 4`**, a sharp confinement to hunt inside;
(GR-107)(iii)'s proven off-`M` half, the reason the 25 other matchings are
free; (GR-59), the precedent and the shape of the answer; (GR-86)'s cap.
`gprice.pairs_of` and `perfect_matchings` enumerate the matchings.

**What counts as a HIT.** Either answer to Q1, stated with its exact
quantifier — a proof or a broad measurement that `min_M ≤ 2` survives (say
over what population, with caps disclosed), or **a shape where every
matching prices `≥ 4`**, which is the bigger kill and a
coordinator-surfacing headline. Q2 answered with pointers is required
either way and is **not** optional colour.

**Bars.** Do **not** re-open the per-matching form — it is refuted, that is
settled. Do not attack (GR-C1) or the `2k ∈ {4, 6}` `O ⊄ M` corner. Do not
re-run GHWIT's `--exh` or `--build`, GPRICE's 1 431-pair sweep, GBLAW's
1 099-pair census or GXESC's 248-pair hunt — cite them; a *new* mode testing
a *new* sentence is fine. (GR-15) and class uniformity are out of scope. No
`.lean` (the standing Lean hold).

**Riders, verbatim from GHWIT's.** TERMINATION check E1/E2/E3 at the return
(E3 ARMED by GBAL — report, never fire). Cap disclosure: an exhausted cap is
*"not found under cap C"*, never nonexistence. F11: every headline claim
needs a driver testing **that sentence**; "exhaustive"/"forced"/"the only"
are their own claim class. **F25, new and aimed straight at this dispatch:**
the sentence describing your *verification bar* is itself a headline claim —
write "N independent models" and any figure you pin by **re-reading the
shipped driver**, never from memory of the session; a scratchpad probe that
is not in the driver does not count toward the bar. All figures exact ℚ,
seeded, degeneracy-guarded; the balance layer is `w4/gridbal_common`,
imported directly, never via sibling re-exports. `gprice`/`gxesc`/`ghwit`
are sibling leaves — sideways imports are in policy but trip §2 rule 2:
extend the existing *Harness debt* item's consumer list in your draft (the
coordinator records it), make no move.

**Driver — conditional, at the pinned path `notes/scripts/w4/gminm.py`.** A
purely derivational answer consuming only landed figures needs no new
driver; state that disposition explicitly. Any new measured or exhaustion
claim mints the driver at the pinned path, read-only imports, left untracked
for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
GMINM"): §(K-grid) **extends**; labels **(GR-125)–(GR-129)**, **Steps
G145–G149**; return any unconsumed remainder to the tail.

### GMINM — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: not the outcome the spec ranked first, and a more consequential
one.** The spec told GMINM to hunt hardest for a shape pricing `≥ 4` at every
matching. That shape **cannot exist** at `2k = 2` — proven, not merely unfound
— and the routing question the spec attached as (Q2) turned out to carry the
finding.

**(Q1) The `min_M` reading is a THEOREM** ((GR-126)). Two landed pieces
compose: (GR-107)(iii)'s off-`M` half has a **vacuous hypothesis at
`2k = 2`** (imbalance is `2 − 2·#B ∈ {2,0,−2}`, so `|δ| ≤ 2` holds at every
configuration and the (GR-C1) hedge never binds), and (GR-94)(iv) already
supplies a perfect matching avoiding any two prescribed branches at every
habitat (Plesník 1972). So `min_M (d_adm − d_par) ≤ 2` everywhere, and the
hunted stronger kill is impossible.

**(Q2) The ledger consumes neither reading the arc has been arguing about**
((GR-127)). (b′)'s term is `d_adm(shape) − d_par(shape)` with **both ends
independent minima over matchings** — this is what `gdev.min_dev` computes,
its loop running `for nd` outer and `for mat` inner and fixing each layer at
the first `nd` any matching reaches. So the consumed statement is
**(L)** `min_M d_adm − min_M d_par ≤ 2`, not **(P)** `∀M` (GHWIT's, refuted)
and not **(m)** `min_M (d_adm − d_par)` (this spec's, now proven).
**(m) ⇏ (L) and (L) ⇏ (m).**

**The separation needs no new measurement.** (GR-67)'s parity law proves every
*per-matching* gap EVEN; W3's landed record is `d_par = 2`, `d_adm = 3` — a
ledger gap of **1**, which no per-matching gap can be. And at (GR-122)'s own
witness shape the ledger gap is **0**: the matching that refuted per-matching
(b′) is not even `d_par`-optimal for its own shape.

**What this does to the previous four directions.** GPRICE, GBLAW, GXESC and
GHWIT all attacked (GR-104)(i) at `2k = 2` — reading **(P)**. The ledger runs
on **(L)**. Their *mechanism* theorems stand and are untouched; what is
re-priced is the target's relevance, and `notes/Pencil-strategy.md` §8's own
warning ("a residual-of-a-residual inside the (a′)/(b′) ledger [that] does not
touch a named `hK` gap") reads, in hindsight, as the signal it was.

**No status word moves.** (GR-104)(i) and per-matching (b′) stay REFUTED;
(GR-15), `hK` and class uniformity are untouched; E3 stays ARMED and does not
fire. **The live successor is a NEW statement: is the ledger gap ever `≥ 3`?**
— measured spectrum `{0, 1, 2}` at 4 935 shapes, and by (GR-127) no proof of
it may fix its anchor matching ((GR-59)'s moral, one notch further out).

**Verification the coordinator re-ran.** `--validate` in full: exit 0, ALL
LEGS OK, 353 s; the `(diagram gap, per-matching max, min_M, shape-level)`
census reproduces, including five pairs at diagram gap 4 with `min_M` gap 0
**and** ledger gap 0. Independently checked against the tree: `gdev.min_dev`'s
loop order and docstring (the (Q2) claim), (GR-67)'s "every per-matching layer
gap is EVEN", (GR-94)(iv)'s "Such an `M` exists at every habitat", and W3's
landed `d_adm = 3`.

**F25 compliance, unprompted and worth recording.** The return stated its own
bar by re-reading the shipped driver and **corrected the count downward**:
*"two models plus a landed-predicate certificate — not three models"*, noting
the certificate confirms achievability rather than optimality, so the `n = 20`
lower bounds rest on the model, cube-validated at `n ≤ 12` only. That is
exactly the discipline F25 was minted for, one dispatch earlier.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed.

## OGEOM — thirty-eighth ordinal, the forty-sixth direction (single dispatch, prepped 2026-08-26)

**Selection provenance:** the **2026-08-26 widened delegation** — the pick is
the coordinator's, under the user's two stated criteria (explore different
paths; prefer examples that could kill whole directions or counterexample the
target). **The twelfth's disclosure applies — no independent top-rung ranking
of the alternatives.** Dispatched **un-named, single**, at **`recon-opus`**
(fable conserved).

**Why this, and why now.** It is `notes/Pencil-strategy.md` §8.5's one **open**
row, in the section whose own header calls it *"the move this board's own risk
analysis recommends before more `hK` spend"*. It is the first direction off
§(K-grid) in six, and GMINM has just shown what that concentration cost: five
directions attacked reading **(P)** of (b′) while the ledger consumes **(L)**
((GR-127)). This dispatch attacks a **carried kernel's own truth**, not a
ledger residual.

**The target — is there a class shape where `hK` is FALSE?** Concretely: a
class (shape, split) at which **`{σ = 0} = ∅`**, i.e. *every* chart point of
`H = G − v − a` carries a self-stress, so `H`'s rows are nowhere independent
and (a₂) fails. By **(OC-24)** that makes **`hK` FALSE at that shape** — a
**PENCIL event**, not a (K-tight) one.

**What is already settled, and must not be re-run.** The **counting** route to
this disproof is **DEAD**: **(OC-37)** proves `slack(F) ≥ 0` at every class
shape with equality iff `F` is a cycle or bouquet, so **no `H`-supported
stress in the habitat is combinatorially forced** (2 614 shapes, 215 906
supports, no cap, `slack < 0` zero times). Direction **SIGZ** ran the
authorized `σ > 0`-everywhere hunt on that mechanism and returned **NO HIT**.
Cite both; re-running either is out of scope. What (OC-37) left standing, and
your whole target, is the **geometric** half: *no forced chain-span drop and
no forced Kirchhoff drop* — **measured free but open class-uniformly**,
**one-point decidable per shape**, and in **(OC-8)'s own object class**.

**The confinements handed to you, all landed.** (i) **(OC-39)** carries an
exact-ℚ **full-row-rank certificate at 3 368/3 368** class (shape, split)
pairs over the **exhaustive `K4` stratum** — per-pair *proofs*, not a sample —
so **a counterexample cannot live there**; start outside it and say where you
looked. (ii) **The only known failure mechanism** is a self-stress of a short
**theta sub-multigraph** inside `H` (§(K-flank) *F5(d)*'s support), with
(OC-37)'s tight corollary `Σ min(ℓᵢ, 6) ≥ 13` bounding when a theta can carry
one at all. (iii) **(OC-38)** is the cautionary instance: `P21` is
`hnoRigid`-FALSE and **one unit short** of what the class needs, and its five
σ-jump seeds are **exactly** the five where `localtest.plane_basis`
degenerates — a *set equality*, so the arc's only exhibited near-instance sits
on the **(OC-7) coincidence locus** and is an artifact, not a witness. Any
candidate you find must be checked against `repin.star_generic` before it is
called a hit. (iv) **(OC-35)/(OC-36)** give the mechanism language: a stress
is a **Kirchhoff flow on topological paths** valued in the chain-span perps,
and `corank R(F) = Σδ_Q + ρ_F − slack(F)`.

**What counts as a HIT — both directions are valuable, state which you got.**

1. **A disproof witness:** a class (shape, split), off the `K4` stratum,
   with `{σ = 0} = ∅` — every chart point stressed — surviving the (OC-38)
   coincidence check. **This makes `hK` FALSE there.** Report it **separately
   and first**, with the shape, the split, the mechanism, and the exact
   arithmetic. **The direction-A pivot rule is in force** for what it *means*
   — but note the stop clause was **superseded 2026-08-26**: the coordinator
   works a confirmed hit up toward formalization rather than halting, and what
   goes to the user is the **classification** (does `PencilPair K 3 G` itself
   fail, or only the `hK` pin?) and the confirming pass. So: **state your
   classification explicitly** and do not overstate confidence on a single
   witness.
2. **A class-uniform proof that the geometric half is free** — that no chain-
   span or Kirchhoff drop is ever forced. That delivers (a₂)'s necessary half
   class-uniformly and **closes the last known route to a disproof**, which is
   itself decision-relevant: it says stop hunting counterexamples and commit
   to proving.
3. **An honest MISS with the route priced** — where the hunt reached, what
   mechanism would be needed, and whether §8.5's row should stay open. **Cap
   disclosure is mandatory:** *"not found under cap C"*, never nonexistence.

**Bars.** Do **not** re-run (OC-37), SIGZ's hunt, or the (OC-39) `K4`
certificates. Do **not** attack (OC-8), input (a)'s target-rank half (a₁), or
(GR-15) — separate residuals. Class uniformity of the *escape* is out of
scope. Do not touch §(K-grid)'s (b′) ledger at all — (P) is refuted, (m) is
proven, (L) is the live one and is **not** this dispatch's business. No
`.lean` (the standing Lean hold).

**Riders.** TERMINATION check E1/E2/E3 at the return (E3 ARMED by GBAL —
report, never fire). F11: every headline claim needs a driver testing **that
sentence**; "exhaustive"/"forced"/"the only" are their own claim class.
**F25:** state your verification bar by **re-reading the shipped driver** —
write "N independent models" and any pinned figure from the deliverable,
never from memory of the session; a scratchpad probe that is not in the
driver does not count. Every script you run is committed. All figures exact ℚ
(or exact `ℚ(i)` via `exactcore.Gauss`, now a base-layer primitive), seeded,
degeneracy-guarded; `notes/scripts/README.md` binds and its *Divergences*
table names the same-name-different-semantics traps. Sideways imports are in
policy but trip §2 rule 2 — record them in your draft, make no move.

**Driver — conditional, at the pinned path `notes/scripts/w4/ogeom.py`.** A
purely derivational result consuming only landed figures needs no new driver;
state that disposition explicitly. Any new measured or exhaustion claim mints
the driver at the pinned path, read-only imports, left untracked for the
coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
OGEOM"): §(K-out) **extends**; labels **(OC-45)–(OC-49)**, **Steps O42–O46**;
return any unconsumed remainder to the tail.

### OGEOM — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: NO disproof witness — a HIT of the spec's type 2, restricted.**
The geometric half of the disproof question is now free **by an argument**,
class-uniformly in the ambient shape, on a named finite frontier. §8.5's row
narrows sharply and stays open.

**No witness, and the classification question does not arise.** 91 260 live
cores searched, **0** with `corank > 0` at every gated draw. The dispatch
correctly declined to classify (`PencilPair` vs the `hK` pin) on the strength
of nothing found — the right call, and the KBARE-FALSIFY precedent is why the
spec asked for the classification in the first place.

**Three results, each with its witness.** **(OC-46)** — `H = G − v − a` is a
*vertex deletion*, hence **induced**, so `G`'s chart surjects onto `H`'s and
**`σ` depends on `H` alone; the ambient class shape drops out**. The only
failure mode of the extension construction is a chord, which an induced
subgraph cannot have (1 482 + 222 extensions, 0 failures). **(OC-47)** — a
topological path of length `≥ 6` has full chain span, so its flow variable
vanishes and the path is **dead**; iterating gives the live core. Since
**girth `≥ 7`** is forced at a class shape (a cycle of length `≤ 6` would be
rigid, contradicting `hnoRigid` — coordinator-verified against
`notes/Pencil-informal-grid.md`), **every cycle and every bouquet is dead** —
so **(OC-37)(ii)'s `slack = 0` mechanism, the only topology at which one
geometric unit suffices, is gone class-uniformly, by argument rather than
enumeration.** **(OC-48)/(OC-49)** — the exhaustive iso-reduced hunt, and the
census: `{σ = 0} ≠ ∅` at **275 342** class (shape, split) pairs over 63 013
shapes **by theorem**, the chain run end-to-end 222 times with all four
`IsNondegPencilRealization` conjuncts green.

**(OC-45), the adversarial check that passed — and it upgrades a landed
result.** Every class-shape branch has `ℓ ≤ 5` and `G°` is bridgeless, so
`sigz.k4_stratum`'s `{1..5}^6` is a **theorem, not a cap** (re-enumerated at
`{1..12}^6`: 877 = 877). Consequently **(OC-39) is upgraded, not corrected** —
its 3 368 per-pair certificates become consequences of an argument. Nothing
landed is contradicted by this pass.

**What it does NOT do, stated because the negative is an emptiness claim.**
Unsearched cells: `n(F°) = 4` at `|E°| ≥ 9`, `n(F°) = 5` at `|E°| ≥ 9`, and
**every `n(F°) ≥ 6`** — the budget bounds `|E(F°)|` but not `n(F°)`. Below
`n(F°) ≤ 5` that is a *compute* frontier (`--huntn` takes a cell range and
slice index); above it, an *ideas* frontier. Seed cap 8 gated draws per core;
census cap `|V°| ≤ 5`, `|E°| ≤ 9`; cross-check cap 250 pairs. **The headline
is "not found under these caps", never nonexistence** — and the driver prints
that boundary itself, before any number.

**The residual is now one shape-free sentence** — *at every live core, the
Kirchhoff map `⊕_Q S_Q^⊥ → (K⁶)^nodes` is injective at the generic chart
point.* Not a counting statement, not shape-indexed. The first time the
geometric half has been a single sentence.

**(OC-38) independently reproduced**, which is worth recording: `P21`'s
`(3,3,6)` theta has an **empty** live core, so generic `σ = 0` — matching
(OC-38)(iv)'s 360/360 — and its `Σd = 3` overflows the core budget 2, which
**re-derives "one unit short" as a budget statement** rather than a
measurement.

**Verification the coordinator re-ran.** Both invocations of the disclosed
two-call split: `--bound --dom --core --cert` (exit 0, 288 s) and `--hunt`
(exit 0, 357 s); the 21 086/0, 271 974/271 974, 3 324 + 44 = 3 368 and 250/250
figures all reproduce. The **girth `≥ 7`** premise — load-bearing for
(OC-47)(i)'s class-uniform claim and *cited* rather than asserted by the
driver — was checked independently against the workbook and holds.

**F25 bar, read off the shipped driver:** **three independent
double-implementations**, each machine-asserted — corank by direct
`5|E|×6|V|` matrix *and* by the (OC-35) flow system; the class predicate by
oracle *and* by counting; the (Λ4)(iii) filter by vertex-set pruning *and* by
brute force over all `2^m` subsets. Nothing quoted from a scratchpad probe.

**Harness:** thirteen read-only imports, all §1 primitives or catalogued layer
devices — the arc's widest fan-in, and **no new sibling-import debt**.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 stays
**ARMED by GBAL, not fired**: the target is not proven.

## BATTAIN — thirty-ninth ordinal, the forty-seventh direction (single dispatch, prepped 2026-08-26)

**Selection provenance:** the **2026-08-26 widened delegation** — a
coordinator pick, so the twelfth's disclosure applies (no independent
top-rung ranking of the alternatives). Dispatched **un-named, single**, at
**`recon-opus`** (fable conserved).

**Why this pick, and it is the starkest fact on the board.** Forty-six
directions have attacked `hK`. **Zero** have attacked `hbareSplit** — the gap
map's own words are *"open, nothing being developed"*, and
`notes/Phase39.md` has flagged the imbalance as **dispatch attention, not
adjudication** since 2026-07-30. It is also the pick GMINM's lesson argues
for: `hbareSplit` is a kernel **carried by the landed theorem**
(`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`), not a
residual-of-a-residual, and the arc has just spent five directions
discovering that a ledger residual was misaimed.

**The target — the seed-free direct-attainment shape** (strategy §8.4's
(K-bare) development row, **rank 3** on the 2026-08-25 re-rank; the
KBARE-FALSIFY probe's own suggestion). **Bypass the antecedent**: instead of
repairing route A's refuted fixed-seed insertion, attack
**`HasPencilRealization K 3 G` directly on the habitat**. It is strictly
stronger than the `∃`-seed form, and **seed-free**, which is the point — the
probe's finding was that the antecedent supplies an object route A cannot
use.

**What is settled, and must not be re-litigated.** **(K-bare-ext) is REFUTED
as stated** (KBARE-FALSIFY, 2026-08-20, *Steps BE1–BE8*) — exactly and
cap-free — but **`hbareSplit` itself is UNTOUCHED and still carried as
pinned**: its consequent is an `∃` over frameworks and every probed gadget
attains, so what died is route A's `∀`-over-seeds shape, not the kernel.
**Option B (the insertion calculus) is NOT commissioned** (2026-07-30
adjudication, standing) — do not drift into it, do not cost it, do not
propose it as the route. It needs the owed KT pp. 684–691 re-pin first and
was built for chart-generic seeds.

**Two enablers make this newly affordable** (both landed, both from the
probes): the §(K-tight) **boundary-load calculus transports** (192/192), and
the **dependent stratum is complete** at `corank(G′) ≤ 3`. Note the honest
difficulty statement from the gap map, which you should test rather than
assume: versus `hK`, (K-bare) is *easier on uniformity, harder on the seed
side*, and the habitat reaches **corank 2** (DZ), so `¬PencilNondegFeasible`
buys **no corank control** — the chart/reseed/engine apparatus has nothing to
consume on either side of the split, leaving only the 2–3-dimensional `pt(v)`
placement freedom.

**What counts as a HIT — three shapes, state which you got.**

1. **Direct attainment, proven or reduced** — `HasPencilRealization K 3 G` on
   the habitat, or a reduction of it to a named finite/decidable residual
   with the exact quantifier stated. A first slice here is legitimately
   **exploratory** (the board ranks it third precisely because it has no
   named one-step residue), so a well-posed decomposition with the hard step
   isolated is a real result — but say plainly which step is hard.
2. **A falsification arm, and this is the one to report first if it fires.**
   Is there a habitat `G` at which `HasPencilRealization K 3 G` **FAILS**?
   That is a **T2** witness in the probe's tiering, and it makes
   **`PencilPair K 3 G` itself false** — a **PENCIL event**, the phase's
   target motive rather than the induction reaching it. The standing reading
   is that T2 is *"a universal non-existence over frameworks"* and **not
   producible by this harness**. **Test that reading rather than inheriting
   it:** say precisely what a T2 witness would have to exhibit, and whether
   any available tool decides it — noting that `notes/Pencil-strategy.md`
   §5.3 measures whole-graph symbolic work as hopeless (the ungauged
   28-coordinate degree-52 expansion dies at 600 s; a `|V| = 31` shape
   carries ~120 coordinates) and that the symbolic route *"stops exactly
   where the far graph enters"*. **A precise, well-grounded "still
   undecidable by this harness, and here is exactly why"** closes a standing
   question and is a perfectly good outcome — better than a vague hope.
3. **An honest OPEN with the route priced** — what the seed-free shape needs
   that the arc does not have, and whether it is cheaper or dearer than the
   `∃`-seed + deformation-repair alternative.

**Bars.** **Option B stays un-commissioned** — hard bar. Do not re-run
KBARE-FALSIFY's hunt or re-derive its figures; cite them. Do not attack
`hK`, (GR-15), class uniformity, or §(K-grid)'s (b′) ledger — all separate.
Do not touch W4 / `hcontract` (parked by the Lean hold). No `.lean` — the
standing Lean hold.

**Riders.** TERMINATION check E1/E2/E3 at the return (E3 ARMED by GBAL —
report, never fire). **The direction-A pivot rule applies to shape 2**: its
stop clause was superseded 2026-08-26 (a confirmed hit is worked up in-phase,
not halted), but the **classification** is required and is the user's — state
explicitly whether what you have refutes `PencilPair K 3 G` itself or only a
route, and do not overstate a single witness. F11: every headline claim needs
a driver testing **that sentence**. **F25:** state your verification bar by
re-reading the shipped driver; a scratchpad probe that is not in the driver
does not count, and every script you run is committed. Cap disclosure
mandatory. All figures exact ℚ (or exact `ℚ(i)` via `exactcore.Gauss`),
seeded, degeneracy-guarded; `notes/scripts/README.md` binds, and the `kbare/`
sibling-import set is **recorded UNPAID debt** — extend its consumer list in
your draft, make no move.

**Driver — conditional, at the pinned path `notes/scripts/w4/battain.py`.**
A purely derivational result needs no new driver; state that disposition
explicitly. Any new measured or exhaustion claim mints the driver at the
pinned path, read-only imports, left untracked for the coordinator to gate
and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BATTAIN"): §(K-bare-ext) **extends**; labels **(BE-10)–(BE-14)**, **Steps
BE9–BE13**; return any unconsumed remainder to the tail.

### BATTAIN — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: HIT shapes 1 and 2, both graded. `hbareSplit` OPEN and unchanged,
and the classification is explicit — it refutes neither `PencilPair K 3 G`
nor `hbareSplit`, only a *reading* and a *route pricing*. Not a PENCIL
event.**

**Four results.** **(BE-10)** characterizes the motive exactly, **derived off
the Lean bodies** as the spec required: `∃F, HasPencilPanelRealization G F n p
⟺ n_v ≠ 0 ∧ p_v ≠ 0 ∧ n_w ⬝ᵥ p_v = 0` for every `w ∈ closedNbhd(v)`, the
`W_e` clause free. Cross-asserted against `kbare_common.build_rigidity` at
equal exact rank 114. **(BE-11)** — **bare pencil realizability is
UNCONDITIONAL** (all normals in a common 3-space, all points at its perp:
legal at *every* graph), so `HasPencilRealization` has **no existence
content** — all of it is the rank. That is *why* the antecedent supplies an
object route A cannot use, a fact the arc had recorded but never explained.
**(BE-12)** — the pencil condition is carried entirely by the hubs, one
determinant each, vacuous at degree ≤ 2; the arc's "only known certificate"
(`|closedHubNbhd(v)| ≥ 4 ⟹ ¬PencilNondegFeasible`) becomes a one-line
theorem. **(BE-13)** — **the first universal rank cap over a pencil stratum
produced by an argument**: `rank(cone) = 6(|V|−1) − def₂(G)` with `def₂` the
*planar* deficiency, exact at 68/68 (DZ `103 = 114 − 11`, predicted before
measured).

**The correction, and it is the valuable one.** **(BE-9)'s "no T2 is
producible by this harness" was too strong.** A universal cap *is* producible
by argument — (BE-13) is one, and it reduces T2 at a forced cone to the
**decidable** criterion `def₂ > def₃`. What actually blocks T2 is narrower and
structural: forcing the cone needs three shared closed-star normals, hence a
common neighbour of two adjacent bodies — a **triangle** — and the habitat is
**triangle-free by `hnoRigid`**. Coordinator-verified in the Lean source, not
a docstring: `Escape.lean:411–418`, via `Graph.triangle_isProperRigidSubgraph`.
(BE-9)'s subclass objection is confirmed **real but inert** — the affine class
is Zariski-dense in `Y°`, a tower of linear fibrations, hence irreducible and
rational.

**The falsification arm, answered positively and deterministically.** **774
shapes, 774 exact-ℚ attainment certificates, ZERO shortfalls** — the entire
216-member index-1 census (not a sample), DZ 114/114, Q3 138/138, a 545-shape
sweep over indices −6…12, and the necklaces. These are **proofs, not cap
reports**: `rank ≤ target` holds universally and the conclusion is
existential, so an exhibited certificate settles a shape. *Step BE7*'s "no T2
candidate found under cap" therefore upgrades to **774 shapes proven not to be
T2 witnesses**. A constructed T2 candidate — a necklace of `K₄−e` blobs — met
the arithmetic half but its own derived stratum attains at `k = 3…7`; the
criterion's two halves have never been met by one graph.

**A methodological trap caught by the dispatch itself, worth recording.** Its
first sweep pass reported three shortfalls from **one seed each**; rank is
lower semicontinuous, so a one-seed shortfall is only a lower bound. All three
attain on another seed. It found and corrected this before returning — the
mirror image of C3's `0/179`.

**What remains, and it is now one sentence.** **(BE-14)**, direct attainment —
*the pencil stratum attains `6(|V|−1) − def₃(G)`*, a **pencil analogue of the
Molecular Theorem** — is OPEN with its hard step isolated to **`Y° ⊄ Z(G)`**:
hub concurrency does not force the rank-drop locus, and nothing in the arc
bounds `Z(G)` (§(K-tight)'s calculus is split-local). **Pricing:** dearer in
absolute terms (whole-graph, no induction, new genericity mathematics),
**cheaper in structure** — seed-free, induction-free, never uses
`¬PencilNondegFeasible`, so it discharges `hbareSplit` **and** `PencilPair`'s
unconditional conjunct at once, as a **standalone theorem** — the phase's own
2026-08-05 bar. The `∃`-seed + repair alternative stays inside the induction
and still meets §(K-tight) *Step 5*'s chartless wall; **nothing this pass found
lowers that wall.**

**Smallest next slice, offered:** (BE-14) restricted to `def₂ = def₃`, where
the cone itself attains by (BE-13) — closed-form, no genericity argument, and
the arc's first `HasPencilRealization` result *proved* rather than measured.
It does **not** discharge `hbareSplit` (DZ has `def₂ = 11`); it is a
proof-of-concept.

**Coordinator verification.** `validate` re-run (exit 0, 72 s); the 68/68 cone
law, DZ `103` vs target `114`, the necklace attainments at `k = 3…7`, and the
774/0 record all reproduce. The triangle-free premise — load-bearing for the
corrected T2 reading — was checked against the Lean source itself.

**F25 bar, read off the shipped driver:** eleven modes, all foreground with
explicit timeouts, exact ℚ throughout, every rng seeded, asserts covering every
`HasPencilPanelRealization` conjunct. **No scratchpad probe backs any claim.**
Seven caps disclosed, including that degree-≥4 habitat members are **unprobed**
and `def₂` is exact only to `|V| ≤ 16`.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 stays
**ARMED by GBAL, not fired**.

## BZAVOID — fortieth ordinal, the forty-eighth direction (single dispatch, prepped 2026-08-26)

**Selection provenance: a USER OPTION SELECTION, not a coordinator pick** — the
2026-08-26 **ninth check-in**, where the BATTAIN landing's offered
slice-shape adjudication was put to the user as the next dispatch and the
answer was **"(BE-14) full statement — hbareSplit"**, over BATTAIN's own
offered `def₂ = def₃` proof-of-concept and over two non-(BE-14) alternatives.
The **option set** was coordinator-authored, so the twelfth's disclosure
applies to the *alternatives* (no independent top-rung ranking of them); the
**pick between them is the user's**. Dispatched **un-named, single**, at
**`recon-opus`** (fable conserved this session — the user left *"all four
rungs dispatchable"* unselected, `weekly_scoped` 92 % critical corroborating).

**This is the direction the phase's own target ranking puts first.** Under the
2026-08-26 eighth-check-in directive (*"prioritizing work that makes headway on
the phase target one way or the other"*), *Hand-off*'s candidate list is ordered
by distance to `PencilPair K 3 G`, and (BE-14) is its head: it discharges
**`hbareSplit`** *and* **`PencilPair`'s unconditional second conjunct** at once,
as a **standalone theorem**, without touching `hcontract` or `hK`. Nothing else
on the board does that.

**The target, and it is one sentence.** (BE-14) (§(K-bare-ext) *Step BE12*):

> *For every graph `G`, the pencil stratum of the panel-hinge realization space
> attains the body-hinge target `6(|V|−1) − def₃(G)`.*

Katoh–Tanigawa give the **panel-hinge** half; the pencil stratum adds
**concurrency**, one determinant per hub, cutting a subvariety of codimension
`Σ_{hubs}(deg v − 2)` out of `(P³*)^V`. **The hard step, isolated by BATTAIN
and the whole of this dispatch:** *the hub concurrency conditions do not force
the configuration into the rank-drop locus* — **`Y° ⊄ Z(G)`**, where `Z(G)` is
the locus whose complement KT's theorem certifies nonempty. Nothing in the arc
bounds `Z(G)`: §(K-tight)'s boundary-load calculus is **split-local** and does
not see the whole-graph locus, and the chart/reseed/engine apparatus is
unavailable by hypothesis.

**What is LANDED and must be CITED, not re-derived.** All four of BATTAIN's
results are in tree (*Steps BE9–BE13*, driver `notes/scripts/w4/battain.py`):
**(BE-10)** the exact motive characterization, derived off the Lean bodies;
**(BE-11)** bare pencil realizability is **UNCONDITIONAL**, so
`HasPencilRealization` has **no existence content — all of it is the rank**;
**(BE-12)** the pencil condition is carried entirely by the hubs, one
determinant each, vacuous at degree `≤ 2`, and `Y°`'s generic rank is
well-defined; **(BE-13)** the cone law `rank(cone) = 6(|V|−1) − def₂(G)` with
`def₂` the **planar** deficiency, exact at 68/68. Do not re-run BATTAIN's 774
certificates or re-measure its figures — **cite them**. (BE-13) is
**proven-informally**, not formally; if your argument leans on it, say which
step of its splitting argument you are leaning on.

**A coordinator reading of the geometry, offered to be TESTED and not
inherited** (F19: a coordinator-predicted obstruction is refuted about as often
as it holds, so the stratum its evidence comes from is named). (BE-11) hands
the arc a **uniform, graph-independent point of `Y`** — the cone — and (BE-13)
prices it exactly: it sits at `6(|V|−1) − def₂(G)`, hence **inside `Z(G)`
whenever `def₂(G) > def₃(G)`**, which is the generic situation (DZ:
`def₂ = 11 > 0 = def₃`). So the shape of the problem is *not* "find a point of
`Y°`" — it is **"deform off the canonical point"**, with a uniform starting
configuration already in hand and its exact rank defect known. Whether the
natural first move is a **dimension/transversality count** (codim `Z(G)` in the
panel stratum against `Σ_{hubs}(deg v − 2)`) or a **direct construction** is
yours to decide; the evidence behind this reading is (BE-11)/(BE-13) plus the
68/68 cone measurements, i.e. the *cone* stratum only, and it says nothing
about transversality.

**What counts as a HIT — three shapes, state which you got.**

1. **(BE-14) PROVEN, or reduced with the residual named and quantified.** A
   proof of `Y° ⊄ Z(G)` class-uniformly is the phase-target result. A
   *reduction* to a named finite/decidable/combinatorial residual, with the
   exact quantifier written out, is a real result — but say plainly what is
   left and over what class it is quantified.
2. **A falsification arm the arc has NOT run, and it is cheap — report it first
   if it fires.** (BE-14) as stated quantifies over **every graph `G`**, not
   only over the `hnoRigid` habitat. BATTAIN's own mechanism makes the
   refutation criterion **decidable**: a forced cone plus `def₂ > def₃` caps the
   rank below target. BATTAIN then argued no *habitat* member can force the cone
   because **forcing needs a triangle** (three shared closed-star normals ⇒ a
   common neighbour of two adjacent bodies) and the habitat is **triangle-free**
   by `hnoRigid` (coordinator-verified in the Lean source, `Escape.lean:411–418`,
   via `Graph.triangle_isProperRigidSubgraph`). **Off the habitat, triangles are
   legal.** So: **hunt a triangle-carrying `G` whose `Y` is forced to the cone
   with `def₂(G) > def₃(G)`.** Such a witness would refute **(BE-14) as stated
   for all `G`**, narrowing the true statement to the habitat — which leaves
   `hbareSplit` and `PencilPair` **untouched** and is therefore *not* a PENCIL
   event, but it does re-scope the theorem being aimed at, and it is the single
   cheapest decisive experiment this spec can name. State the classification
   explicitly either way.
3. **An honest OPEN with the route priced** — what `Y° ⊄ Z(G)` needs that the
   arc does not have, and whether the `∃`-seed + deformation-repair alternative
   (which still meets §(K-tight) *Step 5*'s chartless wall) has become cheaper
   or dearer relative to it.

**The declined partial is NOT the deliverable.** BATTAIN offered
**(BE-14) restricted to `def₂ = def₃`** — where the cone attains in closed form
by (BE-13), giving the arc's first *proved* `HasPencilRealization` result — and
the user **declined it in favour of the full statement**, on the ground that it
does not discharge `hbareSplit` (DZ has `def₂ = 11`). You may use the
restricted case as a **lemma, base case, or sanity check**; you may **not**
deliver it as the result and call the dispatch done. A return that reaches only
the restricted case is an **honest partial** — say so in those words, and price
the remaining distance.

**Bars.** **Option B (the insertion calculus) stays un-commissioned** (2026-07-30,
standing) — do not drift into it, cost it, or propose it as the route. Do not
attack `hK`, (GR-15), class uniformity of the escape, or §(K-grid)'s (a′)/(b′)
ledger — all separate items, and the ledger thread is **closed negatively**
(GHWIT/GMINM); in particular **do not re-open** per-matching (b′) or the `min_M`
reading. Do not touch W4 / `hcontract` (parked by the Lean hold). **No `.lean`**
— the standing 2026-08-05 Lean hold. Do not re-litigate (K-bare-ext)'s
refutation: it is a *route* finding, `hbareSplit` is untouched and still pinned.

**Riders.** TERMINATION check E1/E2/E3 at the return (**E3 ARMED by GBAL** —
report, never fire). **The direction-A pivot rule applies to shape 2**, with its
stop clause superseded 2026-08-26 (a confirmed hit is worked up in-phase, not
halted) but its **classification requirement intact and mandatory**: state
whether what you have refutes `PencilPair K 3 G` itself, refutes only
(BE-14)-for-all-`G`, or refutes only a route — and do not overstate a single
witness ("confirmed" is the (GR-83)/(GR-113) bar: every figure re-derived
through independent exact models). **F11:** every headline claim needs a driver
testing **that sentence**, and "forced" / "exhaustive" / "the only" are their
own claim class needing an *enumerating* driver. **F25:** state your
verification bar by re-reading the shipped driver; a scratchpad probe that is
not in the driver does not count, and **every script you run is committed**.
**Cap disclosure mandatory** — an exhausted search reports *"not found under cap
C"*, never *"does not exist"*, and the disclosure travels with the figure.
All figures exact ℚ (or exact `ℚ(i)` via `exactcore.Gauss`), seeded,
degeneracy-guarded; `notes/scripts/README.md` binds. The `kbare/` sibling-import
set is **recorded UNPAID debt** — extend its consumer list in your draft, make
no move.

**Driver — conditional, at the pinned path `notes/scripts/w4/bzavoid.py`.** A
purely derivational result needs no new driver; state that disposition
explicitly. Shape 2's hunt, if you run it, **does** need one. Read-only
imports; leave it untracked for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BZAVOID"): §(K-bare-ext) **extends**, no new section; labels
**(BE-15)–(BE-19)**, **Steps BE14–BE18**; return any unconsumed remainder to
the tail.

### BZAVOID — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: HIT shape 2, fired NEGATIVELY and BY AN ARGUMENT; shape 1 an honest
partial; shape 3 re-priced. Nothing is refuted — not `PencilPair K 3 G`, not
`hbareSplit`, not (BE-14)-for-all-`G`. Three ROUTE findings and one reduction.
Not a PENCIL event.**

**The falsification arm the spec commissioned is EMPTY BY AN ARGUMENT — and it
is empty for every graph, on and off the habitat.** The spec asked for a
triangle-carrying `G` with a forced cone and `def₂ > def₃`, reasoning that
triangles are legal off the `hnoRigid` habitat. **(BE-15)** shows the
criterion's two halves are logically incompatible. The direction first
**generalized** BATTAIN's cone criterion to a family of universal caps, one per
forced class partition `π(G)` (the vertex classes of the triangle-edge subgraph
`T(G)`), with deficiency `6(k−1) − 5c + Σ_i def₂(G[V_i])`; `k = 1` is (BE-13).
Then it proved **`Σ_i def₂(G[V_i]) = 0` always** — each class is connected and
triangle-covered, a triangle is isostatic in the planar body-pin count
(`3·3 − 2·3 = 3`), and two rigid units sharing a **body** (which is what sharing
a *vertex* means when vertices are bodies) are rigid together — so the cap's
deficiency is exactly `max(0, partitionDef₃(π(G)))`, **a value `def₃`'s own
maximand already takes**. The mechanism can only ever reproduce a bound the
target already accounts for. Exact, **cap-free**, and enumerated at
**375 719 + 27 474** graphs with zero exceptions.

**What that does to BATTAIN's reading is a STRENGTHENING, not a correction.**
*Step BE13* explained the empty arm by *"forcing needs a triangle, and the
habitat is triangle-free by `hnoRigid`"*, with a Lean-level citation. Sound, but
**not needed**: the arm was never inhabited anywhere, and the reason is an
identity rather than a property of the habitat. The `hnoRigid` appeal becomes a
special case. The superseded sentence in *Step BE13*'s own *what would change
this* block was repaired in the same commit (the RESEARCH-ARC §3 corollary — a
map correction is presumptively a prose correction too).

**The identification, and it changes how the residual should be worked.**
**(BE-16)**, read off the Lean bodies as the guard requires: `rigidityRows`
(`RigidityMatrix/Basic.lean:654`) and `hingeRowBlock` (`:435`, literally
`(span {supportExtensor e}).dualAnnihilator`) make the rank a function of the
**hinge lines alone**; on the pencil stratum the hinge of `uv` is the **join
`p_u ∨ p_v`**, so the framework **is** the molecular (hinge-concurrent)
framework at atom positions `p` — exactly the landed `molecularOfCentres`
construction, whose own body builds the hinge as the join of the endpoint
centres. The pencil condition dualizes to *every closed star of points is
coplanar*: the **all-trigonal-planar** molecule. Consequence that matters:
(BE-14) is **existential, not generic** — `rank ≤ target` is universal, so **one
witness per graph settles that graph**, and `Y° ⊄ Z(G)` is a strictly less
constructive phrasing of the same thing.

**Two routes CLOSED, one of them the most attractive on the board.**
**(BE-17)** — the landed Phases-24–26 `G²` molecule apparatus is **dead here**,
and not merely by hypothesis mismatch: `IsGeneralPositionPlacement`
(`GeneralPositionPlacement.lean:59`) demands every `≤ 4`-subset affinely
independent, which is the **literal negation** of the pencil condition at every
degree-3 hub, and the dictionary's *sufficient condition* for (BE-14) is
measured **FALSE in exact ℚ** at DZ / `spider(5,5,5)+c` / `theta(4,4,4)+c`
(`rank R(G²,p)` = 49/38/32 against generic 54/42/33; dictionary gaps **5/4/1**)
**while the molecular rank attains 114/90/72**. Mechanism: a coplanar `K₄` has
bar-joint rank 5, not 6. **(BE-16)(iv)** — the **coordinator's own offered
transversality/dimension count is structurally incapable** of settling
`Y° ⊄ Z(G)`: containment needs only `dim Y° ≤ dim Z`, satisfiable at every
graph with a hub (DZ: `54 ≤ 59`). The *other* half of that same coordinator
reading — "deform off the canonical point" — **survives and is now priced
exactly** at `def₂ − def₃`, with `def₂ ≥ def₃` proven at every connected graph.
So the reading was **SPLIT, not simply refuted**, on the YLOC precedent.

**One reduction banked.** **(BE-18)** — `def₃` is additive over a 1-vertex cut
(both directions proved, 907 gluings enumerated) and the panel-hinge rank is
`GL₄`-invariant, so pencil attainment **composes over 1-cuts** and **(BE-14)
reduces to 2-connected graphs**. The 2-cut extension is asserted "routine", not
proved — disclosed as cap 8.

**A free corollary worth naming, and it is NOT the declined partial.** At a
genuinely forced cone (`k = 1`) `def₂ = 0`, hence `def₃ = 0`, hence the cone
**attains in closed form** — so (BE-14) holds with no genericity argument for
every graph whose triangle-edge subgraph is spanning and connected (every `K_n`,
every triangular cactus). That is a **subclass** of BATTAIN's declined
`def₂ = def₃` slice, forcing both to `0`, so it is strictly less than what the
user declined and the direction says so plainly. **The declined partial is still
unclaimed.**

**Shape 1 — the honest partial, with the residual quantified.** (BE-14) is
**OPEN**: *for every 2-connected `G`, `∃ p : V → P³` with every closed star
coplanar and adjacent points distinct, at which the molecular body-hinge matrix
has rank `6(|V|−1) − def₃(G)`.* Priced as **the same size as after BATTAIN**,
two dead ends removed and the shape stated correctly; the `∃`-seed + repair
alternative is untouched and §(K-tight) *Step 5*'s chartless wall is not
lowered.

**Coordinator verification.** Full-figure re-run, not `validate` alone: `tri`
(**375 719 / 0**, 73 s, the `n = 7` tier `validate` deliberately skips), `crit`
(**27 474 exhaustive / 0 fire / 16 894 tight**), `cap` (`K4` reproducing
(BE-13); DZ triangle-free at `k = 20`, `c = 23`, cap deficiency `0`; necklaces
`k = 3…7` with cap deficiency `max(0, k−6)`), `pn` (rank **114 by both
carriers**), `flat` (`6` vs `5`; 6/6 hubs), `sq` (deficits **5/4/1**), `glue`
(**907**), `validate` (17 s). **All six Lean pins verified against the
definition BODIES**, not docstrings — `rigidityRows`, `hingeRowBlock`,
`IsGeneralPositionPlacement`, `molecularOfCentres`,
`molecular_finrank_motions_eq_square_ker` (whose `hgp` hypothesis is the gate
(BE-17)(i) turns on), `molecule_rank_formula`. **The load-bearing algebra was
re-derived independently by the coordinator:** `partitionDef₃(π) = 6(k−1) − 5c`;
`d ≥ q − 1` on a connected graph gives `partitionDef₂ ≥ partitionDef₃`
pointwise, hence `def₂ ≥ def₃`; `def₂ = 0 ⇒ def₃ = 0`; `def₂` monotone
decreasing in edges; triangle-covered + connected ⇒ triangle-intersection graph
connected ⇒ `def₂ = 0`; and `k = 1, c = 0` specializing to `6(|V|−1) − def₂(G)`.
**The apparent tension with DZ's `def₂ = 11` resolves correctly** and was
checked: DZ is triangle-free, so its cone is *available*, not *forced*
(`k = 20`), and (BE-13) prices a chosen configuration while (BE-15) prices a
forced one.

**F25 bar, read off the shipped driver:** eight modes, all foreground with
explicit timeouts, **exhaustive** enumerations backing every "always"/"never"
sentence (F11's own claim class), both deficiency oracles cross-checked at all
27 474 exhaustive entries, every rng seeded, and `sq` multi-seeded (6 draws, max
taken) against BATTAIN's own recorded one-seed trap. **The `G²` ranks are exact
ℚ deliberately** — the direction started them in GF(p) and corrected itself,
since a mod-`p` rank is a *lower* bound and therefore the wrong direction for a
shortfall claim. **Nine caps disclosed**, including that the exhaustive tiers
stop at `n = 7`/`n = 6`, that `sq`'s three shapes are all `def₃ = 0` and
degree-3-hubbed with `def₃ > 0` and degree-`≥ 4` hubs **unprobed**, that `Nk_3`
had no usable `Y` sample and is skipped, and — the one that matters most for
soundness — that **(BE-15)(ii)'s closure does NOT inherit (BE-13)'s
proven-informally status**, needing only `def₂(G[V_i]) = 0` and a definitional
inequality. **No scratchpad probe backs any claim.**

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 stays
**ARMED by GBAL, not fired**.

## ZSHEAR — forty-first ordinal, the forty-ninth direction (single dispatch, prepped 2026-08-26, **the side line**)

**Selection provenance: USER-INITIATED, unprompted free text** — 2026-08-26,
mid-turn: *"I'm also curious about whether the ideas inspired by Zheng's
body-pin project are worth pursuing. Perhaps we can look at that on the
side?"* This is the **first direction the §9 shelf has ever produced**, and
the first ever dispatched as an explicit **side line** concurrent with the
main pick. Dispatched **un-named**, concurrently with BZAVOID, at
**`recon-opus`** (fable conserved). Ordinal assigned: it attacks **class
uniformity**, the (K) crux, so unlike the two architecture-testing probes it
is **inside** the direction/ordinal count.

**Why this one of the six, and why the other five are barred.**
`notes/Pencil-strategy.md` §9.3's own cheapest-decisive-first order puts
**(ZH-1)** first, and it is the only one of the six that is a **yes/no question
with an adversarial bed already in tree**. (ZH-2) and (ZH-3) **owe a §2.5
counting-saturation filter check** and are held until it is done; (ZH-4) is
concrete but dearer; (ZH-5) is a design template for a future fan-out's
*selection*, not a result; (ZH-6) is **write-up material, never a dispatch**
(§9.3's own words).

**The candidate.** §9.1's finding is that the source's **Split–Klein form** is
**not an analogy but the same form** as §(K-pitch) *Step 0*'s pitch quadric
`Q(x) = ⟨x, ★x⟩`, with the same vanishing locus and the same meaning (zero
pitch = rotation about a line). (ZH-1) is the device: the orthogonal group of
`q` contains unipotent **shears** `Φ_S(ω,b) = (ω, b + Sω)` for `S` skew, which
fix **each generator individually** (not merely the ideal), because `ωᵀSω = 0`.
The uniformity argument built on it replaces *"exhibit a good seed"* with
*"avoid finitely many proper affine subspaces of `so₃(k)`"*, over any infinite
field — which is exactly `hK`'s hypothesis.

**What it would buy, if it survives.** (i) A **propagation mechanism the arc
does not have**: under a group fixing every generator, one witness certifies a
whole orbit, whereas today `P ≢ 0` is re-established per habitat. (ii) It
**dissolves rather than pays** the field-scope problem — route σ's polarity is
an `ℝ`-only construction aimed at an `hK` quantified at general `[Infinite K]`,
and generalizing it cost a whole section.

**The cheap decisive test, already specified in tree, and run it FIRST.**
§(K-flank) *Step F5(d)* exhibits **five legal nondegenerate target-rank `G′`
seeds at `P21`** with `s₀ = 1`, `dim R_a = 0`, `dim U = 1` that *Step 2.3*'s
calculus **proves** fail at every placement. Those are **known** escape
failures and therefore the right adversarial bed: apply a random `S ∈ so₃` and
ask whether the criterion matrix's minors move **while the target-rank
condition survives**.

**The predicted death, and you must confront it head-on rather than discover it
at the end.** If that failure locus is **shear-invariant, (ZH-1) dies
immediately — and dies for exactly §4.6's growing-ground-set reason**, since
`so₃(k)` is a **fixed-dimensional** group and therefore *cannot see the graph*.
§9.1 records this as the honest risk; §4.6's filter is the arc's most reliable
killer. **A coordinator reading, offered to be tested and not inherited:** the
obvious repair is to make the group **graph-indexed** — a shear per body or per
hinge, i.e. an action of `so₃(k)^{V}` or `so₃(k)^{E}` rather than one global
`S` — which would pass the growing-ground-set test by construction. Whether
such a product action still preserves the form generator-wise is the question
that decides (ZH-1)'s repair, and the evidence behind this reading is only the
single-`S` computation `ωᵀSω = 0`, i.e. nothing about the product action at all.
**A precise, well-grounded "(ZH-1) is dead, and here is the exact reason"
closes a standing shelf item and is a perfectly good outcome** — better than a
hedge. Report the death as a HIT of the negative kind, with the shelf row moved.

**Secondary deliverable, bounded and prose-only — the OWED filter check.**
§8's board records one debt against the shelf: *"the §2.5 counting-saturation
check that (ZH-2)/(ZH-3) owe is a cheap prose-only slice and worth running
opportunistically."* Run it. **(ZH-2)**'s potential `∆ = (self-stress dim) +
trdeg_k K − 3|V|` passes §4.6's growing-ground-set test (it is indexed by
`V(G)`/`E(G)`) but has **never** been read against §2.5's counting saturation —
`trdeg` is a *dimension* rather than a count of combinatorial objects, which is
precisely why the check is non-obvious and owed. **(ZH-3)**'s codimension-count
rank lower bound owes the same. **No driver, no new labels beyond the
reservation, no pricing onto §8's board** — a verdict of the form *"survives
§2.5 / dies by §2.5, because …"* for each, and nothing more. The shelf stays
off-board either way.

**Bars — the provenance bar is the hard one.** The source is a **preprint,
unrefereed**, its own acknowledgment credits an AI assistant with *"the
refinement of proof details, the Lean formalization and its verification"*, and
**neither the paper nor the repository has been independently checked by this
project**. Per top-level `CLAUDE.md` *Referencing prior work* and
`DESIGN.md` *Formalize everything the argument uses*: it is an **IDEA SOURCE,
never a citation**, and **no theorem of it may be imported, assumed, or leaned
on**. Your deliverable must stand on (a) **classical facts** — Witt's theorem
and the α/β classification of the Klein quadric's maximal isotropics are
already in §7's in-use list, so **check first whether the shear is already
implicitly available** rather than treating it as new — and (b) **this
project's own drivers**. If a step needs the source's Lemma 3.4 or
Proposition 3.3, that step is **not delivered**; say so. (§9's own dimensional
note, for orientation only: its Lemma 3.4 sits *exactly* on its boundary at
`d = 3` via `2(d−1) = d+1`, which fails at `d ≥ 4`, so an error there would be
structural rather than repairable.) Do not attack (ZH-2)/(ZH-3) beyond the
filter check above, do not open (ZH-4)/(ZH-5), do not write up (ZH-6). Do not
touch `hbareSplit`/(BE-14) — **BZAVOID owns it concurrently**. Do not touch
W4 / `hcontract`. **No `.lean`** — the standing Lean hold. **This dispatch is
read-only w.r.t. every shared file and commits NOTHING** (RESEARCH-ARC §2).

**Riders.** TERMINATION check E1/E2/E3 at the return (**E3 ARMED by GBAL** —
report, never fire). **F11:** every headline claim needs a driver testing
**that sentence**; *"the failure locus is shear-invariant"* is an
**invariance** claim and needs a driver that tests invariance, not one that
samples a few `S`. **F25:** state your verification bar off the shipped
driver; every script you run is committed. **Cap disclosure mandatory.** All
figures exact ℚ, seeded, degeneracy-guarded — the `plane_basis` precedent (a
degenerate sampler silently contaminated several passes' escape-failure
figures) is exactly this bed, so guard the `P21` seeds explicitly and assert
their `s₀`/`dim R_a`/`dim U` against *Step F5(d)*'s recorded values before
drawing any conclusion from them. `notes/scripts/README.md` binds.

**Driver — expected, at the pinned path `notes/scripts/w4/zshear.py`.** The
adversarial pre-test is a measured claim and needs one. Read-only imports;
untracked, for the coordinator to gate and commit.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
ZSHEAR"): **new section §(K-shear)** in `notes/Pencil-informal.md`, tag
**`SH-`** (globally 0-hit, cleaner than `BE-`); labels **(SH-1)–(SH-6)**,
**Steps SH1–SH5**; return any unconsumed remainder to the tail. If (ZH-1) dies,
the section is still minted — a recorded death is the deliverable.

### ZSHEAR — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: (ZH-1) is REFUTED — a HIT of the negative kind, and the refutation is
a computation-free identity plus its exact verification. `hbareSplit`/(BE-14)
untouched; no gap-map row moves; not a PENCIL event.**

**The exact reason: the shear is a GAUGE transformation.** Writing `s` for the
axial vector of the skew `S`, **`Φ_S = Λ²(T_{−s})` identically in
`ℚ[s₀,s₁,s₂]`** — the shear group *is* (not "is isomorphic to") the
**translation subgroup of `PGL(4)`** acting on line coordinates, verified by
comparing two independently-built matrices. Also identically:
`Q(w) = ⟨w,★w⟩ = 2·dir(w)·mom(w)`, upgrading §9.1's *"same form"* from a
reading to an identity in the harness's own Plücker convention; and
**`Φ_Sᵀ★Φ_S = ★`**, so **`Q` is the shear group's own defining invariant**.
(SH-1)/(SH-2). The spec asked *"check first whether the shear is already
implicitly available to this project"* — the answer is **yes, trivially**: it is
the 3-dimensional tip of a 15-dimensional group the arc has had all along, and
its pointwise-fixed 3-space is a **β-plane of the Klein quadric**, already in
strategy §7's in-use list, whose pointwise stabilizer in `O(Q)` is exactly
3-dimensional — so nothing larger is on offer either.

**On the arc's own adversarial bed the failure locus is shear-invariant, and by
more than rank equality.** *Step F5(d)*'s five proven escape failures were
**re-derived and asserted before use** (the spec's explicit requirement, and the
`plane_basis` precedent): `s₀ = 1`, `dim R_a = 0`, `dim U = 1` at seeds
101/111/128/136/138, all three §(K-tight) structure identities asserted at all
35 valid seeds. Then, at all 35 seeds and both strata: `U′ = Φ^{−T}U`,
`R_a′ = Φ^{−T}R_a`, `Λ²Π̂(b)′ = Φ·Λ²Π̂(b)`, `C(ab)′ = Φ·C(ab)` (45/45); the
`2 × dim U` criterion matrix **equal entry-for-entry** in the pushed basis
(150/150, because `⟨Φ^{−T}u, ΦC⟩ = ⟨u,C⟩`); exact rank equal at corresponding
placements on both KT routes (222/222); pitch preserved (30/30). **The minors do
not even move.** So for a fixed seed the bad-`S` set is **all of `so₃`** (if the
seed fails) or **empty** (if it escapes) — never a *proper nonempty* affine
subspace, and (ZH-1)'s mechanism, *"finitely many proper affine subspaces cannot
cover an affine space over an infinite field"*, is a true principle that is
**vacuous here**. (SH-3)/(SH-4).

**The coordinator's offered repair is decided, in both of its readings.**
Identically,
`Q(Φ_{t_u}X_u − Φ_{t_v}X_v) = Q(X_u−X_v) + 2(t_u−t_v)·(dir X_u × dir X_v)`, so
the per-body product action does **not** preserve the form generator-wise off
the diagonal (defect `2` at an exhibited instance) and is therefore not an
action on the variety. On the carrier side the honest lift is per-body
**translations**, and the maximal carrier-preserving family at fixed normals is
computed exactly — cut by `normal_h·(t_u − t_h) = 0` per hub-neighbour
incidence, **dim 49 of 63** at `P21`, containing the diagonal, and it **does**
pass §4.6's growing-ground-set filter, unlike `so₃` itself. But it acts **simply
transitively on the fixed-normal slice of the pencil chart**: it *is* §(K-slide)
*Step 1(e)*'s chart re-labelled, and it **moves `dim R_a`** (6/6 fields kill the
forced failure, against 0/45 for the global shear). So it gives deformation,
which the arc already has, and propagates nothing. (SH-5).

**The general form, and it is stronger than the predicted death.** §4.6
predicted *"`so₃` is fixed-dimensional and cannot see the graph"*. True, but not
sharp: the shear cannot see **anything** — it is a gauge, and every ingredient
of the criterion transports with it. The sharp statement is a **dichotomy**: a
group under which the criterion is equivariant **cannot** turn a failing seed
into an escaping one; a family that *does* move a failure is no symmetry and
propagates no witness. (SH-6). Fourth instance of §4.6 (R1)'s relocation
pattern — and the **first one backwards**, in that the candidate was retired by
being shown *already owned* rather than out of reach.

**The residue worth keeping, and it is new, small and permanent.** `Q(r̃) ≠ 0`
is `PGL(4)`-invariant, so **no gauge-fixing or frame normalization can ever
supply it**. Coordinator-checked for consistency against landed work: this does
**not** disturb `m2/lambda1.m2` block **(M4)**, whose landed status is a
*computational-feasibility* result (the gauged local frame with `λ` free
finishes; the 600 s kill is the ungauged 28-point expansion). The residue adds a
**scope** statement on top of it — legitimate for computation, provably
incapable of producing the non-vanishing — so it strengthens rather than
contradicts, and orphans nothing.

**Secondary deliverable — the OWED §2.5 filter check, DISCHARGED (prose only,
nothing priced onto §8's board).** **(ZH-2)** survives §2.5 **only in its
stratified reading**: at the generic point of the *whole* chart
`trdeg = dim(chart)`, which is a function of hub/degree data alone (§(K-slide)
*Step 1(e)*'s tower), so whole-chart `∆` **is** count-expressible and §2.5 bites
exactly. **(ZH-3)** survives the filter — a codimension is geometric and does
separate seeds at a fixed graph — but the sharper finding needs no filter: it is
**circular**. On the tight class `m = 5|E| = target`, so `rank ≥ m − c` reaches
the target only at `c = 0`, where the statement reads *the pencil chart's
generic self-stress dimension is 0* — which **is**
`HasGenericPencilRealization`. Recommendation accepted: (ZH-3) is re-labelled
**circular as posed** rather than *owing a filter check*.

**Provenance bar honoured in full**, and independently confirmed at landing: no
theorem of the source is imported, assumed, or leaned on; nothing in the section
needs its Lemma 3.4 or Proposition 3.3; and nothing in it is evidence for or
against them. The author-name item struck earlier in the session (`f3ded610`)
appears nowhere in the draft, the driver, or the return — the mid-flight
correction took.

**Coordinator verification.** `--validate` re-run at **356 s** (the return said
353 s; the bed is cached once per process, standalone `--inv` alone is 426 s) and
`--iso` separately; every headline figure reproduces — 150/150, 222/222, 45/45,
30/30, `dim R_a` moved 0/45 vs 6/6, family dim 49/63, defect 2. **Four Lean pins
verified against the definition BODIES**, not docstrings: `Theorem55.lean:3059`
(`HasCoplanarPanelRealization`), `Statement.lean:88`
(`HasPencilPanelRealization`), `Motive.lean:110` (`IsNondegPencilRealization`)
and `Motive.lean:140` (`HasGenericPencilRealization`, which is what makes the
(ZH-3) circularity claim hold in shape). **The load-bearing identities were
re-derived independently by the coordinator:** a translation sends
`(dir, mom) ↦ (dir, mom − t × dir)`, which is exactly `Φ_S` with `S ↔ −t`; and
`dir·mom = p₀₁p₂₃ − p₀₂p₁₃ + p₀₃p₁₂` is the Klein form, with
`Q(Φ_S(ω,b)) = 2ω·(b + s×ω) = 2ω·b` since `ω·(s×ω) = 0` — the source's own
`ωᵀSω = 0`, in our coordinates. **One convention note, not a defect:** the
hand-derivation gives the (SH-5)(i) defect term with the opposite sign, which is
the axial-vector orientation implied by `Φ_S = Λ²(T_{−s})`; the driver computes
it symbolically in its own convention and exhibits the defect, and the
conclusion (not form-preserving off the diagonal) is sign-independent.

**F25 bar, read off the shipped driver:** four modes, all foreground with
explicit timeouts, `--validate` **inside** the 600 s budget, exact ℚ throughout,
the two structural modes fully **symbolic** (identities in `ℚ[…]`, no sampling
at all — the strongest evidence class the arc has), the bed re-derived and
asserted before use, and the `plane_basis` guard **reported rather than
assumed** (`star_generic` rejects 5/5 failing and accepts 26/30 escaping —
rejection is **necessary, not sufficient**, stated as such). No scratchpad probe
backs any claim.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 stays
**ARMED by GBAL**, neither fired nor disarmed.

## BINDUC — forty-second ordinal, the fiftieth direction (concurrent pair, prepped 2026-08-26)

**Selection provenance: a USER DIRECTIVE naming the criterion, the pick made
under it by the coordinator.** 2026-08-26, verbatim: *"Let's continue with 2
dispatches in parallel one on the direction that is most likely to have most
impact towards either proving or disproving the target theorem and one
continuing the Zheng line."* So the *criterion* is the user's and sharper than
the standing one — **max impact on proving or disproving `PencilPair K 3 G`** —
while the pick against it is coordinator-set, and the twelfth's disclosure
applies (no independent top-rung ranking of the alternatives). Dispatched
**un-named**, concurrently with ZJACOB, at **`recon-opus`** (fable conserved).

**Why this is the max-impact pick, stated so it can be checked rather than
trusted.** (BE-14) is the only statement on the board that removes a **carried
item** outright: proven, it discharges **`hbareSplit`** *and* **`PencilPair`'s
unconditional second conjunct**, as a standalone theorem. The honest limit,
stated up front: it does **not** discharge `hK` or `hcontract`, so it takes the
phase from three carried items to two and delivers half the target motive — and
that is still strictly more than anything else available, since `hK` is the
phase's hardest item with **no named next slice after 47 directions** and
`hcontract` cannot close without the wave-sized **(K-res)**, which the user
declined in favour of a scoping slice. **BZAVOID's own ranked successor list puts
this first.**

**What BZAVOID changed, and it is why this is now a construction problem.**
(BE-16) proved (BE-14) is **EXISTENTIAL, not generic**: `rank ≤ target` holds
universally, so **one witness per graph settles that graph**, and the pencil
stratum **is** the planar-atom molecular stratum — the object to build is a
*point* configuration `p : V → P³` with every closed star coplanar, i.e. an
all-trigonal-planar molecule. The residual, verbatim from *Step BE18*:

> `∀ G` 2-connected, `∃ p : V(G) → P³` with `{p_w : w ∈ closedNbhd(v)}` coplanar
> for every `v` and `p_u ≁ p_v` on edges, such that the molecular body-hinge
> rigidity matrix at `p` has rank `6(|V|−1) − def₃(G)`.

**The target: carry the induction BZAVOID opened.** (BE-18) proved composition
over a **1-vertex cut** (`def₃` additive both directions, 907 gluings; the rank
half by `GL₄`-alignment of the shared body's flag), which is what reduced
(BE-14) to 2-connected graphs. Your job is the **next layer and the base**:

1. **The 2-cut composition.** BZAVOID asserts it *"looks routine by the same
   `GL₄` alignment, with `def₃(G) = def₃(G₁) + def₃(G₂) − 6` to be checked"* —
   **asserted, not proved or measured**, and disclosed as its cap 8. Prove or
   refute both halves. **Do not inherit the `− 6`:** derive the correction term
   from `def₃`'s own maximand (`|P| = |P₁| + |P₂| − 2` when both shared vertices
   sit in merged parts; the shared pair may or may not be adjacent, and the
   `GL₄` transitivity that made the 1-cut alignment free is on
   (plane, point-on-plane) **flags**, so a 2-cut needs two flags aligned at
   once and that is a real condition, not a restatement). A refutation with an
   explicit witness is as good an outcome as a proof.
2. **The base class, and this is the part with no named answer.** If 1- and
   2-cuts compose, the base is **3-connected**. Say plainly whether that base is
   attackable, and if not, what the honest decomposition is. BZAVOID's other
   offered base — the **`def₂ = def₃` closed-form slice**, still unclaimed and
   still the user's declined-as-a-*deliverable* partial — is legitimate **as a
   base case inside this induction**; use it that way if it fits, and say so.
3. **Where it obstructs, if it does.** An induction that closes on a named
   subclass and provably fails outside it is a real result — the subclass is
   then the first proved-attainment class the arc owns beyond BZAVOID's
   forced-triangle corollary.

**A TRAP, coordinator-verified in the Lean, that you must not walk into.** The
project has a landed well-founded induction principle over exactly this kind of
object: `Graph.minimal_kdof_reduction`
(`Molecular/Induction/ForestSurgery/Reduction.lean:673`, `\leanok`, KT
Theorem 4.9). I read its signature: its three closure hypotheses are named
**`hbase`**, **`hsplit`** and **`hcontract`** — and **`hcontract` is
byte-for-byte the phase's own PARKED carried item**. Scaffolding (BE-14) on that
principle therefore **re-imports the exact obligation (BE-14) is valuable for
avoiding**, and would convert a standalone theorem back into a conditional one.
It also runs only over `IsMinimalKDof n 0`, not over all graphs, so it does not
even cover the statement. **Go by connectivity decomposition, not by the KT
reduction moves.** If you conclude the KT scaffold is nonetheless the right one,
that is a **finding to report, not a licence to use it** — it would be a
re-routing of the phase's architecture and is the user's call.

**What counts as a HIT — state which you got.**

1. **The induction advanced.** 2-cut composition proven (with the correct
   correction term derived, not inherited), and the base class named with an
   honest assessment. Best case: (BE-14) proven on a named, non-trivial class.
2. **(BE-14) PROVEN.** The phase-target result. If you get here, say so plainly
   and do not decorate it.
3. **An obstruction, located.** The induction provably fails at a named
   decomposition class — and then the question that matters for the *disproof*
   side: does the failure suggest a **new universal-cap mechanism**? BZAVOID
   proved the forced-degeneration cap can never refute (BE-14) at any graph
   ((BE-15), cap-free), so a disproof now **needs a genuinely new cap
   mechanism**, and an obstruction is the most likely place one would surface.
   Report it as a candidate, never as a refutation.
4. **An honest OPEN with the route re-priced** against the `∃`-seed + repair
   alternative, whose chartless wall (§(K-tight) *Step 5*) BZAVOID did not lower.

**Bars.** **Option B (the insertion calculus) stays un-commissioned** (2026-07-30,
standing). **Do not re-attempt the three routes BZAVOID closed:** the
forced-degeneration cap as a refutation route ((BE-15), cap-free, every graph);
the landed Phases-24–26 `G²`/molecule-dictionary apparatus ((BE-17) — its
general-position gate is the *literal negation* of the pencil condition, and its
sufficient condition measures FALSE at three shapes); and the
transversality/dimension count ((BE-16)(iv), structural). Do not re-derive
BATTAIN's or BZAVOID's figures — **cite them**. Do not attack `hK`, (GR-15),
class uniformity, or §(K-grid)'s ledger. Do not touch W4 / `hcontract`. **No
`.lean`** — the standing 2026-08-05 Lean hold. **Read-only w.r.t. every shared
file; commit NOTHING** (RESEARCH-ARC §2) — ZJACOB runs concurrently.

**Riders.** TERMINATION E1/E2/E3 at the return (**E3 ARMED by GBAL** — report,
never fire). Classification mandatory if anything in shape 3 fires: say whether
you have refuted `PencilPair K 3 G`, (BE-14)-for-all-`G`, or only a route, and
do not overstate a single witness. **F11:** a driver per headline sentence, and
"routine"/"always"/"the only" are their own claim class needing an *enumerating*
driver — note that the thing you are checking is itself an inherited
*"looks routine"*, so this rider bites directly. **F25:** state your
verification bar off the shipped driver; every script you run is committed.
**Cap disclosure mandatory.** Exact ℚ, seeded, degeneracy-guarded; multi-seed any
shortfall claim (F27 — rank is lower semicontinuous, so one draw is a lower
bound only, and both BATTAIN and BZAVOID were bitten by exactly this).
`notes/scripts/README.md` binds; the `kbare/` sibling-import set is recorded
UNPAID debt with `w4/bzavoid` its second consumer — extend the list, make no move.

**Driver — expected, at the pinned path `notes/scripts/w4/binduc.py`.** The
2-cut `def₃` law is a measured/enumerable claim and needs one; `w4/bzavoid.py`'s
`glue` mode is the precedent to extend from (read-only import).

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BINDUC"): §(K-bare-ext) **extends**, no new section; labels
**(BE-20)–(BE-24)**, **Steps BE19–BE23**; return any unconsumed remainder.

### BINDUC — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: HIT shape 1, advanced on all three jobs; shape 3 answered (the
candidate mechanism EXISTS and fires empty); shape 2 not reached. `hbareSplit`
OPEN and pinned; not a PENCIL event. The single biggest advance the arc has made
on the phase target.**

**Job 2 — the part the spec said had "no named answer" turned out FREE, in four
elementary lines.** **A 3-connected graph has `def₂ = 0`**: 3-connectivity ⇒
3-edge-connectivity ⇒ every proper nonempty `S` has `|∂S| ≥ 3` ⇒ summing over a
`q`-part partition, `2d(P) ≥ 3q` ⇒ `partitionDef₂ ≤ 3(q−1) − 3q = −3 < 0` for
every `q ≥ 2`, while `q = 1` gives `0`. Hence `def₃ = 0` (BZAVOID's (BE-15)(a)),
hence the **flat witness** — all points distinct in one plane, the *legal dual*
of BATTAIN's chart-illegal coincident-points cone — attains in closed form.
**EXHAUSTIVE at 226 891 3-connected labelled graphs, `n = 4…7`, zero
exceptions**, and the bound is **tight**: the driver measures the worst
`partitionDef₂` at exactly the proved `−3`. **So BATTAIN's declined
`def₂ = def₃` slice, which the spec re-authorized as a base case, covers the
ENTIRE base.** Contrapositive, and it reframes the whole problem:
**`def₂ > def₃` forces a cut of size `≤ 2`** (16 214 exhaustive instances, none
3-connected).

**Job 1 — the inherited `− 6` is REFUTED, not merely unchecked, and the spec's
instruction not to inherit it was load-bearing.** It goes **negative** — two
triangles sharing an edge give `−4` against the true `0` — which is impossible
since `def₃ ≥ 0` always, and it is negative at **9 425 of 10 804** enumerated
gluings (87.2 %), correct at only **54** (0.5 %). The exact law, derived from
`def₃`'s own maximand and proved in **both** directions:
**`def₃(G) = max(g₁+g₂, f₁+f₂−6) = f₁+f₂ − min(δ₁+δ₂,6)`**, with `g_i` the
maximand over partitions putting the cut pair in one part and `δ_i ∈ [0,6]`; both
branches are needed (`g₁+g₂` attains the max at 10 798, `f₁+f₂−6` at 54).

**The rank half is reduced to ONE named lemma, with its obstruction located.**
`dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁+ρ̄₂)` over relative-screw subspaces of
`Λ²K⁴`, so **attains ⟺ `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)`**. Two things it needs, both
named: **(a)** welded-framework attainment (`ρ_i ≤ δ_i` always), so the induction
must carry a **strengthened statement**, not (BE-14) itself; and **(b)** general
position, which the residual gauge group — dim **7** adjacent / **5**
non-adjacent, against `Gr(3,6)`'s dim **9** — provably cannot supply. **Free
cases proved:** `δ₁ = δ₂ = 0`, and with *one* rigid side the criterion collapses
to `ρ = δ` on the other with **no general position at all**, confirmed as a
biconditional at 296 ear additions (240 attaining; the 56 misses are all
hub-load-4 *constructor* caps with the cause localized to `ρ₂ = 3 < δ₂`, never
shortfall claims).

**(BE-14) is now ONE LEMMA away, and the decomposition is exhaustive.** Base
`{3-connected}` ∪ `{max deg ≤ 2}` ∪ `{def₂ = def₃}` — note the middle set is
where the landed `IsGeneralPositionPlacement` gate *is* satisfiable, so
(BE-17)'s dead route is alive on exactly its complement — plus 1-cuts (BE-18),
plus the 2-cut step. Only the last is open. A new **hub-plane construction** (one
plane per hub or per forced hub class, feasible when every closed neighbourhood
holds `≤ 3` hubs) attains at **5 824** graphs with **0 failures**, **2 441 of
them with `def₂ > def₃`** where the flat witness provably misses — each a
per-graph theorem, and collectively **beyond every witness the arc had** — and it
reaches necklace(3)/(4) systematically. The class-level statement is **measured,
not proved**, and is disclosed as such.

**The disproof side, which the spec asked about explicitly: the new-cap mechanism
EXISTS, is strictly more general, and fires EMPTY.** The general propagation rule
is *"`π_v` is forced to `π` once `closedNbhd(v)` holds three independent points
already in `π`"*, which fires **without any triangle** — at a `K_{2,3}`, and in
chains, so **`K_{3,3}` is forced flat and triangle-free** (driver-checked both
ways). Hunted under an **aggressive** combinatorial closure that *over*-claims
forcing (so an empty result is the stronger statement): **27 470 connected graphs
exhaustive at `n ≤ 6` (20 963 forced flat) plus 4 800 sampled at `n = 7…10`
(4 307 forced flat) — ZERO with `def₂ > def₃`**, worst gap `0`. The largest
`def₂` at a forced-flat graph is **5**, so with BZAVOID's `def₂ ≥ def₃` the
measured statement is the strictly stronger **forced flat ⇒ `def₂ = def₃`** —
where the flat witness is forced, it therefore **attains**, and the mechanism is
harmless. **MEASURED, not proved, and reported as a candidate rather than a
refutation** — exactly as the spec required.

**THE SCOPE CORRECTION THIS FORCES ON BZAVOID, made in this commit.** (BE-15)'s
propagation rule is **adjacent-pair** forcing, and *that* is what needs a
triangle; the general rule accumulates three independent pinned members of a
closed neighbourhood and needs none. So the forced class partition can be
**strictly coarser** than `π(G)`'s `T(G)`-components, and on those coarser
classes (BE-15)(ii)'s *"each class is triangle-covered, hence `def₂ = 0`"* step
**does not apply**. What (BE-15)(ii) establishes, exactly: **the TRIANGLE-forced
mechanism is closed at every graph, cap-free and by an argument** — unchanged and
sound. The **general** mechanism is closed only as **MEASURED**. The unqualified
*"no graph whatsoever"* in the landed claim, and the coordinator's own landing
prose repeating it, **over-reached**; both are corrected in place (workbook claim,
gap-map row, the fan-out header's BZAVOID clause, and the phase note), and a proof
of (BE-23)(ii) is now the named target that would restore it in full. **This is
the second time this session a landed headline was re-priced by the next
direction** (the GMINM/F26 shape), and the second time the coordinator's own
verification passed it — because, again, no driver tested the sentence that was
wrong.

**THE TRAP: confirmed, with a correction to the COORDINATOR'S justification.**
`Graph.minimal_kdof_reduction`'s conclusion is
`∀ G, G.IsMinimalKDof n 0 → 2 ≤ ncard → P G`, so it **cannot reach (BE-14)'s
`∀ G`** — the trap conclusion stands and the direction went by connectivity, with
(BE-20) now giving a *positive* reason to. But its `hcontract` is **NOT
byte-for-byte** the phase's parked item, as the spec claimed: the principle
quantifies over `IsMinimalKDof n 0` with a **richer** induction hypothesis,
whereas the phase's (`Escape.lean:451`) quantifies over `Loopless` with
`V(G').Nonempty` only — the same obligation *shape* at `P := PencilPair K 3`, with
**the phase's strictly stronger**. Instantiating would hand back a **sibling**
obligation, not the parked one. Coordinator-verified against both signatures at
landing: **the correction is right and the spec was wrong.**

**Coordinator verification.** Full-figure re-run, not `validate` alone: `base`
(**226 891 / 0**, 411 s — the exhaustive `n = 7` tier `validate` skips, plus the
16 214 contrapositive), `twocut` (**10 804** gluings, law at every one, `− 6`
correct at 54 / impossible at 9 425), `force` (**27 470 + 4 800**, zero
candidates, `K_{3,3}` forced-flat-and-triangle-free confirmed), `validate`
(114 s, all modes). **The load-bearing proof was re-derived independently by the
coordinator** — 3-connected ⇒ 3-edge-connected ⇒ `|∂S| ≥ 3`; summing over parts
gives `2d(P) ≥ 3q`; so `partitionDef₂ ≤ 3(q−1) − 3q = −3`, and `q = 1` gives `0`,
hence `def₂ = 0` — and the driver's measured worst value of exactly `−3` confirms
tightness rather than merely consistency. The `− 6` refutation was independently
sanity-checked from `def₃ ≥ 0` alone: any pair of `def₃ = 0` pieces makes
`def₃(G₁)+def₃(G₂)−6 = −6 < 0`, impossible, so the formula could not have been
right for *any* 3-connected pair — which, by (BE-20), is most of them. **Both Lean
signatures compared directly** for the trap correction.

**F25 bar, read off the shipped driver:** eight modes, all foreground with
explicit timeouts, exhaustive enumerations backing every "always"/"never"
sentence, the `|∂S| ≥ 3` step swept separately from the `def₂` computation (so the
proof's two steps are checked independently rather than jointly), the 2-cut law
checked against an **independent oracle**, every RNG seeded, and the forcing hunt
run under a deliberately **over**-claiming closure so that emptiness is the
stronger reading. **Eleven caps disclosed**, the load-bearing ones being that
(BE-20)(ii) still inherits (BE-13)'s *proven-informally* planar body-pin import (a
direct point-side proof would remove it — a small named target), that (BE-22)(v)
is a **dimension count rather than an obstruction proof** with the piece's own
moduli uncounted, and that (BE-23)(i)/(ii) are class-level **measured**. No
scratchpad probe backs any claim.

**TERMINATION: E1 NO, E2 NO** — one landed claim is refuted (BZAVOID's `− 6`) but
**with its successor in hand**, which is the shape E2 explicitly does not fire on;
coordinator-re-run and agreed. **E3 ARMED by GBAL, not fired.**

## ZJACOB — forty-third ordinal, the fifty-first direction (concurrent pair, prepped 2026-08-26, **the Zheng line, second direction**)

**Selection provenance: the same 2026-08-26 user directive**, whose second half
reads *"and one continuing the Zheng line."* The pick within that line is
**forced by the shelf's own updated order**, not chosen: §9.3's head after
ZSHEAR struck (ZH-1) is **(ZH-4)**, with (ZH-5) a design note rather than a
result, (ZH-2) surviving §2.5 only in its stratified reading, (ZH-3) re-labelled
**circular as posed**, and (ZH-6) write-up material that is never a dispatch.
Dispatched **un-named**, concurrently with BINDUC, at **`recon-opus`**.

**Why (ZH-4) is the right successor and not merely the next in line — this comes
straight out of ZSHEAR's own return.** ZSHEAR established that (ZH-1)'s
mechanism was **the arc's own**: *"avoid finitely many proper subvarieties over
an infinite field"* is **free** once `P ≢ 0` is known, so the real gap is
**PROPERNESS of the failure locus**, and (ZH-1) bought only avoidance. **(ZH-4)
is aimed exactly at properness:** if the escape-failure locus can be presented as
the **singular locus of the universal infinitesimal-motion cone along its zero
section**, then *"escape fails only on a proper closed subset"* becomes *"the
cone is generically smooth along its zero section"* — a **Jacobian-rank
computation** rather than a witness hunt. That is the arc's open thing, attacked
at the point ZSHEAR identified as the actual gap.

**The technique, and where it already touches this project.** §9.2's reading of
the source's Theorem 4.2 is a scheme-theoretic upgrade of **exactly the
White–Whiteley pure-condition material §(K-pure) works by hand**: degeneracy loci
as determinantal subschemes of a two-term complex; the universal
infinitesimal-motion cone a **local complete intersection of the expected
codimension**, hence Cohen–Macaulay and equidimensional; and — the usable part —
the identification of the **first degeneracy locus with the singular locus of
that cone along its zero section**, via the Jacobian criterion. §(K-pure)'s chord
obstruction and isotropic completions (**(PC1)**–**(PC3)**, **(PC-Z)**) are
already local computations at a limit carrier, so §9.2 prices this as *"a
repackaging with real leverage and no filter problem on its face"* — **test that
pricing rather than inheriting it.**

**Two ZSHEAR findings that bind on you, and one that does not.** **Binding:**
(SH-6)'s **dichotomy** — a group under which the criterion is equivariant cannot
turn a failing seed into an escaping one, and a family that *does* move a
failure is no symmetry and propagates nothing. Check early whether the Jacobian
route is a disguised instance (it should not be: smoothness is not a symmetry
claim), and say so explicitly either way. Also binding: **`Q(r̃) ≠ 0` is
`PGL(4)`-invariant, so no gauge-fixing or frame normalization can ever supply
it** — if your route reaches for a normalized local frame, that residue says
what the frame can and cannot buy. **Not binding:** (ZH-1)'s death was
gauge-triviality, which is specific to the shear and says nothing about
(ZH-4).

**What counts as a HIT — state which you got.**

1. **Properness delivered, or reduced to a named Jacobian-rank computation** with
   the exact locus, complex, and quantifier written down. Even a clean reduction
   is a real result, because properness is the identified gap.
2. **The route is DEAD, with the exact reason.** ZSHEAR is the precedent: a
   precise, well-grounded death that strikes a shelf candidate is a HIT of the
   negative kind and a perfectly good outcome. The likeliest deaths to check
   first: the cone is **not** a local complete intersection of the expected
   codimension in *our* carrier (the source's is bar-joint `(2,2)`-sparse, ours
   is body-hinge at multiplicity 5 — **no theorem transfers**); or the
   identification needs a hypothesis the pencil stratum violates, which is
   exactly how (BE-17) killed the `G²` route one commit ago.
3. **An honest OPEN with the route priced** against §(K-pure)'s by-hand
   computations — is this a genuine upgrade or a re-encoding?

**Bars — the provenance bar is the hard one and is unchanged.** The source is an
**unrefereed preprint** whose own acknowledgment credits an AI assistant with the
refinement of proof details, the Lean formalization and its verification, and
which **this project has not independently checked**. Per top-level `CLAUDE.md`
*Referencing prior work* and `DESIGN.md` *Formalize everything the argument uses*:
it is an **IDEA SOURCE, never a citation**, and **no theorem of it may be
imported, assumed, or leaned on** — its Theorem 4.2 included. Your result must
stand on (a) classical facts (the Jacobian criterion, determinantal-scheme
codimension bounds, Cohen–Macaulay/equidimensionality, and the White–Whiteley
pure-condition material already in §7's in-use list — **check first whether what
you need is already available to this project**) and (b) this project's own
drivers and definition bodies. If a step needs the source's Theorem 4.2,
Lemma 3.4 or Proposition 3.3, **that step is not delivered** — say so. §9's
orientation note, for context only: its Lemma 3.4 sits *exactly* on its boundary
at `d = 3` via `2(d−1) = d+1`, so an error there would be structural rather than
repairable. Do not open (ZH-2)/(ZH-5), do not re-litigate (ZH-1) or (ZH-3), do
not write up (ZH-6). Do not touch (BE-14)/`hbareSplit` — **BINDUC owns it
concurrently.** Do not touch W4 / `hcontract`. **No `.lean`** — the standing
Lean hold. **Read-only w.r.t. every shared file; commit NOTHING.**

**Riders.** TERMINATION E1/E2/E3 at the return (**E3 ARMED by GBAL** — report,
never fire). **F11:** a driver per headline sentence; *"the cone is a local
complete intersection of the expected codimension"* and *"the singular locus is
exactly the first degeneracy locus"* are **structural** claims — either derive
them symbolically or exhibit them at named carriers, and never state them more
strongly than what you ran. A **symbolic** dispatch also starts from
`notes/scripts/m2/README.md`; strategy §5.3's measured boundary is the standing
warning (the ungauged 28-coordinate degree-52 expansion dies at 600 s), so scope
any Macaulay2 leaf against it up front rather than discovering it. **F25:** state
your verification bar off the shipped driver; every script you run is committed.
**Cap disclosure mandatory.** Exact ℚ (or exact `ℚ(i)` via `exactcore.Gauss`),
seeded, degeneracy-guarded; `notes/scripts/README.md` binds.

**Driver — conditional, at the pinned path `notes/scripts/w4/zjacob.py`** (plus
`notes/scripts/m2/zjacob.m2` if a symbolic leaf is genuinely needed; ZSHEAR
needed none and said so). A purely derivational result needs no new driver —
state that disposition explicitly. Read-only imports, untracked.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
ZJACOB"): **new section §(K-jac)** in `notes/Pencil-informal.md`, tag **`JC-`**
(globally 0-hit); labels **(JC-1)–(JC-6)**, **Steps JC1–JC5**; return any
unconsumed remainder. Mint the section even if the route dies — ZSHEAR's
precedent: a recorded death with its exact reason is the deliverable.

### ZJACOB — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: (ZH-4) is REFUTED — HIT shape 2 (a death with its exact reason) plus
shape 3's pricing. And the death is an EQUIVALENCE, not an obstruction**, which
is a sharper category than the spec anticipated. No gap-map row moves;
`hbareSplit`/(BE-14) untouched (BINDUC owned them concurrently); not a PENCIL
event.

**The route's input is computed for free, and that is the first half of the
problem.** (JC-1): the harness's 5-rows-per-hinge model is **not polynomial** in
the chart coordinates (`exactcore.perp_basis` is an `rref`, so a "Jacobian" of it
is basis-dependent); the polynomial presentation is `dominance.motion_system`'s
augmented system, `6|E|` equations polynomial in `y` and exactly linear in the
fibre variables. At a zero-section point its Jacobian is **`[0 | A(y)]`** —
**108/108** `y`-entries identically zero in `ℚ[pts]` (every `∂F/∂y` carries a
factor `ω_e`), fibre block equal to `motion_system`'s own matrix **240/240**
against an independently-built copy. So `rank Jac(y,0,0) = rank A(y)`, and
*"generically smooth along the zero section"* unfolds **with no computation in
between** to *"`rank R(y)` attains target generically"*. The direction is careful
about which half is free: `Sing 𝒞 ∩ Z ⊆ D_1` holds **unconditionally**; the
reverse inclusion — the half the route needs — is **conditional on the
expected-dimension hypothesis**.

**And that hypothesis contains the conclusion.** (JC-2), the load-bearing step:
stratifying by corank, `dim 𝒞 = max_{k≥0}(dim B_k + 6 + k)`, and since `B` is
irreducible (§(K-chart)) exactly one stratum is dense, so `𝒞` has the expected
dimension `dim B + 6` **⟺ `B_0 ≠ ∅` and `codim_B B_k ≥ k` for every `k ≥ 1`**.
On the tight class `#equations` equals that expected codimension (*Step JC1*), so
this is also exactly *"local complete intersection of the expected
codimension"* — and `B_0 ≠ ∅` **is** properness, which on the tight class is the
phase target. **The route's hypothesis contains its conclusion as its weakest
clause.** Coordinator-verified by re-deriving the stratification count
independently.

**The corollary that reshapes the shelf: (ZH-4)'s hypothesis IS (ZH-3).** The two
candidates §9 priced as its "concrete" ones were **one** candidate, and ZSHEAR's
*circular as posed* verdict on (ZH-3) transfers verbatim with a mechanism
attached. §9 now has **exactly one dispatchable candidate left** — (ZH-2) in its
stratified reading only.

**Two independent corroborations, each a separate claim class.** (JC-3): every
classical bound on the height of an ideal of minors is an **upper** bound and
takes the generic rank `r` as an **input** — Eagon–Northcott, Bruns,
Eisenbud–Huneke–Ulrich, with EHU's own introduction stating the direction in as
many words. On our shapes the sharpest reads the **graph-independent constant
`7` = 6 trivial motions + 1**, measured identical at **8/8** shapes, so §4.6's
growing-ground-set filter fires as well; and the input-dependence is *exhibited*
twice — `P21`'s two sub-loci (`r = 119` vs `120`) and `Nk₄`'s two global strata
(`89` vs `90`, recomputing (BE-13)'s law). (JC-4): the criterion is
**identically blind** to the pure-condition half — every partial of a
fibre-degree-`≥ 2` equation vanishes on the zero section (**84/84**, for a
general quadratic and for the arc's own `Q(t) = ⟨t,★t⟩`), so any cone carrying
the pitch is singular along its *whole* zero section at every `y`. That is (PC5)'s
invariant mismatch one level up: **tautologous where it applies, vacuous where
the arc needs help, with no third region.**

**The re-encoding is faithful, hence useless.** (JC-5): inserting `v` cuts
`𝒞_{G−v} × K⁶` by 10 rows on 6 columns → 4 conditions on the relative twist,
which is §(K-tight) *Step 2.1* **verbatim**; and over an escaping seed the
zero-section singular locus is *Step 2.4*'s conic `line(ab) ∪ P′`, both factors
exhibited at four carriers. The `line(ab)` component is **chart-illegal** — a
Lean pin the direction verified against the body, `Motive.lean:110`'s conjunct 4,
which at a degree-2 non-hub says exactly *"`pt v, pt a, pt b` not collinear"* — so
`P′` is what survives, which is the arc's existing object.

**General form (JC-6): a conservation law.** The determinantal/scheme package
converts expected codimension **into** structure and has **no theorem producing
it** over a non-generic base. The strongest repair — use Tay on the *ambient*
space, where the cone genuinely is an LCI, then restrict — dies to §(K-pure)
**(PC6)**'s already-exhibited descent failure at `P21`.

**Both coordinator-predicted deaths were refuted AS DIAGNOSES, and this is the
fifth such instance.** The spec named two likeliest deaths: *(i)* "the cone may
not be an LCI of the expected codimension in our carrier" — which **mis-locates a
conclusion as a checkable hypothesis**; *(ii)* "the identification may need a
hypothesis the pencil stratum violates" — the stratum does not *violate* it, it
**is** it. Both are wrong in a deeper way than a wrong guess: the *framing* was
wrong. This is the first instance where the promoted `RESEARCH-ARC.md` §7 rule
(one commit old) is what made the correction legible — the spec labelled them
"likeliest deaths to check first" rather than asserting them, so the direction
could report the framing error instead of quietly working around it.

**The provenance bar is explicitly NOT what kills this**, and the direction says
so: granting the source's Theorem 4.2 in full changes nothing, because a carrier
analogue would **be** the phase target. No theorem of the source is imported,
assumed or leaned on; nothing here bears on its Lemma 3.4 or Proposition 3.3.

**Binding-findings check, both explicit.** (SH-6): **not** an instance of the
symmetry clause — no group, and smoothness is not a symmetry claim (checked
early, as required) — but **is** an instance of the relocation clause, and the
**first onto the conclusion itself**. `Q(r̃) ≠ 0` being `PGL(4)`-invariant
**decided the symbolic-leaf question**: any M2 leaf is barred twice, ungauged by
§5.3's measured 600 s boundary and gauged by being provably incapable of producing
the non-vanishing. **No M2 leaf, and not for budget reasons** — exactly the
disposition the spec asked to be stated explicitly.

**Coordinator verification.** `--validate` re-run at **249 s** (the return said
237 s; timing variance, inside the 600 s budget either way) and `--sym`
separately; every headline figure reproduces — 108/108, 240/240, 84/84, 218
points at 112/106, the constant `7` at 8/8, and both input-dependence
exhibitions. **The Lean pin was verified against the definition body:**
`Motive.lean:110`'s conjunct 4 is
`∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v)`, and
`dominance.motion_system` exists at `w4/dominance.py:139` as claimed. **The
load-bearing step was re-derived independently:** over `B_k` the fibre has
dimension `6 + k`, the `B_k` partition `B`, so `dim 𝒞 = max_k(dim B_k + 6 + k)`,
which equals `dim B + 6` iff `codim B_k ≥ k` for all `k ≥ 1` **and** `B_0 ≠ ∅`
(else a `k ≥ 1` stratum is dense and already exceeds it) — and `B_0 ≠ ∅` is
attainment. **All four classical citations were checked** against
author/title/journal/volume/year/pages: Eagon–Northcott, Proc. Roy. Soc. London
Ser. A **269** (1962) 188–204; Bruns, PAMS **83** (1981) 19–24;
Eisenbud–Huneke–Ulrich, Amer. J. Math. **126** (2004) 417–438 (arXiv:math/0209184);
Hochster–Eagon, Amer. J. Math. **93** (1971) 1020–1058. All four resolve, and
**no section pointer is asserted for any** — the CLAUDE.md bar honoured rather
than guessed. The `7 = 6 + 1` arithmetic was checked independently under both
parametrizations of the Eagon–Northcott bound.

**F25 bar, read off the shipped driver:** four modes, all foreground with
explicit timeouts, `--validate` inside 600 s, exact ℚ throughout, `--sym`
**sampling-free**, `RNG_SEED = 20260826` with every RNG seeded. The `P21` bed was
re-derived and **asserted against *Step F5(d)*'s recorded `(30,5,5)`** before
use, and `repin.star_generic` was **reported, not used as a gate** (5/5 rejected,
26/30 accepted — independently reproducing (SH-3)), so the 112/106 split is a
tally of **exhibited points and never a rate**. No scratchpad probe backs any
claim.

**TERMINATION: E1, E2, E3 all NO** — coordinator-re-run and agreed. E3 stays
**ARMED by GBAL**, reported not fired.

## BTWOCUT — forty-fourth ordinal, the fifty-second direction (single dispatch, prepped 2026-08-26)

**Selection provenance: forced, for the first time in the arc.** No ranking was
needed and none was made. BINDUC closed every other layer of (BE-14)'s
decomposition and proved the decomposition **exhaustive**, so the strengthened
2-cut composition lemma is not the best candidate — **it is the only one**, and
proving it proves **(BE-14)**. The user's standing max-impact criterion
(2026-08-26) selects it trivially. Dispatched **un-named, single**, at
**`recon-opus`** (fable conserved). The twelfth's disclosure is **not** engaged:
there were no alternatives to rank.

**This is the highest-stakes dispatch of the arc.** (BE-14) proven discharges
**`hbareSplit`** *and* **`PencilPair`'s unconditional second conjunct**, as a
standalone theorem — two of the phase's three carried items' worth of motive, and
the phase's own 2026-08-05 standalone-significance bar. Read the state of the
induction from §(K-bare-ext) *Steps BE19–BE23* directly; it is **not** restated
here.

**The target, stated exactly as BINDUC left it.** Across a 2-cut `{u,v}` with
pieces `G₁, G₂`:

> `dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁ + ρ̄₂)` over relative-screw subspaces
> of `Λ²K⁴`, so **attainment ⟺ `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)`**.

**Two needs, both named by BINDUC, and they are not symmetric in difficulty.**

1. **The strengthened statement — and pinning it IS the first job.** `ρ_i ≤ δ_i`
   always, so what recurses is **welded-framework attainment**, not (BE-14)
   itself. **Write the strengthened statement down precisely before proving
   anything**: it must (a) imply (BE-14) at the top level, (b) be closed under
   1-cut composition ((BE-18)) and under the 2-cut step, and (c) hold at the
   three base classes BINDUC proved free. That is a **design decision**, it is
   the crux of this slice, and a wrong choice here wastes the rest — the phase's
   own precedent is that a mis-shaped kernel costs the whole tower built on it.
   If the statement you need is *stronger than anything the base classes give*,
   say so plainly: that is a real (negative) result about the induction, not a
   failure of the dispatch.

2. **General position — and BINDUC's own cap says the obstruction may not be
   real.** BINDUC prices the residual gauge group at dim **7** (adjacent cut
   pair) / **5** (non-adjacent) against `Gr(3,6)`'s dim **9**, concluding it
   "cannot supply" general position. **Its cap (BE-22)(v) discloses that this is
   a dimension count, not an obstruction proof, and that the PIECES' OWN MODULI
   ARE UNCOUNTED.** That is the coordinator's reading, flagged to be tested and
   not inherited (RESEARCH-ARC §7): **count the pieces' moduli first.** If each
   piece's own realization space supplies freedom beyond the gauge group — and it
   plausibly does, since the pieces are only required to *attain*, not to sit at
   a specific configuration — then need (2) may **dissolve**, and the lemma
   reduces to need (1) plus bookkeeping. The evidence behind this reading is
   exactly BINDUC's disclosed cap and nothing more; it may well be wrong.

**Already proved — do not re-derive, and note what they leave open.**
`δ₁ = δ₂ = 0`; and **one-rigid-side**, where the criterion collapses to `ρ = δ`
on the other side with **no general position required at all** (biconditional,
296 ear additions). So the genuinely open zone is **both sides non-rigid with
positive `δ`s** — attack that, and use the one-rigid-side case as the model for
what a clean proof looks like.

**What counts as a HIT — state which you got.**

1. **The lemma PROVEN ⇒ (BE-14) PROVEN.** State it plainly and do not decorate
   it. Then stop: the **phase-boundary consequences are the user's call**, not
   yours and not the coordinator's — whether Phase 39 closes, whether a
   successor phase opens for the Lean, and what happens to `hK`/`hcontract` are
   `PHASE-BOUNDARIES.md` events against a standing 2026-07-24 no-split
   adjudication. Report; do not act on them, and do not open a Lean file (the
   standing hold binds regardless of how good the news is).
2. **The strengthened statement PINNED plus partial progress.** A precisely
   written, checked strengthened statement — closed under both compositions,
   true at the three free base classes — is itself a real deliverable even with
   the hard case open, because it is the thing the whole induction recurses on.
3. **An obstruction, located.** The lemma provably fails for some 2-cut class.
   Then: is the failure a **new universal-cap mechanism**? BINDUC's (BE-23)(ii)
   is measured-empty over 25 270 forced-flat instances, and BZAVOID's (BE-15)(ii)
   is proved only for the **triangle**-forced mechanism (scope-corrected
   2026-08-26 — read the bordered note at (BE-15)(ii), not the headline), so a
   genuine new cap is live in a way it was not two commits ago. Report as a
   candidate, never as a refutation; classification mandatory.
4. **An honest OPEN with the route priced** — and, since this lemma *is*
   (BE-14), an assessment of whether the connectivity induction is the right
   frame at all, or whether the `∃`-seed + repair alternative (whose chartless
   wall nothing has lowered) becomes competitive again.

**Bounded secondary deliverable, if and only if it is cheap.** BINDUC's ranked
successor (2): a **direct point-side proof of the flat law**, removing
(BE-20)(ii)'s inherited (BE-13) *proven-informally* planar body-pin ingredient.
This matters more than it did before, because (BE-20) is now **load-bearing for
the whole base**, so an informal ingredient sits under the free part of the
induction. BINDUC calls it "a small, self-contained target". Take it only if it
does not compete with the primary; skip it explicitly if it does.

**Bars.** **Do not inherit BZAVOID's `− 6`** — REFUTED (BE-21); the exact law is
`def₃(G) = max(g₁+g₂, f₁+f₂−6)`. **Do not over-rely on (BE-15)(ii)**: its
cap-free closure covers the **triangle**-forced mechanism only. Do not
re-attempt the routes closed by BZAVOID ((BE-15) triangle cap, the `G²`/molecule
apparatus (BE-17), the transversality count (BE-16)(iv)) or by ZJACOB (the
Jacobian/singular-locus route and, per (JC-6), **any** route deriving properness
from a codimension count, a Jacobian criterion, or Cohen–Macaulayness —
§(K-jac) answers those before they start). Do not scaffold on
`Graph.minimal_kdof_reduction`: its conclusion cannot reach `∀ G`, and its
`hcontract` is a **sibling** of the phase's parked item, not the same obligation
(the spec that called them byte-for-byte was wrong — BINDUC's correction, and
the phase's is strictly stronger). Do not attack `hK`, (GR-15), class
uniformity, or §(K-grid)'s ledger. Do not touch W4 / `hcontract`. **No `.lean`**
— the standing 2026-08-05 Lean hold, which binds even on a HIT shape 1.

**Riders.** TERMINATION E1/E2/E3 at the return (**E3 ARMED by GBAL** — report,
never fire). **F11:** a driver per headline sentence; a *criterion* claim needs a
driver that tests the biconditional, not one direction of it. **F27:** multi-seed
any shortfall claim — rank is lower semicontinuous, and this namespace has been
bitten twice (BATTAIN, BZAVOID). **F25:** state your verification bar off the
shipped driver; every script you run is committed; cap disclosure mandatory, and
**disclose explicitly whether any dimension count in your argument is an
obstruction proof or only a count** — that distinction is what (BE-22)(v) got
right and is the single most likely place for this slice to overclaim. Exact ℚ,
seeded, degeneracy-guarded; `notes/scripts/README.md` binds. The `kbare/`
sibling-import set is recorded UNPAID debt, now with three `w4/` consumers and a
three-deep `battain → bzavoid → binduc` chain — extend the list, make no move.

**Driver — expected, at the pinned path `notes/scripts/w4/btwocut.py`.** Extend
`w4/binduc.py`'s `twocut`/`rank2`/`ear` modes by read-only import rather than
reimplementing the gluing machinery.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BTWOCUT"): §(K-bare-ext) **extends**, no new section; labels
**(BE-25)–(BE-29)**, **Steps BE24–BE28**; return any unconsumed remainder.

### BTWOCUT — landing write-up (LANDED 2026-08-26, recon-opus, one serial coordinator commit)

**Verdict: HIT shape 2, delivered in full — the strengthened statement PINNED
with its design decision made and priced. (BE-14) is NOT proved.** `hbareSplit`,
`PencilPair` and (BE-14)-for-all-`G` untouched; **not a PENCIL event**. Two
landed claims corrected, both with successors in hand.

**Job 1, the crux, is done — and it splits into a free half and the whole
difficulty.** **(BE-25)(i)**: BINDUC's disclosed cap 9 — *does one configuration
satisfy attainment and welded attainment at every cut pair simultaneously?* — is
**VACUOUS**. Every quantity in play (the body-hinge rank, `dim M(G/π)`, `ρ_{uv}`,
`dim(ρ̄₁+ρ̄₂)`) is the rank of a matrix **polynomial in the configuration**, hence
lower semicontinuous, hence maximal on a dense open subset of an irreducible
component; a **finite intersection of dense opens is dense open**, so at the
generic point they are **all simultaneously maximal**. Coordinator-verified: the
argument is standard and correct. **What genericity does NOT give is that those
maxima equal the combinatorial caps — that is the entire content**, and recording
the distinction means the induction never again has to argue that two good
configurations can be chosen at once.

**The design decision, made with both shapes checked against all three
criteria.** **S-all** (*for every pair `{u,v}`, `ρ_{uv} = δ_{uv}`*) implies
(BE-14) immediately and is free at the base — but is **NOT self-closing**.
**S-mark** (*relative to a **rooted** 3-block / SPQR tree, one marked pair per
subtree*) **closes**, because each subtree attaches at exactly one separation
pair. **The decision: S-mark is the shape the induction should carry; S-all is
the shape the evidence is about.** The price is stated rather than hidden — the
motive then carries **a tree and a marked pair, not just a graph**.

**A new elementary theorem makes S-mark's leaf base free.** **A 3-connected graph
minus one edge still has `def₂ = def₃ = 0`** — one line past (BE-20)(i):
`d_G(P) ≥ ⌈3q/2⌉`, so deleting an edge gives `d_H ≥ ⌈3q/2⌉ − 1`, and both forms
come out `≤ −1 < 0` for `q ≥ 2`. **EXHAUSTIVE at 19 696 (3-connected `B`, edge
`uv`) leaf blocks, zero with `def > 0`, bound measured tight at `−1`.**
Coordinator-verified by hand in both forms (`−1` at even `q`, `−2` at odd for the
`def₂` form; `−3q/2−1` and `(−3q−7)/2` for the `def₃` form). The direction
**discloses that this is not independent evidence about the flexible case** — the
leaf block minus its virtual edge is rigid, so it is base 1's argument confirmed,
not extended.

**Job 2: the coordinator's reading is borne out on everything measured — and the
direction refuses to overclaim it.** The spec asked whether BINDUC's
general-position obstruction was real, given that its own cap (BE-22)(v)
disclosed the pieces' moduli were **uncounted**. Counted: side moduli with the
shared flags **held fixed** run **4–26** against the gauge group's 7/5 (hardest
rows 18/18 and 24/24 free), and **16/16 splits reach
`dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)`**. The obstruction hunt fires **empty at
13 484/13 484** both-`δ`-positive instances — exhaustive at `n = 5,6` plus
sampled **both-sides-hubbed** at `n = 7,8,9`. **So the need as posed dissolves,
and the *reading* behind (BE-22)(v) is refuted: the gauge group was never the
right place to look.** But the disclosure the spec demanded is given squarely:
**no dimension count in the draft is an obstruction proof** — the moduli count is
a **lower bound on one constructor's own parameters** and cannot establish
transversality in either direction, so **(BE-22)(v) is left standing as a
count**. Every attainment is an exact-ℚ **per-graph theorem**; every non-hit is
*"not found under this constructor"*.

**BINDUC's 56 `cube+ear` misses are REFUTED — and its own cap called it.** BINDUC
disclosed them (cap 10) as *constructor* caps needing a concurrent plane
arrangement "not attempted". Built: the mechanism is exact — `flat_config`
flattens the ear's **pencil-unconstrained interior**, capping `ρ ≤ dim Λ²π = 3` —
and under a `hubflat` rung **296/296 now attain**. Exemplar `cube+ear(m=4)`: flat
`64/66` with `ρ₂ = 3 < δ₂ = 5`; hubflat **`66/66`, `ρ₂ = 5 = δ₂`**. The fix is
the **ear's own moduli**; the general-position half was never involved. This is
BINDUC's ranked successor (3) — the concurrent-plane rung — **built, not proved**.

**The induction's one genuinely-new obligation, located and named: CROSS-PAIR
closure.** **(BE-28)(i)**: for a cross pair `x ∈ V₁∖{u,v}`, `y ∈ V₂∖{u,v}`,
`G/xy` is **not decomposable at `{u,v}`** — the merged vertex is adjacent to both
sides, so `{u,v}` stops being a separator — hence **neither the (BE-21) `def₃`
law nor the (BE-22)(i) fibre-product law applies**, and S-all's closure obligation
at cross pairs has **no composition law behind it**. Same-side pairs are
unaffected (bookkeeping). **This is S-all's whole cost, and it is why S-mark
exists.** Measured true at **13/13** battery graphs (21–91 pairs each) and
**1 200/1 200** census instances, cross pairs included, zero violations — with
two independent deficiency oracles cross-checked at **408 080** (graph, pair)
instances, zero mismatches. **Reported as measured with no argument**, which is
what keeps S-all live rather than dead.

**What remains, and it is now one geometric sentence.** The 2-cut step itself is
**unproved**: it reduces to *the image of a piece's realization space in
`Gr(δ₂,6)` is not contained in `ρ̄₁`'s bad locus*. The direction calls this **the
first genuinely geometric obligation the arc has reached**, and that reading is
right — every prior residual was combinatorial, rank-arithmetic, or a route
question.

**Coordinator verification.** Full-figure re-run beyond `validate` (117 s):
`spqr` (**19 696 / 0**, 403 s, bound tight at `−1`, plus 6 721/6 721 carrying S1),
`earfix` (**296/296**, with the exemplar's flat-vs-hubflat contrast reproduced
exactly), `moduli` (**16/16**, and the mode prints its own obstruction-proof
disclaimer). `crosspair` + `hunt` were re-run to completion. **Both new arguments
were re-derived independently by the coordinator** — the `G−e` bound in both
forms and at both parities, and the semicontinuity argument (rank lower
semicontinuous ⇒ each max locus dense open ⇒ finite intersection dense open).

**F25 bar, read off the shipped driver:** eight modes, foreground with explicit
timeouts, exact ℚ throughout, `binduc` imported **read-only**, every RNG seeded,
and an explicit **F27 escalation protocol** — one cheap draw per instance, then
*only the residuals* multi-seeded — which is the correct shape given rank
semicontinuity and which this namespace has twice been bitten for missing.
**Caps disclosed**, the load-bearing ones being that no dimension count is an
obstruction proof, that `spqr`'s S1 evidence is not independent of base 1, and
that the cross-pair claim has no argument. The bounded secondary (a direct
point-side flat law) was **declined explicitly** as competing with the primary —
the disposition the spec asked for.

**TERMINATION: E1 NO, E2 NO** — two landed claims corrected, both with successors
in hand, which is the shape E2 does not fire on; coordinator-re-run and agreed.
**E3 ARMED by GBAL, not fired.**

## BIMAGE — forty-fifth ordinal, the fifty-third direction (single dispatch, prepped 2026-08-27)

**Selection provenance: FORCED for the second consecutive direction, and now
strictly geometric.** BTWOCUT closed every remaining layer of the strengthened
2-cut composition lemma but one and named the residue exactly — *the image of a
piece's realization space in `Gr(δ₂,6)` is not contained in `ρ̄₁`'s bad locus* —
and this direction is **BTWOCUT's own ranked successor (1)**, taken in the
restriction BTWOCUT itself recommended (the **ear** case first). Proving it
proves the 2-cut lemma, which proves **(BE-14)**, which discharges
**`hbareSplit`** *and* **`PencilPair`'s unconditional second conjunct** as a
standalone theorem. The user's standing max-impact criterion (2026-08-26, tenth
check-in) selects it with nothing above it to rank. Dispatched **un-named,
single**, at **`recon-opus`** — **fable is unavailable this session** (check-in
2026-08-27), so opus is the mapped-rung substitute and **no rung was conserved
by choice**.

**Ranked and NOT chosen — the twelfth's disclosure IS engaged this time**, since
unlike BTWOCUT there were alternatives:

- **BTWOCUT's successor (2)** — a *proof* that the bundle / concurrent-plane
  construction attains wherever the generic-plane ladder does not, turning
  (BE-29)(ii) from a rung into a theorem and reaching `DZ` and
  `spider(5,5,5)+c`. Real value, but it strengthens a **constructor**, not the
  lemma. **Offered below as job 3, cheap-only.**
- **BTWOCUT's successor (3)** — cross-pair closure ((BE-28)(i)). It buys the
  simpler **S-all** frame and retires the rooted tree from the motive; but
  **S-mark is PINNED and closes**, so this is motive economy, not progress on
  the target.
- **BTWOCUT's successor (4)** — the direct point-side proof of the flat law.
  **Do not take it**, and note that `notes/Phase39.md`'s *"unclaimed and still
  small"* was **STALE**: BTWOCUT priced it and it is **not** cheap (it needs a
  planar body-pin rank derivation from scratch). Corrected in the phase note in
  this same prep commit.
- **(BE-23)(ii)** (*forced flat ⇒ `def₂ = def₃`*) — the disproof side's
  highest-value single search, and the thing that would restore (BE-15)'s
  cap-free closure in full. **Ranked next** if this direction returns an honest
  OPEN.
- **The (K-res) scoping slice** — the user's own 2026-08-26 choice, now
  **deferred a SECOND round** by the same max-impact directive that deferred it
  the first. Recorded as a deferral, **not** a drop; taken under the standing
  pick delegation and disclosed here *because* it is a second deferral of a
  user-selected item.
- **(ZH-2) stratified** — the Zheng lane's one remaining dispatchable candidate.
  The lane is a **standing second lane**, not a per-round obligation, and it does
  not out-rank the last lemma of (BE-14).

**The target, stated exactly as BTWOCUT left it.** For a 2-cut `{u,v}` with
pieces `G₁, G₂` **both attaining**, (BE-22)(iii) gives

> attainment of `G` ⟺ `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)`.

Fix `ρ̄₁ ∈ Gr(δ₁, 6)`. Its **bad locus**

> `B(ρ̄₁) := { W ∈ Gr(δ₂,6) : dim(ρ̄₁ + W) < min(δ₁+δ₂,6) }`
> `        = { W ∈ Gr(δ₂,6) : dim(ρ̄₁ ∩ W) > max(0, δ₁+δ₂−6) }`

is a **Schubert variety — proper and Zariski-closed** in `Gr(δ₂,6)`. The whole
remaining obligation is

> **`ρ̄₂( Y°(G₂; flags at u,v) ) ⊄ B(ρ̄₁)`**,

at the *same* irreducible component whose generic point (BE-25)(i) already makes
every other quantity simultaneously maximal, and with `ρ̄₁` itself ranging over
`G₁`'s own realizations. **Nothing in the arc bounds that image** — (BE-27)
measures it and says so explicitly.

**Job 1 (PRIMARY) — the ear case, which BTWOCUT ranked first because it is
already written down.** When `G₂` is an **ear** (a path `u = w₀, w₁, …,
w_{m+1} = v` of `m` interior degree-2 vertices), the workbook already records
`ρ̄₂ = ⟨ℓ₁, …, ℓ_{m+1}⟩` — the **span of the path's hinge lines** — with
`ℓ₁ ∈ Π_u`, `ℓ_{m+1} ∈ Π_v` and the rest free ((BE-26)'s exemplar exhibits it).
In the (BE-16) point model (`p : V → P³`, hinge of `xy` the join `p_x ∨ p_y`,
pencil condition ⟺ every closed star coplanar) the interior points are the only
moduli, and (BE-27)(i)'s count reads `3m − 2` here — which reproduces the
measured `7` at `K₄ + ear(3)` exactly. **So the ear case is a fully explicit,
finite-dimensional question and it is the one to settle first.** State the answer
as a theorem or as a located obstruction; do not leave it as a measurement.

**Job 2 — what `ρ̄₂` is for a piece that is NOT an ear, or a proof that no such
description exists.** This is the bridge from job 1 to the lemma (BE-14)
actually needs, and it is where the direction earns its rung. The obvious
candidate upper bound is the intersection over `u–v` paths of the path spans;
whether it is an equality, and whether the pencil condition is what makes it one,
is open as far as the coordinator can see. **A negative here is a real result:**
if `ρ̄₂` admits no hinge-line description off the ear, say so plainly and the
route to (BE-14) through job 1 is priced accordingly.

**COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (RESEARCH-ARC §7).**
*Provenance, named as the rule requires:* derived by the coordinator at
dispatch time from (BE-26)'s own `Λ²π` argument plus the standard Klein-quadric
dictionary, **not** measured, **not** found in either workbook by a coordinator
grep, and resting on **no** stratum of this arc's evidence. It may be false,
vacuous, or already implicit. The hypothesis: in Plücker coordinates on
`Λ²K⁴ ≅ K⁶`, job 1's data is a **chain on the Klein quadric** — each `ℓ_i` is a
quadric point, **consecutive** ones are conjugate (they share `p_i`, and two
lines meet iff their Plücker points are conjugate), **non-consecutive** ones are
unconstrained, and each **end** line ranges over the pencil at its flag, which is
a **line ruled on the quadric**. If that is right, job 1 becomes: *can the span
of such a chain meet a fixed `δ₁`-subspace in the minimum dimension?* — a
classical question with no graph theory left in it. **Test it before using it**
(the cheapest falsification is the `δ₂ ≤ #edges of the shortest `u–v` path`
consequence, which is one driver run against BTWOCUT's own `moduli`/`hunt`
batteries); report it as refuted, confirmed, or vacuous, and **do not let it
frame the answer if it fails.**

**Job 3 — BTWOCUT's successor (2), CHEAP-ONLY.** A proof that the bundle /
concurrent-plane construction attains wherever the generic-plane ladder does
not. Take it only if job 1 closes early; **skip it explicitly** if it competes,
exactly as BTWOCUT skipped its own secondary.

**What counts as a HIT — state which you got.**

1. **The image statement PROVEN in general ⇒ the 2-cut lemma ⇒ (BE-14) PROVEN.**
   State it plainly, undecorated. Then **stop**: the phase-boundary consequences
   are the **USER's** call — whether Phase 39 closes, whether a successor phase
   opens for the Lean, what happens to `hK` / `hcontract` — a
   `PHASE-BOUNDARIES.md` event against the standing 2026-07-24 no-split
   adjudication. Report; do not act; **do not open a `.lean` file** (the
   2026-08-05 hold binds regardless of how good the news is).
2. **The ear case PROVEN, the general case reduced.** A theorem for ear pieces
   plus an exact statement of what the general piece needs is a real deliverable:
   ears are the extremal flexible pieces (`δ` grows with the path), and by
   (BE-22)(vi) the one-rigid-side case is already free, so ear-vs-flexible is
   most of the open zone.
3. **An obstruction, located.** The image *is* contained in a bad locus for some
   2-cut class. Then classify, **mandatorily**: is this a failure of the 2-cut
   step only (re-shape the induction), of (BE-14) (the disproof side, and then
   whether it is a new universal-cap mechanism in (BE-23)(ii)'s sense), or of the
   **conjecture**? Report as a **candidate**, never as a refutation, and read the
   direction-A pivot rule in `notes/Phase39.md` *Current state* before writing
   the classification.
4. **An honest OPEN with the route priced** — including whether the connectivity
   induction is still the right frame, or whether the `∃`-seed + repair
   alternative (whose chartless wall nothing has lowered) becomes competitive.

**Bars.**

- **ZJACOB (JC-6) binds hardest on this direction of any so far, and it is the
  single most likely place to overclaim.** No route may derive properness,
  generic smoothness, or transversality from a **codimension count**, a
  **Jacobian criterion**, or **Cohen–Macaulayness**. A non-containment argument
  that reduces to "the image has dimension `≥` the bad locus's codimension" is
  exactly the barred shape. **Every dimension count you write must be labelled
  as a count and not an obstruction proof**, per (BE-27)(i)/(ii)'s own
  discipline.
- **Do not re-run the gauge-group count.** (BE-27)(ii) refuted the *reading*
  that the residual gauge group (dim 7 adjacent / 5 non-adjacent) is where
  general position must come from — *"the gauge group was never the right place
  to look"*. The freedom is the **piece's own moduli**.
- **Do not re-derive settled BTWOCUT results:** (BE-25)(i) simultaneity
  **VACUOUS**; (BE-25)(ii) **S-mark PINNED** as the induction's shape (do not
  re-litigate S-all vs S-mark); (BE-25)(iii)/(iv) both bases **FREE**; (BE-26)
  the ear misses **cleared**; (BE-29) the hunt **empty at 13 484/13 484**.
  Extend these; do not repeat them.
- **Do not inherit BZAVOID's `− 6`** (REFUTED; the law is
  `def₃(G) = max(g₁+g₂, f₁+f₂−6)`), and **do not over-rely on (BE-15)(ii)** —
  cap-free for the **triangle** mechanism only.
- **ZSHEAR:** `Q(r̃) ≠ 0` is `PGL(4)`-invariant, so **no gauge-fixing can supply
  it** — a second, independent reason not to look to the gauge group.
- **Closed routes, do not re-attempt:** the `G²`/molecule apparatus ((BE-17),
  its general-position gate is the *literal negation* of the pencil condition),
  the transversality/dimension count ((BE-16)(iv)), the Jacobian/singular-locus
  package (§(K-jac)).
- **Do not scaffold on `Graph.minimal_kdof_reduction`** — its conclusion cannot
  reach `∀ G`, and its `hcontract` is a **sibling** of the phase's parked item,
  not the same obligation (BINDUC's correction, §(K-bare-ext) *Step BE21*).
- **Out of scope entirely:** `hK`, (GR-15), class uniformity, §(K-grid)'s
  ledger, W4 / `hcontract`, and **any `.lean`** (standing 2026-08-05 hold).

**Riders.** **TERMINATION E1/E2/E3** at the return (**E3 is ARMED by GBAL** —
report, never fire). **F11:** a driver per headline sentence; an *"every" /
"exhaustive" / "the only"* claim needs a driver that **enumerates**. **F27:**
multi-seed any shortfall claim — rank is lower semicontinuous and this namespace
has been bitten twice (BATTAIN, BZAVOID). **F25:** state your verification bar
off the **shipped** driver; every script you run is committed
(`notes/scripts/README.md` binds; §4 convention 8's cap-disclosure rule is
harness-wide); exact ℚ, seeded with printed literals, degeneracy-guarded via
`binduc.assert_generic_star` + `kbare_common.verify_pencil_witness`. **Cap
disclosure mandatory** — *"not found under cap C"*, never *"does not exist"*.
The `kbare/` sibling-import set is recorded **UNPAID** debt with three `w4/`
consumers and a four-deep `battain → bzavoid → binduc → btwocut` chain:
**extend the recorded list, make no move.**

**Driver — expected, at the pinned path `notes/scripts/w4/bimage.py`.** Extend
`w4/btwocut.py` (and through it `w4/binduc.py`) by **read-only import** rather
than reimplementing the gluing, deficiency-oracle or pencil-witness machinery.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BIMAGE"): §(K-bare-ext) **extends**, no new section; labels **(BE-30)–(BE-34)**,
***Steps BE29–BE33***; return any unconsumed remainder.

### BIMAGE — landing write-up (LANDED 2026-08-27, recon-opus, one serial coordinator commit)

**Verdict: strictly between HIT shapes 2 and 4, and the direction refused to
round it up.** Not shape 1 ((BE-14) not proved), not shape 2 in full (the ear
case is **reduced**, not **proved**), not shape 3 (the hunt fires empty after
escalation). `PencilPair K 3 G`, `hbareSplit` and (BE-14)-for-all-`G` are
untouched; **not a PENCIL event**. Reservation **fully consumed** —
**(BE-30)–(BE-34)**, *Steps BE29–BE33*, nothing returned.

**The headline is a refutation of a standing sentence of BTWOCUT's own.**
*"Nothing in the arc bounds that image"* is now false for the ear:
`ρ̄₂ = ⟨ℓ₁,…,ℓ_{m+1}⟩` with **equality** (a path is a tree, so the edge
multipliers are free — two lines, and checked as an identity of *subspaces*, not
dimensions, at 44/44 draws), and the achievable tuples are **exactly** the
chains with `ℓ₁ ∈ Π_u`, `ℓ_{m+1} ∈ Π_v` and consecutive members conjugate.
Coordinator-verified: both directions of the bijection are elementary and
correct.

**The coordinator's Klein-chain hypothesis: CONFIRMED, and stronger than it
claimed** — a bijection, not an inclusion. Per RESEARCH-ARC §7 the spec shipped
it labelled *to be tested, not inherited*, with its provenance named and its
cheapest falsification specified; the direction tested it rather than assuming
it, **proved** the falsification consequence (`δ₂ ≤` shortest-path length, tight
on the ear for `m ≤ 5`) instead of merely confirming it, and returned the
**correction the hypothesis does not predict**: at small `m` the two ends
interact, giving three exact **confinement laws** — at `π_u = π_v` with `m = 2`
the image collapses to a **single point** of `Gr(3,6)`. This is the fifth
consecutive coordinator prediction the direction it primed has *tested*; unlike
the four before it, this one survived.

**Job 2 answered positively, and the coordinator's other candidate REFUTED.**
`ρ̄` obeys an exact **series/parallel recursion** — series **sums**, parallel
**intersects**, both proved by elementary gluing and verified as subspace
identities — so a hinge-line description exists for **every series-parallel
piece** down its SPQR tree. The spec's *"obvious candidate upper bound is the
intersection over `u–v` paths"* is a genuine bound but **NOT an equality**,
refuted by an exact witness (`θ(3,3)` + pendant edge: `1` against `2`), because
intersection does not distribute over sum. Coordinator-re-derived: the witness
is right and the arithmetic is forced.

**Three elementary combinatorial theorems, each one merge inequality.**
`u ~ v ⇒ δ_{uv} ≤ 1`; a common **triangle** `⇒ δ_{uv} = 0`; **`≥ 3` common
neighbours** `⇒ δ_{uv} = 0`. Coordinator-re-derived all three independently from
the merge identity `value = f − 6k + 5c` — they are correct. They matter because
they are exactly the two mechanisms that **force `π_u = π_v`** (BZAVOID's
triangle propagation, BINDUC's `K_{2,3}` generalization), so wherever the
sharpest confinement is *forced*, that piece has `δ = 0` and (BE-22)(vi) makes
the composition free: **the obstruction and the deficiency are in tension**, the
same shape (BE-15) found on the disproof side. Swept over **542 893**
`(graph, pair)` instances, **exhaustive** at `n ≤ 6` (27 474 graphs / 408 080
pairs), zero violations across five predicates — including the purely
combinatorial necessary condition **`δ_{uv} ≤ dist(u,v)`** for S-all/S-mark,
which is the arc's cheapest falsification test and **fires empty**.

**The bad locus, classified — and the cap that governs the whole landing.**
Three mechanisms: **pencil swallowing**, **confinement**, and the `m = 1`
**opposite ruling**. Each is a **proved** lower bound on the loss, resting on a
proved **α-plane escape lemma** (`Bad(B)` is at most a point for `dim B ≤ 4`, at
most a line for `dim B = 5`) which the coordinator re-derived from the Klein
form. **That the loss is EXACTLY their maximum is MEASURED at 358/358, not
proved** — the direction names this its headline cap and requires it to travel
with the figure. The one open sub-step is named precisely: the greedy's last
choice of `p_m ∈ π_v` must satisfy two conditions in a 2-parameter family.

**Every trap a real piece shows is a configuration artifact.** 934 predicted
trapped `(piece, m)` pairs over a census subsample; 682 have `π_u = π_v` *chosen
by the constructor* rather than forced — the same shape as BINDUC's 56 ear
misses — 230 forced, 22 genuinely geometric. Rebuilt as composed graphs with
side 1 free to move: **607/607 reach the criterion and the whole-graph target**.
And 43/43 real `G₁ ∪ ear(m)` instances reach `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)` **by
moving the ear alone**, at `δ₁` up to 6.

**One gate-invisible defect, caught in coordinator verification and fixed before
landing.** The draft twice wrote that the SP recursion's residue is *"the
R-node, which (BE-25)(iii) already makes rigid after removing its parent virtual
edge"*, and the shipped driver printed the same sentence. **(BE-25)(iii) closes
the LEAF R-node only** — BTWOCUT's own consequence line reads *"every SPQR
**leaf** 3-block is rigid"* — where the piece **is** the skeleton minus its
parent virtual edge, so `ρ̄ = 0` and the recursion terminates. An **internal**
R-node, with flexible children substituted for its virtual edges, is not covered
and is not rigid at all: `K₄` with one virtual edge replaced by an ear **is**
BINDUC's `K₄ + ear(m)`, `δ ∈ {4,5}`. The clause read as closing what the
direction's **own ranked successor (3)** is queued to open. Corrected in the
workbook and in the driver's printed prose, and `sprec` re-run. Logged
(`notes/dispatch-log.md`).

**Coordinator verification.** `validate` re-run to completion (the escalation
reproducing 73/73 at the reduced tier), then the full tiers of `sprec`, `chain`,
`alpha` and `combi` — the last reproducing **542 893** instances and all five
zero-violation columns exactly. **Both new arguments were re-derived
independently by the coordinator**: the three merge-inequality theorems (all
three cases, including the third-part contradiction) and the α-plane escape
lemma from the Klein form. The `θ(3,3)`+pendant witness was checked by hand
(`3 + 3` intersecting to `0`, against two `4`s intersecting to `2`).

**F25 bar, read off the shipped driver:** nine modes, one per headline sentence;
every *"every"/"always"/"exactly"* sentence backed by an **enumerating** tier;
every subspace claim an identity of **spaces**, never of dimensions; exact ℚ
throughout with no GF(p) and no floating point; every rng seeded with a printed
literal; every configuration passing `assert_generic_star` **and**
`verify_pencil_witness`. **Ten caps disclosed**, the load-bearing three being
the measured exactness, the measured *"no real piece produces a bad `ρ̄₁`"*, and
the twice-subsampled census. **Procedural slip, disclosed by the direction
itself:** one driver run auto-backgrounded for a missing explicit `timeout`; it
was re-run in the foreground and every quoted figure comes from a foreground
run (dispatch-log **F6**, seventh instance).

**Ranked successors, this pass's own order.** (1) *a piece satisfying the
strengthened statement admits a configuration with `Π_u ⊄ ρ̄₁`, `Π_v ⊄ ρ̄₁`* —
with (2) it **proves the ear case outright**, and the SP recursion is the tool;
(2) the greedy's last step — self-contained projective geometry, the smallest
item in the arc's queue; (3) the **internal R-node**, the step from ear to
general piece; (4) BTWOCUT's successor (2), the bundle proof, **skipped here
explicitly** as the spec authorizes.

**TERMINATION: E1 NO, E2 NO** — one coordinator candidate and one landed
sentence refuted, both with successors in hand, which is the shape E2 does not
fire on; coordinator-re-run and agreed. **E3 ARMED by GBAL, not fired.**

## BEARCASE — forty-sixth ordinal, the fifty-fourth direction (single dispatch, prepped 2026-08-27)

**Selection provenance: FORCED for the THIRD consecutive direction.** BIMAGE
reduced the ear case of the strengthened 2-cut lemma to **exactly two** open
items and ranked them (1) and (2); it says in terms that together they **prove
the ear case outright**. There is nothing above them to rank, and the user's
standing max-impact criterion (2026-08-26, tenth check-in) selects them.
Dispatched **un-named, single**, at **`recon-opus`** — fable unavailable this
session (check-in 2026-08-27), so opus is the mapped-rung substitute.

**Disclosed, because it is now a pattern and not an accident: this is the
SEVENTH consecutive direction in §(K-bare-ext).** The standing *diversification*
criterion was minted to correct the arc's §(K-grid) concentration and now reads
against this namespace instead. It is being **overridden deliberately, by the
max-impact criterion that supersedes it**: (BE-14) discharges **two of the three
carried items** and nothing else on the board is within a direction of a proof.
**Unpicked and named, so the concentration stays visible:** the **(K-res)
scoping slice** (a user-selected item, now deferred a **THIRD** round);
**(ZH-2) stratified**, the Zheng lane's one dispatchable candidate; and
**(BE-23)(ii)**, the disproof side's highest-value single search. **BIMAGE's
successor (3)** (the internal R-node) and **(4)** (BTWOCUT's bundle proof) are
ranked below this direction only because they do not close anything on their
own.

**The target — the two items, stated exactly as BIMAGE left them.**

> **(α) The greedy's last step.** (BE-33)(i)'s α-plane escape lemma runs the
> chain greedily through every **interior** vertex of the ear. It does **not**
> close the **final** choice: `p_m` must lie in the 2-parameter plane `π_v` and
> satisfy **two** conditions at once — `ℓ_m ∉ W_{m−1}` **and** `ℓ_{m+1} ∉ W_m`.
> BIMAGE characterizes the bad case (it forces
> `⟨x,y⟩ ∧ (p_v + λ p_{m−1}) ⊆ W_{m−1}` for some `λ`) and does **not** rule it
> out. **Closing (α) turns (BE-33)(ii)'s reach formula from MEASURED (358/358)
> to PROVED**, which is the landing's headline cap.
>
> **(β) The `ρ̄₁` non-containment.** *A piece satisfying the strengthened
> statement admits a configuration with `Π_u ⊄ ρ̄₁`, `Π_v ⊄ ρ̄₁` and
> `dim(ρ̄₁ ∩ Z) ≤ dim Z − c₂`.* This is a statement about **ONE piece and its
> own moduli**, not about two pieces in relative position — which is what makes
> it tractable, and it is the same simplification (BE-22)(vi) exploited.
>
> **[SPEC DEFECT, recorded in place 2026-08-27 — the dispatch refuted it.** The
> third clause is unsatisfiable at `δ₁ ≥ 5` by plain Grassmann; the coordinator
> transcribed it verbatim from BIMAGE's ranked successor (1) without checking
> its arithmetic, and it reached the phase note's hand-off too. The correct
> target is `loss ≤ max(0, δ₁+δ₂−6)`. See (BE-36).**]**

**Job 1 — (α).** Self-contained projective geometry, no graph theory; BIMAGE
calls it **the smallest item in the arc's queue**. Take it first: it is the
cheaper of the two and it converts a measured headline into a proved one.

**Job 2 — (β), the substantial half.** The **SP recursion (BE-31) is the tool
the direction that minted (β) names**: for a series-parallel `G₁`, `ρ̄₁` is
computed from its own hinge lines down the SPQR tree, so (β) becomes a statement
about **sums and intersections of chain spans** — the same objects job 1 works
with, which is why the two belong in one direction.

**Job 3 — the generalization, ONLY if jobs 1 and 2 both close.** State and, if
it is cheap, prove the ear case's successor: **the same non-containment for an
arbitrary series-parallel piece on the other side**, via the recursion. The ear
is the all-`S` case; `S`+`P` is the natural next frontier and would leave the
**internal R-node** as the single named residue of the whole 2-cut lemma. **Skip
it explicitly** if it competes with jobs 1–2, exactly as BIMAGE skipped its own
secondary.

**Coordinator-verified observations — use them, they are not predictions.**

1. **The `δ₁ = 6` corner is VACUOUS, and (β) must be stated with that carve-out.**
   If `δ₁ = 6` then `ρ̄₁ = K⁶`, so `Π_u ⊆ ρ̄₁` necessarily — but then
   `dim(ρ̄₁+ρ̄₂) = 6 = min(δ₁+δ₂,6)` and the criterion is **already met**. Read
   off `bimage.py hunt`'s own output, which flags exactly this (*"the `Pi_u <=
   rho_1` column includes the VACUOUS hits rho_1 = 6"*). Any sweep for a
   counterexample to (β) that counts those rows is counting non-instances.
2. **What the criterion actually demands, in two regimes.** With
   `dim ρ̄ᵢ = δᵢ`: at `δ₁ + δ₂ ≤ 6` it is `ρ̄₁ ∩ ρ̄₂ = 0`; at `δ₁ + δ₂ > 6` it is
   `dim(ρ̄₁ ∩ ρ̄₂) = δ₁ + δ₂ − 6` exactly. The second regime is the one `C₁₀` /
   `C₁₂` at antipodes live in (`δ = (5,5)`, `(6,6)`), and both are **measured
   attaining** — the extremal rows of BTWOCUT's `rank2` table.
3. **`ρ̄₁` and `ρ̄₂` are never in naive general position at the cut, and this is
   structural.** The pencil condition at `u` constrains the **whole** closed
   neighbourhood, both sides at once, so when a side is path-like its first
   hinge at `u` lies in `Π_u` — hence each of `ρ̄₁ ∩ Π_u`, `ρ̄₂ ∩ Π_u` is
   generically a *line* of the 2-dimensional `Π_u`. Two distinct lines of a
   2-space span it and meet only at `0`, so this forces **no** intersection —
   but it is why (P), *pencil swallowing*, is the classification's first
   mechanism, and it is worth having stated rather than rediscovered.
   **Scope caveat, measured:** this is a claim about **path-like** sides only —
   `bimage.py hunt` reports `ρ̄₁ ∩ Π_u = 0` at 15 of 80 subspaces, so it is
   **false in general** and must not be assumed for an arbitrary `G₁`.

**COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (RESEARCH-ARC §7).**
*Provenance:* the coordinator's reading of a **pattern** across two landed
results — (BE-32)(ii)/(iii) (the mechanisms that *force* `π_u = π_v` also force
`δ = 0`) and (BE-15) on the disproof side (forcing confines each class to a
local cone and thereby forces `def₂ = 0`). It rests on **no measurement of its
own**. The hypothesis: **(β) is true for the same reason, by a tension argument**
— that a piece whose *every* configuration has `Π_u ⊆ ρ̄₁` is thereby forced
into a regime where the criterion is vacuous or the strengthened statement
fails, so the obstruction and the deficiency cannot coexist. If that tension is
real, (β) is proved by the (BE-32) method rather than by a genericity argument.
**It may well be false**, and the honest alternative is that (β) needs the
piece's moduli directly. **Test it; do not let it frame a negative result.**

**The falsification arm — commissioned, and it is the standing positive
criterion.** Hunt for a piece that satisfies the strengthened statement and has
`Π_u ⊆ ρ̄₁` (or the (Z)/(R) variant) at **EVERY** configuration with the given
flags — not at one drawn configuration. BIMAGE's 607/607 escalation is
**measured over the BTWOCUT ladder's configurations**, which is exactly the cap
(BE-26) caught BINDUC on: a constructor artifact reads as a trap. So the
question this direction must answer is the one escalation cannot: **is the
trapped set empty as a matter of the piece, or only of the constructor?** A
genuine witness here would be the first real candidate for a new universal cap
since (BE-23)(ii) and **must be classified against it**.

**What counts as a HIT — state which you got.**

1. **(α) and (β) both proved ⇒ THE EAR CASE PROVED.** The arc's first *proved*
   case of the strengthened 2-cut lemma. State it plainly; report the
   phase-boundary question and **do not act on it** (the user's call; the
   2026-08-05 Lean hold binds regardless).
2. **One of the two proved.** (α) alone turns the reach formula from measured to
   proved — a real deliverable on its own, and the cheaper one.
3. **An obstruction, located** — (β) fails for some piece class. Classify
   **mandatorily**: 2-cut step only, (BE-14), or the conjecture; candidate,
   never refutation; read the direction-A pivot rule in `notes/Phase39.md`
   *Current state* before writing it.
4. **An honest OPEN with the route priced**, including whether the ear case is
   the right first target at all or whether the internal R-node (successor (3))
   should have gone first.

**Bars.**

- **ZJACOB (JC-6) still binds hardest.** No properness, generic smoothness or
  transversality from a **codimension count**, a **Jacobian criterion**, or
  **Cohen–Macaulayness**. (β) is exactly the kind of statement that invites a
  dimension count; **label every count as a count**, per (BE-27)(i)/(ii) and
  (BE-33)(ii)'s own discipline.
- **Do not re-derive BIMAGE's settled results:** (BE-30) the chain bijection and
  the three confinement laws; (BE-31) the SP recursion (and note **(BE-25)(iii)
  closes the LEAF R-node only** — the internal one is not rigid, `K₄ + ear(m)`
  is one); (BE-32) the three merge-inequality theorems; (BE-33)(i) the α-plane
  escape lemma; (BE-34) the hunt and escalation. **Extend these; do not repeat
  them.**
- **Do not re-run the gauge-group count** ((BE-27)(ii): *the gauge group was
  never the right place to look*), and **do not re-open S-all vs S-mark**
  ((BE-25)(ii): S-mark **PINNED**).
- **Do not inherit BZAVOID's `− 6`** (REFUTED), and **(BE-15)(ii)** is cap-free
  for the **triangle** mechanism only.
- **Closed routes:** the `G²`/molecule apparatus ((BE-17)), the
  transversality/dimension count ((BE-16)(iv)), the Jacobian/singular-locus
  package (§(K-jac)), and — ZSHEAR — anything expecting **gauge-fixing** to
  supply a `PGL(4)`-invariant.
- **Out of scope entirely:** `hK`, (GR-15), class uniformity, §(K-grid)'s
  ledger, W4 / `hcontract`, and **any `.lean`** (standing 2026-08-05 hold).

**Riders.** **TERMINATION E1/E2/E3** at the return (**E3 ARMED by GBAL** —
report, never fire). **F11:** a driver per headline sentence; an
*"every"/"exhaustive"/"the only"* claim needs a driver that **enumerates** — and
note that (β) quantifies over **every configuration of a piece**, which no
sampler enumerates, so a claim there is **measured** unless you have an
argument. **F27:** multi-seed any shortfall claim. **F25:** state your
verification bar off the **shipped** driver; every script committed
(`notes/scripts/README.md` binds); exact ℚ, seeded with printed literals,
degeneracy-guarded via `assert_generic_star` + `verify_pencil_witness`. **Cap
disclosure mandatory.** The `kbare/` sibling-import set is recorded **UNPAID**
debt, the chain now **five deep** (`battain → bzavoid → binduc → btwocut →
bimage`): **extend the recorded list, make no move.**

**Driver — expected, at the pinned path `notes/scripts/w4/bearcase.py`.** Extend
`w4/bimage.py` (and through it `btwocut` / `binduc`) by **read-only import**;
its `chain`, `sprec`, `alpha` and `badA` modes already build every object jobs 1
and 2 need.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BEARCASE"): §(K-bare-ext) **extends**, no new section; labels
**(BE-35)–(BE-39)**, ***Steps BE34–BE38***; return any unconsumed remainder.

### BEARCASE — landing write-up (LANDED 2026-08-27, recon-opus, one serial coordinator commit)

**Verdict: HIT shape 2 — one of the two proved, and it is (α).** `PencilPair
K 3 G`, `hbareSplit`, (BE-14)-for-all-`G` and the 2-cut step are all untouched;
**not a PENCIL event**. Reservation **partly returned** for the first time in
this namespace: **(BE-35)–(BE-38)** and *Steps BE34–BE37* consumed, **(BE-39)**
and ***Step BE38*** returned unconsumed.

**(α) is closed, and the mechanism is a REORDERING rather than a new tool.** The
last step's two conditions collapse to one — `⟨ℓ_m, ℓ_{m+1}⟩` is the pencil
`p_m ∧ M` — giving **the 2-step lemma (BE-35)(i)**: the reach of `W + c∧M` is
determined by `dim(W ∩ N_M)` alone, with an exceptional `S_t` clause at
`dim = 3`. Coordinator-verified in full: I re-derived the quadratic form
coefficient by coefficient against the draft's `Q(a)` and it **matches exactly**,
and checked the `dim C ≤ 2` union-of-`T_t` count and the converse. The
proof's case split is complete, though it does not spell out why
`c_{02}, c_{03}` cannot be dependent-and-nonzero — that sub-case forces the
image into a line and contradicts surjectivity, which I verified separately.
BIMAGE's bad case is then shown **non-empty but a condition on the SCHEDULE**,
not on `A` — so (α) is a question about the **order of the greedy's choices**,
and is answered by changing it: pick both constrained ends first (**the end-pair
lemma (BE-35)(iii)**, four cases in the quotient `Z/(A∩Z)` — coordinator-verified
including the *"same line"* case, which needs `Z = Π_u + Π_v` and gets it), close
with a point **free in `P³`**, and **slide** two points along fixed lines so `M`
sweeps a 2-parameter transversal family against a `≤ 1`-parameter bad set.
**⟹ the reach formula is PROVED for `m ≥ 3`** — BIMAGE's headline cap,
discharged — with the `m ≤ 2` corners decided separately and **no fourth
mechanism** found at 1 067 targeted instances.

**(β) as stated is REFUTED, and the defect was the COORDINATOR'S to catch.**
`dim(ρ̄₁ ∩ Z) ≥ δ₁ + dim Z − 6` always, so the demanded `≤ dim Z − 2` is
**unsatisfiable at `δ₁ ≥ 5`**, `dim Z` cancelling. This is one line of Grassmann.
It originated in BIMAGE's own ranked successor (1), and the coordinator
transcribed it **verbatim** into `notes/Phase39.md`'s hand-off item 1 and into
this direction's spec without checking its arithmetic — so the dispatch was sent
to prove a false statement, and found that out itself. **No measurement changes**:
the correct target `loss ≤ max(0, δ₁+δ₂−6)` is exactly what the landed
`bimage.py hunt` already tests. Corrected at all four landed sites in this
commit — the workbook's successor ranking, the spec (annotated **in place**, not
silently rewritten), and both phase-note sites. Logged (`notes/dispatch-log.md`).

**The quantifier collapse — the answer to the spec's own job-2 note, and it
needed a hypothesis the draft omitted.** *"At every configuration"* ⟺ *"at a
generic configuration"*, so a sampler can **over-report** traps but **never miss
one**, and one drawn configuration with `loss ≤ slack` is a **theorem for that
piece**. The draft justified this by *"a difference of lower-semicontinuous rank
functions is upper semicontinuous"*, which is **false in general** — coordinator
witness: `V(t) = ⟨(1,0,0),(0,t,0)⟩`, `X = ⟨(0,1,0)⟩` gives `dim(V ∩ X) = 1`
generically and `0` at `t = 0`. It is true exactly where **`dim ρ̄₁` is
constant** — the **attaining** locus, which is where (β) is posed and where all
three consequences live. The hypothesis was supplied at landing; **no conclusion
changes**.

**Two genuinely new class-level results on the (β) side.** The reduction to
three generic-position statements holds in **87 of 91** arithmetic cases, the
four failures being exactly the `π_u = π_v`, `m = 2` corner where the ear has no
freedom at all; and a piece with **`dist_{G₁}(u,v) ≤ 4` has `loss = 0` for every
ear length**, stated with its genericity proviso rather than without.

**The falsification arm answered BIMAGE's cap 3 head-on.** BIMAGE's 607/607 was
measured over the **BTWOCUT ladder's** configurations — the same shape (BE-26)
caught BINDUC on. This direction built a sampler that **owes the ladder nothing**:
by (BE-16) the pencil condition is *every closed star coplanar*, so subdivisions
whose branch vertices form an independent set have a **free parametrization** of
the stratum. Over 24 pieces × 14 generic draws — including **R-node** pieces
(subdivided `K₄`, `K_{3,3}`, prism), which is BIMAGE's own named residue —
**ZERO candidates**, with `Π_u ⊆ ρ̄₁` occurring at *exactly* the vacuous
`ρ₁ = 6` rows, **asserted** rather than eyeballed. The coordinator's observation 3
is reproduced on that independent sampler and **sharpened**: the intersection is
`1` for path-like sides, `0` where two `u–v` paths leave `u` differently, and
never `2` below `ρ₁ = 6`.

**The coordinator's hypothesis was decided NEGATIVE, and cleanly.** The
(BE-32)-style *tension* argument is **not** the mechanism: `δ₂ = min(m+1,6) ≥ 2`
always covers the deficit, so (β) reduces to plain generic position with no
tension needed. Tension survives only at the residue the direction lands on —
**(BE-32)(+)**. Fifth of the last seven coordinator predictions to be decided by
the direction it primed; the second to be decided negative.

**Coordinator verification.** `validate` re-run to completion (117 s), then the
**full** tiers of `twostep` (2 205 comparisons, 14/14 enumerated shapes),
`betadim`, `greedy` (1 432/1 432, every first attempt) and `corners` (1 067/1 067)
— all reproducing exactly. The `betadim` forced minima were checked against my
own independent Grassmann table, row for row. **Three arguments re-derived
independently**: the 2-step lemma's quadratic form, the end-pair lemma's four
cases, and the (β) refutation.

**F25 bar, read off the shipped driver:** eight modes, exact ℚ throughout, every
rng seeded with a printed literal, every subspace claim an identity of spaces;
the `laststep` criterion is **decided, not sampled** (a quadratic form on a
3-space vanishes identically iff it vanishes at three basis vectors and their
three pairwise sums, so the six-point test is a decision procedure); the
`betahunt` sampler **asserts** its chosen plane equals `plane_at`'s closed-star
plane. **Caps disclosed**, the load-bearing ones being that `m ≤ 2` is proved
*given a skew optimal end pair*, that `m ≥ 6` is argued rather than measured,
and that the independent sampler **excludes pieces with adjacent branch
vertices** — which the direction itself names as where it would look next for a
counterexample.

**Ranked successors, this pass's own order.** (1) **(BE-32)(+) as a theorem** —
the single named residue, and two of its mechanisms are already
(BE-32)(ii)/(iii); (2) **(b2)** for a general piece; (3) the **internal R-node**,
now with a free sampler in hand; (4) BTWOCUT's bundle proof, still skipped.

**TERMINATION: E1 NO, E2 NO** — one landed prose sentence corrected with its
successor already in the landed driver, which is the shape E2 does not fire on;
the ear case **narrows** rather than dying. **E3 ARMED by GBAL, not fired.**

## BEARFULL — forty-seventh ordinal, the fifty-fifth direction (single dispatch, prepped 2026-08-27)

**Selection provenance: the ear case's last two items, plus a ROUTING question
the coordinator is putting up deliberately.** BEARCASE closed (α) and left the
(β) side with exactly two open items — its own ranked successors (1) and (2) —
so jobs 1 and 2 are forced in the same way the last two directions were.
**Job 3 is not forced**: it is a coordinator-raised routing question that could
re-rank the board, and it is raised now precisely because the information the
S-all/S-mark pin was made on has changed. Dispatched **un-named, single**, at
**`recon-opus`** (fable unavailable this session).

**Disclosed: EIGHTH consecutive direction in §(K-bare-ext), and the (K-res)
scoping slice is now deferred a FOURTH round.** That slice is a **user-selected**
item (2026-08-26, chosen over the full wave and over a re-deferral). The
coordinator is scheduling it rather than deferring it indefinitely: **it is the
next dispatch after this one**, and this is recorded in `notes/Phase39.md`'s
hand-off, not just here. Also unpicked: **(ZH-2) stratified** and
**(BE-23)(ii)**.

**Job 1 (PRIMARY) — (BE-32)(+) as a theorem.** *A graph that forces
`π_u = π_v` has `δ_{uv} = 0`.* It is the **single named residue** of the ear
case on the (β) side. Status: **MEASURED** at 208 418 instances under the
**aggressive** plane-class closure (which over-claims forcing, so an empty sweep
is the stronger statement — but it is not an argument). **Two of its three
mechanisms are already theorems** — (BE-32)(ii) a common triangle, (BE-32)(iii)
`≥ 3` common neighbours — both by the **merge inequality**
`value = f − 6k + 5c`, which is four lines. The task is the rest: either extend
the merge argument to the aggressive closure's general forcing rule, or exhibit
a graph that forces `π_u = π_v` with `δ_{uv} > 0`. **State the closure operator
you are proving it for** — "forced" is only meaningful relative to one, and the
measured predicate is the aggressive one.

**Job 2 — (b2) for a general piece**, BEARCASE's successor (2): the middle
clause of (BE-37)(ii)'s reduction, at a piece that is not covered by
(BE-38)(ii)'s `dist_{G₁}(u,v) ≤ 4` transfer. With job 1 this **completes the ear
case's (β) side**, and with (α) already closed that is **the ear case, proved**.

**Job 3 — THE ROUTING QUESTION, and it is the reason this spec lifts one of its
own predecessors' bars.** BEARCASE's spec said *"do not re-open S-all vs
S-mark"*. **That bar is lifted for this job only**, and the reason is stated
rather than assumed: BTWOCUT pinned **S-mark** because S-all's cross-pair gap
had *"no composition law behind it"* while S-mark *"closes"* — a correct call
**on the information then available**, when the ear case was unproved and the
general piece and the ear looked comparably hard. **BEARCASE changed that
information**: the ear case is now one or two items from proved, while the
general piece (the **internal R-node**, successor (3)) is untouched.

> **COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (RESEARCH-ARC §7).**
> *Provenance:* the coordinator's own reading, formed at this dispatch, resting
> on **no measurement and no workbook result**; a `grep` confirms the arc has
> **never** considered it (0 hits for "ear decomposition" across the workbooks).
> It is new, and therefore more likely wrong than the usual.
>
> **The hypothesis: the ear case may already BE the induction step.** Every
> 2-connected graph has an **open ear decomposition** starting from a cycle
> (classical; **verify the attribution against a primary source before writing
> it into the workbook** — do not assert a section number). (BE-18) already
> reduces (BE-14) to 2-connected graphs, and a cycle is `max degree ≤ 2`, which
> is one of the **free** base classes ((BE-25)(iv)). Each ear addition attaches
> a path at a pair `{u,v}` — i.e. **exactly the 2-cut composition with `G₂` an
> ear and `G₁` arbitrary**, which is the case BEARCASE has nearly proved. If
> that goes through, the **internal R-node is not needed at all** and successor
> (3) leaves the critical path.
>
> **Two gaps the coordinator already sees, stated so they are not discovered as
> surprises:** **(i) CHORDS.** An open ear decomposition admits **single-edge**
> ears, and a chord addition is **not** a 2-cut composition (`{u,v}` is not a
> separator). `K₄` needs one, so this is unavoidable, and the ear route needs
> its own edge-addition step. **(ii) WHICH strengthened statement.** The
> attachment pair varies along the decomposition, so the induction needs the
> welding clause at the *next* ear's pair — which is neither S-mark (a rooted
> tree) nor obviously S-all (every pair). It may be a **third** shape, marked by
> the decomposition rather than by a tree; whether *that* is self-closing is the
> real question, and if it needs S-all then **cross-pair closure ((BE-28)(i))
> becomes the binding obligation** and jumps from "motive economy" to the top of
> the board.
>
> **Report a verdict on the route, not a preference.** If the ear route does not
> work, say so and why — that is worth as much as a yes, because it **confirms**
> S-mark and retires a coordinator distraction.

**What counts as a HIT — state which you got.**

1. **The EAR CASE PROVED** (jobs 1 and 2 both closed). The arc's first proved
   case of the strengthened 2-cut lemma. Report the phase-boundary question and
   **do not act on it**; the 2026-08-05 Lean hold binds regardless.
2. **One of jobs 1 and 2 proved**, with the other reduced.
3. **A routing verdict on job 3** that re-ranks the board — in either direction.
   A clean NO is a real deliverable.
4. **An obstruction, located** — job 1 fails, i.e. a graph forcing `π_u = π_v`
   with `δ_{uv} > 0`. Classify **mandatorily** (ear case / 2-cut step / (BE-14)
   / the conjecture); candidate, never refutation; read the direction-A pivot
   rule in `notes/Phase39.md` *Current state* first.

**Bars.**

- **ZJACOB (JC-6)** — no properness, generic smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness; **label every
  dimension count as a count**.
- **Do not re-derive BEARCASE's settled results:** (BE-35) the 2-step lemma, the
  end-pair lemma, the reordering-and-slide, the `m ≤ 2` corners; (BE-36) — and
  note **(β) as originally stated is REFUTED**, the correct target being
  `loss ≤ max(0, δ₁+δ₂−6)`, which the landed driver already tests; (BE-37)(i)
  the quantifier collapse, **which holds on the ATTAINING locus** (the general
  semicontinuity claim is false — the corrected statement is in the workbook,
  read it); (BE-38) the transfer and the independent sampler.
- **Do not re-derive BIMAGE's or BTWOCUT's settled results** ((BE-30)–(BE-34),
  (BE-25)–(BE-29)); **(BE-25)(iii) closes the LEAF R-node only**.
- **Closed routes:** the `G²`/molecule apparatus ((BE-17)), the
  transversality/dimension count ((BE-16)(iv)), §(K-jac)'s package, and
  gauge-fixing as a source of a `PGL(4)`-invariant (ZSHEAR). **Do not re-run the
  gauge-group count** ((BE-27)(ii)).
- **The S-all/S-mark bar is lifted for JOB 3 ONLY** — and only as a *routing*
  question. Do not re-litigate (BE-25)(ii)'s reasoning on the information it
  had; it was right then.
- **Out of scope:** `hK`, (GR-15), class uniformity, §(K-grid)'s ledger, W4 /
  `hcontract`, and **any `.lean`** (2026-08-05 hold).

**Riders.** **TERMINATION E1/E2/E3** (**E3 ARMED by GBAL** — report, never fire).
**F11:** a driver per headline sentence; *"every"/"forced"/"the only"* needs a
driver that **enumerates**, and job 1's *"forced"* is a claim about a **closure
operator** — name it and test that one. **F27:** multi-seed any shortfall claim.
**F25:** verification bar off the **shipped** driver; every script committed;
exact ℚ, seeded with printed literals, degeneracy-guarded. **Cap disclosure
mandatory.** **Citation discipline is live this time** (job 3 reaches for a
classical theorem): verify author/year against a primary source, and write
*"classical"* without a section number rather than guess one — `CLAUDE.md`
*Referencing prior work*. The `kbare/` chain is **six deep**: extend the
recorded consumer list, **make no move**.

**Driver — expected, at the pinned path `notes/scripts/w4/bearfull.py`.** Extend
`w4/bearcase.py` (and through it `bimage`/`btwocut`/`binduc`) by **read-only
import**; job 1 wants `bearcase`'s combinatorial layer and `binduc`'s
`def_by_partitions`, job 3 wants an ear-decomposition generator that does not
exist yet.

**Reservation** (`notes/Pencil-labels.md` §"Reserved namespace — direction
BEARFULL"): §(K-bare-ext) **extends**, no new section; labels
**(BE-39)–(BE-43)**, ***Steps BE38–BE42***; **(BE-39)** and ***Step BE38*** are
the tail BEARCASE returned unconsumed. Return any unconsumed remainder.

### BEARFULL — landing write-up (LANDED 2026-08-27, recon-opus, one serial coordinator commit)

**Verdict: HIT shape 3 — a routing verdict that re-ranks the board, and it is a
clean NO — carrying shape 2's job-2 half outright.** `PencilPair K 3 G`,
`hbareSplit`, (BE-14)-for-all-`G`, the 2-cut step and S-mark are all untouched;
**not a PENCIL event**. Reservation **fully consumed**, nothing returned:
**(BE-39)–(BE-43)**, *Steps BE38–BE42*; tail now **(BE-44) / Step BE43**.

**THE COORDINATOR'S ROUTING HYPOTHESIS IS REFUTED — by a one-line theorem, which
is the best possible outcome for a labelled guess.** The spec asked whether an
open ear decomposition makes the ear case *itself* the induction step, retiring
the internal R-node. Answer: **no**, and the chord gap the spec flagged as (i)
turns out to be **fatal and located exactly at the R-nodes it was meant to
retire**. **(BE-43)(i):** in a **chord-free** open ear decomposition the last ear
receives no later attachment, so its interior vertices have degree exactly 2 —
hence **chord-free ⟹ `G` has a degree-2 vertex**, i.e. **every minimum-degree-`≥ 3`
graph, every 3-connected block, every R-node forces a single-edge ear in EVERY
open ear decomposition**. Coordinator-verified by hand, and its counting shadow
(`m ≤ 2n − girth`) checked to be **strictly weaker** — it excludes `K₄` but not
the prism, which the theorem does. Swept: **2 084 3-connected graphs, ZERO
chord-free**. **S-mark's pin stands, for a NEW reason** — not because S-all's
cross-pair gap is unclosed (it still is) but because the ear route does not
escape it and **adds a second gap**, both localising at the R-node.

**Two partition-lattice laws the arc had never extracted, and they are the
landing's real content.** **(BE-39)(i), the quotient sparsity law:** merging *any*
set `S` of parts of an optimal partition is a competitor, so
`5 e_Q(S) ≤ 6(|S|−1)` — giving `Q` **simple** and **`girth(Q) ≥ 6`**, with the
6-cycle **tight**. **(BE-39)(ii), the join lemma:** `g` is **supermodular** on the
partition lattice, so optimal partitions are closed under join, there is a unique
coarsest `P_max`, and **`δ_uv = 0 ⟺ u,v` share a block of `P_max`** — i.e.
**`δ = 0` is an EQUIVALENCE RELATION**. Coordinator-verified: I re-derived the
sparsity law from the merge inequality (the `|S| = 2…6` table reproduces exactly,
including the tight 6-cycle) and checked both halves of the supermodularity
argument, including the `#components ≥ #vertices − #edges` count on the
block-intersection bipartite graph.

**The SHORT-CYCLE LAW, which contains two landed theorems and weakens one.**
A cycle's crossing edges form a closed walk of **distinct** `Q`-edges, hence an
even subgraph, hence contain a `Q`-cycle of length `≥ 6`: **crossings are `0` or
`≥ 6`**, so **every cycle of length `≤ 6` forces `δ = 0`**, and
`δ ≤ max(0, L−6)` in general — **strictly better than (BE-32)(iv)'s `δ ≤ dist`
for every `L ≤ 11`**. (BE-32)(ii) is the `L = 3` case; **(BE-32)(iii) is `L = 4`
and its hypothesis WEAKENS from `≥ 3` to `≥ 2` common neighbours** (61 770
newly-covered pairs, 0 with `δ ≠ 0`). Nothing is refuted — a landed theorem is
**strengthened**. Coordinator-verified including (iii)'s `k ≤ r` step (a closed
walk of length `r` visits at most `r` vertices).

**Job 1: MEASURED → PROVED at 96.2 %, with the boundary EXACT rather than
guessed.** The closure operator is **named** (`bimage.forced_same_plane`, the
aggressive one, which over-claims forcing — so a theorem for it holds a
fortiori). **401 489 of 401 544** forcing steps and **196 043 of 203 723** forced
pairs are proved with no measurement, including **100 % of the exhaustive
`n ≤ 6` tier** — every SPREAD step appears only in the sampled tiers. The residue
is one geometry-free statement, and the boundary is not an artifact: **a 7-cycle
of `Q` has slack `−1`**, so the merge inequality provably cannot pass 6, and a
named triangle-chain family exhibits genuine spread steps at cycle length 7 and 8
(with `δ = 0` at every member anyway).

**Job 2 is discharged outright, in one line.** `Π_u ⊆ Z`, so
`dim(ρ̄₁∩Z) ≤ dim Z − 2 + min(dim(ρ̄₁∩Π_u), dim(ρ̄₁∩Π_v))` — the same cancellation
(BE-36) used to refute (β) as stated. Hence **(b1) ⟹ (b2)** at `δ₁ ≥ 5`, and
`ρ̄₁ ∩ Π_u = 0` at either end gives it at every `δ₁`. **(b2) stops being an
independent clause**, so the ear case's (β) side is down to **one**.

**Citation discipline, which this spec put live.** Whitney, *Non-separable and
planar graphs*, Trans. Amer. Math. Soc. **34** (1932), no. 2, 339–362 — author,
year, title, journal, volume and pages verified against the AMS primary listing,
and the theorem written as **classical with no section number asserted**, which
is what `CLAUDE.md` asks for when a pointer cannot be verified. The coordinator
deliberately asserted no pointer in the spec.

**Coordinator verification.** `validate` re-run to completion (346 s at the
reduced tier), then the **full** tiers of `merge`, `cycles`, `forced` and
`eardec` — every figure reproducing exactly, including the girth histogram
(`forest: 28 572, 6: 61`) and the 0-SPREAD-steps-at-`n ≤ 6` column that makes the
96.2 % claim honest. **Three arguments re-derived independently**: the sparsity
law's `|S|`-table, the ear-decomposition degree-2 theorem with its counting
shadow, and the short-cycle bound's `k ≤ r` step.

**F25 bar, read off the shipped driver:** eight modes; every mode `assert`s its
proved laws so a violation stops the run; `optimal_partitions` cross-checks its
lattice enumeration against `exact_deficiency`'s packing oracle **on every
call**; `def3_fast` cross-checks `def3_multi` against `exact_deficiency` at every
`|V| ≤ 13` call; `forcing_derivation` **asserts** it reproduces
`forced_same_plane`'s pair set exactly. **Ten caps disclosed**, the load-bearing
one being that (BE-41)(ii) reads *"no escape found under this cap"*, never *"none
exists"*. **Self-disclosed loose end:** a more extreme spread-step probe at
`n = 21` was built in scratch and **did not complete** (recursion depth and a
`2²¹` subset table); it is **not** in the shipped driver and backs no claim.

**Ranked successors, this pass's own order.** (1) **(b1) sharpened to
`ρ̄₁ ∩ Π_u = 0`**, which now discharges two of the three clauses at once;
(2) the **spread step**, the last 3.8 % of (BE-32)(+) — pure graph theory, 55
known instances, and the merge inequality is *known* not to reach it; (3) the
**internal R-node**, which job 3 **confirms** on the critical path, now with a
local alternative coordinate (the **chord step**, whose combinatorial half
(BE-43)(ii) is already free); (4) BTWOCUT's bundle proof, still skipped.

**TERMINATION: E1 NO, E2 NO** — a landed hypothesis is weakened and a landed
bound improved, which is the strengthening shape E2 does not fire on.
**E3 ARMED by GBAL, not fired.**

## RESGRID — forty-eighth ordinal, the fifty-sixth direction (single dispatch, prepped 2026-08-28)

**Selection provenance: a USER-SELECTED item, deferred four rounds, committed to
this slot at the BEARFULL prep.** On 2026-08-26 the user was offered the full
(K-res) wave, this cheap scoping slice, or a re-deferral, and chose the
**scoping slice**; the coordinator then bound it to the next slot rather than
let a fifth max-impact pick displace it. Dispatched **un-named, single**, at
**`recon-fable`** — all rungs are available this session, and the verdict prices
a **carried item** and either grounds or corrects a standing claim of the
phase's **status object**, which is the playbook's top-rung trigger.

**THIS IS A SCOPING SLICE, NOT THE WAVE — and the distinction is the spec.**
`notes/Pencil-strategy.md` §8's board prices the (K-res) attack as *"wave-sized;
a user call"*, and **it stays a user call**. This direction does **not** attack
(K-res). Its entire job is to determine **what attacking it would cost**, by
auditing whether §(K-grid) — the arc's largest single body of work, 14 924
lines, *Steps G0–G148*, (GR-1)–(GR-128) — is **reusable** on the (K-res)
habitat or has to be rebuilt from the colouring layer up.

**The question, in one sentence:** *does (GR-15)/§(K-grid) transport to the
`W19`-type (K-res) habitat?*

### Four coordinator-verified facts, each read out of a named file at prep time

Stated so the dispatch **checks** them rather than re-derives them; if one is
wrong, say so — that is a finding, not a detour.

1. **(K-res) is `hK`'s statement verbatim with one hypothesis swapped.**
   `notes/Pencil-W4-informal.md` §"widened kernels (routes 1/3)" *Step 4*: the
   minimal honest form is `hK`'s statement with **`hnoRigid` ↦
   `PencilNondegFeasible K G`**. Same conclusion object, **disjoint** habitats,
   and route 3 packaging (b) carries it as a *byte-identical sibling*. So the
   transport question is **entirely about the proof route** and never about the
   statement — and that same section already says which piece of the route dies:
   *"the (K) stratification's cheap branch"* (*Step 2*).
2. **§(K-grid) is scoped to the TIGHT stratum, explicitly and in its own
   title** — *"the tight-stratum grid residual"* — and **(GR-15) quantifies over
   "every tight class shape"** (gap map, (K-grid) *what would close it*). A
   (K-res) member is **not** a tight class member: §(K-pure) says exactly that
   of `P21` (*"a (K-res) residual, not a tight class member"*), and (AC-6)
   records `W19` as *"rigid but **not count-tight**"*.
3. **The gap map already ASSERTS the transport, without a proof, and that
   sentence is what is under test.** The *State of (K)* map's own arc paragraph
   (`notes/Pencil-informal.md`) says (K-tight) *"since the W4 route-3(b)
   adjudication also carries the whole **(K-res)** residual habitat … same
   difficulty class, same stratum, **so one uniform gap serves both**"*. But the
   chain then reduced (K-tight)'s residual to a gap **quantified over tight
   class shapes**. If fact 2 bites, the umbrella claim and the reduction have
   quietly come apart and **the phase's status object is wrong** — in which case
   `RESEARCH-ARC.md` §3's corollary binds: a map correction is presumptively a
   **body-prose** correction too, so grep the whole file for the same claim
   rather than fixing the row alone.
4. **The habitat numbers are already on file, and they are why transport is
   plausible rather than obviously false.** `notes/Pencil-W4-informal.md`
   §"widened kernels" *Step 5*: `W19` and `S29` both `s₀ = 2`,
   `corank(G′) = 3`, **`dim R_a = 1`**, **8/8** escaping seeds each; the pencil
   rank target attained **108/108** at `W19` and **168/168** at `S29`. And
   (AC-6)'s grid recipe **reached the target at `W19`, 1/1**. So (K-res) sits in
   the **same hard `dim R_a = 1` stratum** §(K-grid) attacks, and the one
   colouring-layer datum that exists there is positive.

### Job 1 (PRIMARY, FORCED) — the hypothesis audit, and it is the deliverable

Walk the chain from **(AC-6)** through **(GR-15)** and on through the
post-(GR-15) reductions — **(GR-16)** the branch reduction, **(GR-17)** the
circuit run law, **(GR-18)** the 6-tree packing, **(GR-19)** the collapse-order-4
certificate — and as far beyond as the later steps actually bear on the
transport. For **each named result**, record exactly which of these it consumes:

> **count-tightness** · **`s₀ = 0`** · **`hnoRigid`** (vs (K-res)'s
> `PencilNondegFeasible`) · **both chain ends hubs** · **2-connectivity** ·
> **`corank(G′) = 1`** (vs (K-res)'s `3`) · **`def = 0`**

**Deliverable: one table, one row per named result, three verdicts only** —
**TRANSPORTS** (the proof never touches the swapped hypothesis),
**TRANSPORTS-WITH-A-NAMED-REPAIR** (state the repair and price it), **BREAKS**
(state the first step that fails and *why*, not that it "might"). A row you
cannot decide is its own verdict — mark it **UNDECIDED** and say what would
decide it; an undecided row honestly marked is worth more than a guessed one.

**Do not re-derive the results themselves.** They are settled; this is an audit
of their *hypotheses*. Cite each by label and step number.

### Job 2 (FORCED) — name the (K-res) residual

From job 1's table, state **(K-res)'s own grid residual** exactly, in one of
three shapes, and say which:

- **(GR-15) verbatim** — the gap really is habitat-uniform, fact 3's umbrella
  claim is grounded, and one gap closes both. Then say **what that does to route
  3's price**: (K-res) stops being a wave and becomes a rider on (GR-15).
- **A strictly stronger sibling** — (GR-15) with its quantifier widened past the
  tight class. Then state the sibling, mint it a label, and say whether the
  §(K-grid) machinery that reduced (GR-15) reduces it too.
- **A genuinely different gap** — the chain breaks before the residual is
  reached. Then name where, and name the (K-res)-side residual that replaces it.

**Whichever it is, the gap map moves**: either (K-tight)'s row/arc paragraph
gains the grounding it currently lacks, or it is **corrected** and (K-res) gets
its own row. Run `python3 notes/check-gapmap-cells.py` before committing any
gap-map edit; a new row is fine, a silently-regrown cell is not.

### Job 3 (NOT FORCED) — the two-shape control

A cheap empirical control, and only if job 1 leaves a row that a measurement
would decide. At the **named** (K-res) shapes — `W19` (`widened.W19`), `S29`
(`saferes.w29`), and `nt21c3` (`dominance`, already labelled *"a (K-res)
shape"*) — does an **(AC-6)-admissible colouring exist** and reach **generic
`dim Z₊ = dim Z₋ = 0` in both blocks**, i.e. the *(GR-15)-shaped* per-shape
check rather than the target-rank check (AC-6) already ran?

**Reuse before you write.** `gridcol.py` / `gridwit.py` / `gridbal_common.py` /
`gexist.py` carry the colouring and `dim Z` layer; `widened.py` and `saferes.py`
build the shapes. **Do NOT run `kslidecomb.shape_ok`** on a (K-res) shape — it
*is* the class predicate (tight count ∧ `def = 0` ∧ `hnoRigid`) and will reject
them by construction; that rejection is the discriminator, not a bug.

### COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md` §7)

> *Provenance:* formed at this prep from the file reads recorded above. It rests
> on **no measurement of its own** and **no workbook result that states it**;
> the arc has never asked the question, because (K-res) has been a **bar** in
> eight consecutive specs and was never a target.
>
> **The hypothesis: the chain transports as far as the colouring layer, and it
> is (GR-15)'s own QUANTIFIER — not the geometry — that has to be restated.**
> Three reasons, each with the stratum its evidence actually comes from:
> **(a)** (AC-6)'s failure mechanism is *bare odd cycle components* and it is
> **complete and proven** (`C3…C14` → exactly `[3,5,7,9,11,13]`); `W19` has 5
> hubs and `S29` has 9, so no hub-carrying (K-res) member can be a bare cycle,
> and the one obstruction the colouring layer is known to have **cannot bite** —
> *stratum: (AC-6)'s own proven parity mechanism, plus the single 1/1 `W19`
> datum*. **(b)** Both habitats sit at `dim R_a = 1` — *stratum: the W4 *Step 5*
> table, **two** shapes*. **(c)** (GR-16)–(GR-19) are stated on `(G°, ℓ, bits)`,
> the **contracted hub multigraph** — a purely combinatorial object that a
> change in `s₀` or `corank` need not touch — *stratum: the statements' own
> form, no measurement*.
>
> **Where the coordinator expects to be wrong, stated up front so it is not
> discovered as a surprise:** count-tightness looks **load-bearing in the
> counting layer** — (GR-3)'s two counting obstructions, (GR-22)'s five caps,
> and above all **(GR-32)'s capacity theorem** (*"the whole graph is exactly
> critical, every proper chunk has one unit of slack"*), which reads like a
> tightness statement wearing another name. If the chain breaks, that is where
> the coordinator expects it. **A clean "does not transport, and here is the
> first step that fails" is worth as much as a yes** — it converts the board's
> (K-res) row from an unpriced *"wave-sized"* into a named gap with a cost.

### What counts as a HIT — state which you got

1. **TRANSPORT PROVEN** — the chain carries and (K-res)'s residual is (GR-15)
   verbatim. One gap then serves both carried obligations; route 3's price drops
   by a wave. Report the consequence for the board, **do not act on it**.
2. **TRANSPORT REFUTED, with the break located** — the first failing step named,
   and (K-res)'s own residual stated. Equally valuable, and it **corrects the
   status object**.
3. **A PARTIAL transport with the surviving fraction measured** — e.g. the
   colouring layer carries, the counting layer does not. State the boundary as a
   *step number*, not as a mood.
4. **An obstruction, located** — something in the audit refutes a landed claim.
   Classify **mandatorily** (§(K-grid)'s own scope / the gap map's umbrella
   claim / (K-res) / `hK` / the conjecture); **candidate, never refutation**;
   read the direction-A pivot rule in `notes/Phase39.md` *Current state* first.

### Bars

- **DO NOT ATTACK (K-res).** Even if the audit finds a clean transport, do not
  then start proving the transported gap — the wave is a **user call** and this
  slice does not pre-empt it. Scope, price, stop.
- **`PencilNondegFeasible` is NOT combinatorially certifiable, and (K-res)'s
  hypothesis IS `PencilNondegFeasible`.** `not_pencilNondegFeasible_of_triangle_two_hubs`
  refutes feasibility propagation as a proposition for **any** purely
  combinatorial (`≤3`-closedHubNbhd) criterion (`notes/Phase39.md` *Blockers*).
  Any repair that proposes to certify the swapped hypothesis combinatorially is
  refuted before it starts — check a candidate repair against this bullet
  **before** writing it down.
- **The counting filters.** **(OC-3)** kills the whole class of counting/matroid
  routes to (OUT)'s hypothesis and **(OC-37)** closes the other direction; §8's
  board carries both as sight-kill filters (growing ground-set; counting
  saturation). Do not propose one as the (K-res) repair.
- **Route σ is NOT a route to (K-res)** — §(K-σ) obligation 2 and the board row
  say so outright (the habitat is *unsampled*, `s₀ = 2`). Do not re-propose it.
- **ZJACOB (JC-6)** — no properness, generic smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness; **label every
  dimension count as a count**.
- **Out of scope:** proving (GR-15) itself; the §(K-bare-ext)/(BE-14) thread
  (eight consecutive directions, deliberately not this one); the W4 **build**;
  and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 is ARMED (by GBAL)**; report, never fire.
**F26** — the consumer is W4 **route 3, branch 4**, and the coordinator has
already traced it (fact 1); do not re-trace it, but do not contradict it either.
**F11** — a driver per headline sentence; *"every" / "transports" / "the only"*
needs a driver that **enumerates**, and job 1's verdicts are **audit** claims,
so their evidence is a **cited step number**, not a measurement — say which is
which per row. **F27** — any *"this shape fails to reach X"* claim needs
multiple independent draws and the return says how many; a positive certificate
needs one. **F25** — verification bar off the **shipped** driver; **every script
committed** (standing 2026-08-05 user requirement); exact ℚ, seeded with printed
literals, degeneracy-guarded. **Cap disclosure MANDATORY** — an exhausted cap is
*"not found under cap C"*, never *"does not exist"*, and the disclosure travels
with the figure. **Read `notes/scripts/README.md` *Harness debt* before any
numerics** (four items outstanding; the §2-rule-2 rule binds: record the item
naming every consumer, do **not** modify the landed file).

### Driver — OPTIONAL, and the spec says so

Job 1 is an audit and may need no new code at all; a prep that forces a driver
onto a reading task buys nothing. **If** job 3 runs, reuse the grid colouring
layer and the residual shape builders by **read-only import** rather than
copying them. If new code is genuinely needed, the pinned path is
**`notes/scripts/w4/resgrid.py`**. If none is written, say so explicitly and
discharge figure invariance the standing way (`git diff --name-only -- '*.py'
'*.m2'` empty **is** the discharge, stated in the commit message).

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction RESGRID".) A **new
section §(K-res)** in `notes/Pencil-informal-grid.md` — that workbook owns
§(K-grid), so colocating the audit minimizes cross-file citation — with tag
**`RS-`**, tokens **(RS-1)–(RS-12)**, ***Steps RS1–RS10***, driver
`notes/scripts/w4/resgrid.py`. `RESGRID`, `resgrid`, `§(K-res)`, `(RS-1)`,
`(RS-2)`, `(RS-9)`, `RS1` and *`Step RS`* each verified **0-hit** as raw
substrings across `*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` at reservation time.
**Return any unconsumed remainder.** Note the deliberate near-miss: `(K-res)`
alone is a **habitat name** with 139 existing hits, so every citation of the new
section must carry its `§` — the §(K-bare-ext)-beside-(K-bare) precedent
exactly. **Checked and NOT chosen:** extending the `GR-` tail (it would mix two
habitats inside one label family, against the registry's qualify-don't-merge
rule) and `RESPORT` (names the hoped-for answer, which is the framing
`RESEARCH-ARC.md` §7 forbids).

### RESGRID — landing write-up (LANDED 2026-08-28, recon-fable, single design-pass commit)

**Verdict: HIT shape 3 — a PARTIAL transport with the boundary a step number,
carrying shape 2's correction of the status object.** `hK`, (GR-15), class
uniformity, E1/E2 untouched; **E3 stays ARMED (by GBAL), not fired**. Canonical
home: **§(K-res)**, `notes/Pencil-informal-grid.md` (end of file), *Steps
RS1–RS10*; driver `notes/scripts/w4/resgrid.py`. Reservation: (RS-1)–(RS-6)
consumed, **(RS-7)–(RS-12) returned**, the M2 leaf never needed.

**The question is answered in both directions at once.** The §(K-grid)
**geometry transports verbatim** — (AC-6)'s recipe and parity mechanism,
(GR-1)'s reduction, (GR-5) chart membership, (GR-7)/(GR-8), (GR-9)'s
vanishing half, (GR-19)'s semicontinuity/monotonicity — because none of those
proofs touches the swapped hypothesis; the **tight bookkeeping does not**:
the first outright failures are **(GR-16)(iv)** (squareness), **(GR-17)(d)**
(the girth-7 binding list) and **(GR-18)(i)** (the 6-tree partition — Nash–
Williams *fails at the core*, `Σ(6−ℓ) = 8 > 6`, driver-asserted), and
everything built on (GR-21)/(GR-22)/(GR-25)/(GR-32) consumes exactly what the
habitat swap removes. Job 1's audit table (*Step RS5*) has **no UNDECIDED
row**: every verdict is a cited proof reading or a driver figure, per F11.

**Four new laws, minted because the audit needed them.** **(RS-1)**
`rank = 6(|V|−1) − dim Z₊ − dim Z₋` at ANY legal both-forest colouring —
(GR-15)'s criterion is habitat-free; **(RS-2)** the slack law
`dim Z = (m − 3h) + dim W`, with the colour split balanced within the index;
**(RS-3)** short cores force a (GR-8) witness (`g ≥ 1`, parameter-free) and
**rigidity always pays for it** (`def ≥ f(W) − index`); **(RS-4)** the
transported discharge through (GR-5)/(AC-7).

**Job 2: the residual is the SECOND of the three offered shapes — a strictly
stronger sibling.** **(RS-5)**: every `def = 0` (K-res) shape admits an
admissible both-forest colouring with generic `dim Z₊ = dim Z₋ = 0` —
(GR-15)'s criterion verbatim, quantifier widened past the tight class,
quantifiers **disjoint**, so **closing (GR-15) does NOT close (RS-5)**. The
gap map's umbrella sentence (*"one uniform gap serves both"*, standing since
2026-08-02) is **corrected**, §(K-res) gets its own gap-map row, and the
(K-tight) row and W4 workbook carry pointer corrections (the F12 grep found
three prose sites; all repaired in this commit).

**Job 3 ran, and it decided the one row citation could not.** Exhaustive
colouring sweeps at all three named shapes: `W19` 28 of 52 passing colourings
at generic `(0,0)`, `S29` 468 of 1 140, `NT21c3` 24 of 54 — and at each an
**exact rational target point** (108/168/120), i.e. **(RS-5) is PROVEN
per-shape at all three** by semicontinuity, the census's own instrument. At
`W19`/`S29` every passing block carries the forced core witness
(`dim W ≥ 1`, asserted combinatorially, measured exactly 1) and reaches
`dim Z = 0` anyway — the index-2 slack absorbs it, exactly as (RS-3) says.
**(RS-6)**: the deficient fringe is refuted with a mechanism — θ(2,3,7)
(`def = 1`, `index = 0`, rigid `C₅` core) is **provably capped at 58 < 59**
at every one of its 4 admissible colourings, retiring §(K-clos) *Z6*'s
recorded miss as a theorem.

**The coordinator hypothesis, scored per `RESEARCH-ARC.md` §7.** Headline
(*"the quantifier, not the geometry"*): **confirmed on the rigid stratum,
refuted on the deficient fringe**. Reason (a) (parity cannot bite):
confirmed. Reason (b) (`dim R_a = 1` kinship): **irrelevant to the grid
route** — `s₀`, `corank(G′)`, `dim R_a` are consumed *nowhere* in §(K-grid)
(escape-side quantities; the grid is split-free), which corrects the prep's
fact-4 framing. Reason (c) ((GR-16)–(GR-19) purely combinatorial, hence
untouched): **refuted** — three of the four break. The expected break
location ((GR-32)) is real but **downstream of the first break**.

**Scope, price, stop — the scoping answer (*Step RS9*).** (K-res) is
**neither a rider on (GR-15) nor a rebuild from the colouring layer up**:
the reduction to (RS-5) is free (geometry + certificate instruments
transport), per-shape checks are cheap and three are banked, the
**uniformity machinery must be rebuilt above the *Step G23* waterline**
(no tight structural law carries), and the deficient members are out of the
grid route's reach entirely. **The wave stays a user call; nothing here
starts it.**

**F25/F27 bar, read off the shipped driver.** Four modes plus `--validate`
(~60 s); every identity **asserted** in-run ((RS-1) at 72 matched draws +
3 exact points + the θ control; (RS-2)=(GR-7) at all 2 492 passing blocks;
the forced witness per block; rigidity-covers-excess per shape); enumeration
**exhaustive** per shape (the 2^20 cap asserted non-binding); the θ
refutation rests on a parameter-free floor plus exhaustive enumeration, not
on draws (F27 satisfied by proof, with 3 draws/colouring corroborating);
seeds printed; the one count cap (24 identity-asserts/shape) disclosed as a
cap on asserts, not enumeration.

**TERMINATION: E1 NO, E2 NO** (a scoping target settled, successor object
named — (RS-5)'s uniform statement, a user call), **E3 ARMED, not fired**.

## BSHARP — forty-ninth ordinal, the fifty-seventh direction (single dispatch, prepped 2026-08-28)

**Selection provenance: BEARFULL's own successor (1), taken under the standing
research-pick delegation on the max-impact criterion.** The ear case's (β) side
is down to **one clause**, and this is it. Dispatched **un-named, single**, at
**`recon-opus`** — the playbook's default for a read-only research recon; RESGRID
took the top rung because it re-priced a carried item and corrected the status
object, and this one does neither.

**Diversification note, and it is a genuine reset rather than a waiver.** This is
§(K-bare-ext)'s **first** direction since RESGRID broke an eight-direction run in
the namespace. Still unpicked and disclosed: **(ZH-2) stratified** (the standing
Zheng second lane) and **(BE-23)(ii)**.

### The target, stated exactly

> **Prove `ρ̄₁ ∩ Π_u = 0`** — (b1) sharpened from `≤ 1` to `0` — at one end of a
> general ear-case piece.

By **(BE-42)(ii)**, *proved*, that single statement discharges **(b1) and (b2)
together**: (b1) ⟹ (b2) outright at `δ₁ ≥ 5`, and **always** from the sharpened
`0`, at **either** end. With **(α)** closed by BEARCASE, the ear case's (β) side
then has only **(b3)** left (*`ρ̄₁ ∩ E` is not an opposite-ruling pencil*).

### What is already free — cite it, do NOT re-derive it

- **(BE-30)(iv)**, proven: `ρ̄₁ ⊆ ⟨ℓ_e : e ∈ P⟩` for **every** `u–v` path `P`.
- **(BE-42)(i)**, proven: the Grassmann bound, exact at every draw, tight at 144.
- **(BE-42)(ii)**, proven: (b1) ⟹ (b2) at `δ₁ ≥ 5`, and always from `0`.
- **(BE-42)(iii)**, the **mechanism, NAMED not proved**: every hinge line at `u`
  lies in `Π_u = p_u ∧ π_u` (closed star coplanar, (BE-16)); `assert_generic_star`
  forbids two hinge lines at a body from coinciding, so **any two hinge lines at
  `u` span `Π_u`**; if two `u–v` paths leave `u` by **different edges** then `ρ̄₁`
  lies in both path spans, whose `Π_u`-parts are **different lines**.
- **(BE-38)(iii)**, measured and asserted: `Π_u ⊆ ρ̄₁` occurs at **exactly** the
  `ρ₁ = 6` vacuous rows and nowhere else.
- **(BE-38)(i)/(ii)**, proven: a path piece has `dim(ρ̄₁ ∩ Π_u) = 1`; and any
  piece with a `u–v` path of length `≤ 4` whose interior lines are generic
  against `Z` has `loss = 0` outright.

### Job 1 (PRIMARY, FORCED) — discharge the genericity proviso, or locate it

The workbook is explicit that **(BE-42)(iii) is a mechanism, not a proof**: the
containment is exact and the two `Π_u`-lines are distinct, but concluding `0`
*"still needs the interior lines to be generic against `Π_u`, and that is
labelled a genericity proviso"*. **That proviso is the whole job.** Either
discharge it — by an argument, on the pencil stratum, at the pieces that need it
— or state exactly what it is and exhibit the configuration where it fails.

**A reduction the coordinator believes the proviso admits, offered as a starting
point and not as a result** (test it first; if it is wrong, say so and proceed
from the mechanism directly): with `P`, `Q` two `u–v` paths leaving `u` by
different edges, (BE-30)(iv) gives
`ρ̄₁ ∩ Π_u ⊆ (⟨ℓ_e : e ∈ P⟩ ∩ Π_u) ∩ (⟨ℓ_e : e ∈ Q⟩ ∩ Π_u)`. Each factor
**contains** the first-edge line and the two first-edge lines are distinct in the
**2-dimensional** `Π_u`, so the intersection is `0` **as soon as each factor is
exactly that one line**. If that is right, the proviso is precisely: *no
combination of `P`'s interior hinge lines enlarges `⟨ℓ_e : e ∈ P⟩ ∩ Π_u` past
`⟨ℓ_{first}⟩`* — a codimension condition on the interior lines, one path at a
time, and **not** a joint condition on the pair. **State whether the reduction
holds** before using it.

### Job 2 (FORCED) — the two coverage questions the mechanism raises

Both are structural, both are cheap, and neither is answered anywhere in the
workbook:

1. **When does the mechanism's own hypothesis fail?** It needs *two `u–v` paths
   leaving `u` by different edges*. A **path piece** has only one `u–v` path, so
   the hypothesis fails there outright — and (BE-38)(i) proves `dim = 1` at a
   path piece, **sharp**, so the sharpening to `0` is **FALSE** there. The honest
   target is therefore a **case split**, not a uniform sharpening. Say so in the
   statement you land.
2. **Does the split already cover everything?** See the coordinator hypothesis
   below.

### Job 3 (NOT FORCED) — the disclosed sampler coverage gap

`bgrass`'s battery inherits bearcase's shape guard (branch vertices an
independent set, each free vertex with at most one branch neighbour), so it is
**subdivisions only** and, in the workbook's own words, *"says nothing about
pieces with adjacent branch vertices"*. If the argument in job 1 is
configuration-sensitive, that is the class to test it on. Reuse `bearfull.py
bgrass`'s parametrization by read-only import; a new shape family is the only
new code this should need.

### COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md` §7)

> *Provenance:* formed at this prep by reading (BE-30)(iv), (BE-38)(i)/(ii),
> (BE-42)(ii)/(iii) and caveat 6 of BEARFULL's *Verification* block. It rests on
> **no measurement of its own** and on **no workbook sentence that states it**.
> Four of the last five coordinator predictions in this arc were refuted or split
> by the direction they primed; price this one the same way.
>
> **The hypothesis: the case split is already complete, so the sharpening is
> needed only at non-path pieces.** At a **path** piece, `ρ̄₁` is a chain, so
> `δ₁` is governed by the same ear formula and `dist ≥ 5` should force
> `δ₁ ≥ 5` — which is exactly (BE-42)(ii)'s **first** branch, needing no
> sharpening; while `dist ≤ 4` is (BE-38)(ii), free. If both hold, **path pieces
> need nothing new**, and job 1's sharpening is required only where the
> mechanism's hypothesis is available anyway. *Evidence stratum:* the ear's own
> reach formula (BE-33)(ii), **proved for `m ≥ 3`** but proved **about the ear**,
> transported here by analogy and **not** by a stated result — that transport is
> the weak link and is where the coordinator expects to be wrong.
>
> **A second, weaker guess, flagged separately because its stratum is different
> again:** (BE-38)(iii)'s *"`Π_u ⊆ ρ̄₁` at exactly the `ρ₁ = 6` rows and nowhere
> else"* is an **asserted** measurement over 24 pieces × 14 draws, and it is the
> `dim = 2` case of the same question job 1 asks at `dim = 1`. If the proviso is
> real it should already be visible as a `dim(ρ̄₁ ∩ Π_u) = 1` row at a piece with
> two paths — `bgrass` reports exactly such rows at `δ₁ = 5`. **Check whether
> those rows are the proviso failing or the vacuous corner** before building an
> argument that would have to explain them away.

### What counts as a HIT — state which you got

1. **`ρ̄₁ ∩ Π_u = 0` PROVED** on its honest domain, with the case split stated.
   That closes **(b1) and (b2)** and leaves the ear case's (β) side at **(b3)**
   alone. Report the consequence for the board; **do not act on it**, and the
   2026-08-05 Lean hold binds regardless.
2. **The proviso reduced to a named, checkable condition** with the reduction
   proved, even if the condition itself stays open.
3. **The case split settled** (job 2) even without job 1 — knowing exactly which
   pieces need the sharpening is a real deliverable.
4. **An obstruction, located** — a piece with two `u–v` paths where
   `dim(ρ̄₁ ∩ Π_u) = 1` genuinely and not vacuously. Classify **mandatorily**
   (the sharpening / (b1) / the ear case / (BE-14) / the conjecture);
   **candidate, never refutation**; read the direction-A pivot rule in
   `notes/Phase39.md` *Current state* first.

### Bars

- **Do not re-derive** (BE-30)(iv), (BE-42)(i)/(ii), (BE-35)–(BE-38), or the
  short-cycle law (BE-39)/(BE-40). Cite them. **(BE-25)(iii) closes the LEAF
  R-node only**; **(β) as originally stated is REFUTED** — the correct target is
  `loss ≤ max(0, δ₁+δ₂−6)`.
- **Closed routes, do not re-open:** the **ear-decomposition induction**
  ((BE-43), refuted by a theorem — every minimum-degree-`≥ 3` graph forces a
  single-edge ear); the `G²` apparatus ((BE-17)); the transversality/dimension
  count ((BE-16)(iv)); gauge-fixing as a source of a `PGL(4)`-invariant (ZSHEAR);
  the gauge-group count ((BE-27)(ii)). **ZJACOB (JC-6)** — no properness or
  transversality from a codimension count, a Jacobian criterion, or
  Cohen–Macaulayness; **label every dimension count as a count** ((BE-27)).
- **The spread step is NOT this direction.** It is BEARFULL's successor (2) and
  the last 3.8 % of (BE-32)(+); leave it.
- **Out of scope:** `hK`, (GR-15), (RS-5) and the (K-res) wave (a user call),
  class uniformity, W4 / `hcontract`, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 is ARMED (by GBAL)**; report, never fire.
**F11** — a driver per headline sentence; *"every" / "always" / "the only"* needs
a driver that **enumerates**, and a genericity claim is a claim about a
**locus**, so name the locus and say what tests it. **F27** — the asymmetry is
live here: an exhibited `= 0` at a configuration is a **proof** for that
configuration, while *"this piece fails to reach `0`"* needs multiple independent
draws and the return says how many; a single non-zero draw is an **upper bound
artefact**, not a failure. **F25** — verification bar off the **shipped** driver;
**every script committed**; exact ℚ, seeded with printed literals,
degeneracy-guarded, `assert_generic_star` **and** `verify_pencil_witness` on
every draw (the (BE-42)(iii) mechanism *consumes* the first of those, so a draw
that skips it tests nothing). **Cap disclosure MANDATORY.** **Read
`notes/scripts/README.md` *Harness debt* before any numerics** — and note the
`w4/bear*` chain is now **seven** deep: extend the recorded consumer list,
**make no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/bsharp.py`

Extend `bearfull.py` (and through it `bearcase`/`bimage`/`btwocut`/`binduc`) by
**read-only import**; `bgrass`'s free parametrization and its two guards are the
things to reuse, and job 3's adjacent-branch-vertex family is the one genuinely
new generator.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BSHARP".)
§(K-bare-ext) **extends**, no new section; labels **(BE-44)–(BE-48)**, ***Steps
BE43–BE47*** — exactly the tail BEARFULL declared. `BSHARP`, `bsharp`,
`(BE-45)`, `(BE-48)` and *`Step BE47`* verified **0-hit**; `(BE-44)` and *`Step
BE43`* have **two hits each and both are the tail POINTERS** BEARFULL and its
registry row wrote, not consumed labels — checked, not assumed. **Return any
unconsumed remainder.** **Checked and NOT chosen:** `BZERO` (0-hit, but it names
the answer as if settled, and the honest target is a case split in which `0` is
**false** at path pieces) and `BFLAG` (0-hit, but it names the apparatus rather
than the question).

### BSHARP — landing write-up (LANDED 2026-08-28, recon-opus, single design-pass commit)

**Verdict: HIT shape 2 with a refutation attached — the target is CLOSED as a
question, and the answer is a DICHOTOMY rather than a theorem.**
`PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the 2-cut step, S-mark
and (BE-32)(+) untouched; **not a PENCIL event**; **E3 stays ARMED (by GBAL),
not fired**. Canonical home: **§(K-bare-ext)**, `notes/Pencil-informal.md`,
*Steps BE43–BE47*; driver `notes/scripts/w4/bsharp.py`
(`red|split|gen|hyp|adj|validate`). Reservation **fully consumed** —
(BE-44)–(BE-48) and *Steps BE43–BE47*, nothing returned.

**The spec's own correction was right, and it did not go far enough.** The spec
refused the uniform sharpening because (BE-38)(i) proves `dim = 1` sharp at a
**path piece**, and asked for a case split. The split is real but the class is
wrong: the sharpening fails at every **series end** — every `u–v` path leaving
`u` by the same edge — of which a path piece is the special case, and a
**lollipop** (a pendant path from `u` into a `θ` whose far hub is `v`) is a
series end with **three** `u–v` paths where it also fails. **(BE-45)(i)**,
proved from (BE-31)(i)'s SERIES identity: the leading edge is a bridge, its own
hinge line sits in `ρ̄₁ ∩ Π_u`, at every configuration.

**And there is a SECOND, independent mechanism the spec did not have — which
refutes the mechanism's implied sufficiency, on the arc's own landed rows.**
**(BE-45)(ii)**: if `δ₁ = min_P dim⟨P⟩` then (BE-30)(iv)'s containment is an
**equality of spaces**, so `ρ̄₁ ∩ Π_u` inherits that path's first line — **with
no hypothesis on the first edges at all**. That fires at `K₄`/`K_{3,3}`/prism
subdivided ×5, `θ(5,6,7)`, `θ(5,7,9)`, every one with **three distinct first
edges at `u`** and `dim(ρ̄₁ ∩ Π_u) = 1`. **These are BEARFULL's own `bgrass`
rows.** So (BE-38)(iii)'s summary clause *"`0` wherever two `u–v` paths leave
`u` by different edges"* is **false**, and (BE-42)(iii) inherited it when it
named itself *"the reason behind"* that measurement. **No measurement changes;
one prose clause does** — the same shape as (BE-36), and the second time in
this sub-arc a summary sentence outran its own table. The coordinator's second,
weaker guess asked exactly this question (*"are those `δ₁ = 5` rows the proviso
failing or the vacuous corner?"*): **neither — they are a second mechanism**,
and it is a theorem.

**The dichotomy is exact.** Forward (a mechanism fires ⟹ the sharpening fails):
**proved**, both halves, certified per draw as identities of spaces. Converse
(neither fires ⟹ it holds): **0 mismatches over 49 pieces**, proved at 8 of the
11 applicable pieces and measured at 3. (M1) is a property of the **graph**
(decided by connectivity, never by path enumeration); (M2) is a property of the
**configuration**, generically of the graph.

**The reduction the spec offered: TESTED, and the verdict is *sound, with a
different limit than expected*.** It holds, and it **decouples** exactly as the
spec guessed — the condition is per path. But *"`⟨P⟩ ∩ Π_u = ⟨ℓ_first⟩`"* is
equivalent to `dim⟨P⟩ ≤ 5` and fails **identically**, at every configuration,
once a path spans all six dimensions. **The limit is a dimension count, not a
genericity proviso** ((BE-44)). It is also sufficient-not-necessary: loose at 6
of 37 pieces, three of which have the sharpening it cannot see.

**Job 1 delivered: the genericity proviso is DISCHARGED where the sharpening is
available.** The condition is **open** on the constant-rank locus (a morphism
to a product of Grassmannians against a closed incidence locus) and the free
parametrization is **irreducible**, so a non-empty open is dense and finitely
many meet — (BE-25)(i)'s own argument. Hence **one exhibited exact-ℚ witness
proves a whole shape's stratum**, and by (BE-37)(i)(3) the (β) side is
existential, so a dense open is *more* than it needs. 11 pieces exhibit `0`,
296 guarded draws, zero variation over attaining draws ((BE-46)). What is not
discharged, and is said plainly: the class-level statement over all pieces.

**Job 2 answered, and the coordinator hypothesis is SPLIT — at the link the
prep named, but not in the way it expected.** Every failure case discharges
(b2) by a route already landed: `δ₁ ≤ 4` is (BE-38)(ii), `δ₁ = 5` is
(BE-42)(ii)'s first branch, `δ₁ = 6` meets the (BE-22) criterion **outright**,
and (M1) at one end is (BE-42)(ii) at the other. **The residual is exactly
series-at-BOTH-ends with `δ₁ ≤ 4`** (hence `dist ≥ 5`), and there (b2) is
**equivalent to a named identity**: `ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` — the middle of the
piece contributes nothing to `Z` past the two leading lines — **exhibited 5 of
5** ((BE-47)). The ear reach formula (BE-33)(ii), the transport the prep
flagged as the weak link, is **not used**: (BE-30)(i) gives a path piece
`δ₁ = min(dist,6)` directly. So the transport is not *wrong*, it is
*unnecessary*, and the hypothesis's error is one class up.

**Job 3 was NOT FORCED and turned out to be LOAD-BEARING.** `bsharp.py adj` is
the **first parametrization past bearcase's shape guard**: plane first at every
branch vertex, then adjacent branch points forced onto the **meet line** of
their planes (and a branch vertex with two branch neighbours to the
triple-plane point). 12 pieces outside the old guard, 72 guarded draws, **0
dichotomy mismatches**. And the residual window is **out of the old guard's
reach** on the natural both-series family — it forces pendant length `≥ 3`,
hence `δ₁ = 6`, the vacuous corner. The sampler also **re-derives**
(BE-30)(iii)(c) instead of assuming it: a triangle on two adjacent branch
vertices collapses two hinge lines and the gate rejects the draw.

**F25/F27 bar, read off the shipped driver.** Five modes plus `validate`
(~280 s end-to-end); **497 guarded draws**, every one through
`assert_generic_star` **and** `verify_pencil_witness`, with the flags at `u`,
`v` asserted equal to `plane_at`'s closed-star flags and `Π_u, Π_v ⊆ Z`
asserted as identities of spaces; every subspace claim `same_space`/`contains`,
never a dimension; the per-path invariant and the dichotomy both **asserted**,
so a violation stops the run. **F27 in both directions:** the `= 0` rows are
proofs at their configuration (and, with (BE-46), on a dense open), while every
*"this piece fails to reach `0`"* row carries **8 independent draws** — and is
in any case backed by (BE-45)'s identity, which is what actually carries it.
Caps disclosed: the converse's 3 measured-only rows, (BE-46)'s per-shape scope,
the new sampler's own max-branch-degree-2 guard, the 4000-path enumeration cap
(not hit), the 49-piece battery, and the `dim Z = 3` regime excluded from
(BE-47)(iii).

**One index repair made in passing, disclosed rather than smoothed.**
`notes/Pencil-labels.md`'s §(K-bare-ext) **registry row** had been stale since
BZAVOID — BIMAGE, BEARCASE and BEARFULL each landed without extending it. One
clause now covers all four directions ((BE-30)–(BE-48), *Steps BE29–BE47*) and
says so. The registry is a pure index; the workbook's four continuation verdict
blocks stay authoritative.

**Gap map.** The `(K-bare)` row was **integrated, not appended** (the (BE-42)
sentence rewritten in place, `+196` words) and the landing **paid part of its
own way** by compressing the (BE-43) ear-route clause (`−30`), landing at
**1 568 / 1 600**. **32 words remain, which is not enough for the next
landing**: the recompute target is recorded in the labels file.

**TERMINATION: E1 NO, E2 NO** (the refutations are of this direction's own
target as posed and of one landed prose clause, every landed measurement
intact, successor named — the window identity), **E3 ARMED, not fired**.

**Successor ranking, for the coordinator (not acted on).** **(1)** *The window
identity as a class statement* — at a both-series piece with `δ₁ ≤ 4`,
`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩`. (BE-31)(i) makes `ρ̄₁ = ⟨ℓ_u⟩ + ρ̄(middle) + ⟨ℓ_v⟩`
explicit, so the statement is *"the middle's own `ρ̄` misses `Z`"* — a
genuinely new obligation, and closing it puts the (β) side at **(b3) alone**.
**(2)** BEARFULL's spread step, still the last 3.8 % of (BE-32)(+), untouched
here. **(3)** (b3) itself — *`ρ̄₁ ∩ E` is not an opposite-ruling pencil* — which
no direction has yet attacked and which (BE-33)'s third trapping mechanism
already describes. **(4)** A parametrization for branch vertices of branch
degree `≥ 3` (unsubdivided `K₄`), the first shape neither sampler reaches.

## BRULE — fiftieth ordinal, the fifty-eighth direction (single dispatch, prepped 2026-08-28)

**Selection provenance: a coordinator pick that DEVIATES from the previous
direction's successor order, deliberately and for a logged reason.** BSHARP
ranked the window identity (1), the spread step (2) and **(b3)** (3). This spec
takes **(b3)** — and `notes/dispatch-log.md` **F26** is the reason: the phase's
own worst episode was five consecutive directions ordered by *"the previous
direction's successor order, which mechanically chases residuals"*, at a target
the consumer never consumed. The consumer here is **(BE-37)(ii)**, whose
reduction needs **(b1) ∧ (b2) ∧ (b3)**. (b1) and (b2) are now discharged
everywhere but one named window. **(b3) has never been attacked at all** —
it is the last unexamined clause of (β), and the only one whose difficulty is
entirely unknown. Dispatched **un-named, single**, at **`recon-opus`**.

### The target, stated exactly

> **(b3)** *(from (BE-37)(ii), verbatim)*: **`ρ̄₁ ∩ E` is not an opposite-ruling
> pencil `y ∧ L`.**

Decide it: prove it (on its honest domain, with the case split stated if it
needs one), or exhibit a piece and configuration where `ρ̄₁ ∩ E` **is** an
opposite-ruling pencil. Either is a full deliverable.

### What is already free — cite it, do NOT re-derive it

- **(BE-33)**, proven: the ear's bad locus is **exactly three mechanisms**
  (pencil swallowing / confinement / **the `m = 1` opposite ruling**), each a
  *proved lower bound*. (b3) is the piece-side counterpart of the third.
- **(BE-34)**, measured: every trap a real piece shows is a **configuration
  artifact**, **607/607** escalated.
- **(BE-37)(i)(2)/(3)**, proven, and it is the lever: a random exact draw
  computes an **upper** bound on `min loss`, so a sampler **can report a false
  trap but can never miss a real one**; and since (β) is **existential**, one
  drawn configuration settles a piece. An empty hunt therefore corroborates in
  the **safe** direction — the precise sense in which 607/607 is stronger than
  "measured".
- **(BE-30)**, proven: `ρ̄₂` is the span of a **chain on the Klein quadric**,
  with three exact confinement laws at small `m`.
- **(BE-45)/(BE-46)/(BE-47)**, BSHARP: the dichotomy, the discharged proviso,
  and the residual window. **Do not re-open the sharpening** — it is settled
  FALSE at an exact dichotomy.

### Job 1 (PRIMARY, FORCED) — decide (b3)

Note what makes this different from (b1)/(b2): those are **dimension** bounds,
while (b3) is a **shape** condition — *not of the form `y ∧ L`*. A dimension
count cannot settle it (and per **ZJACOB (JC-6)** must not be dressed up as
one). What settles it is the Klein-quadric structure (BE-30) plus whatever
forces `ρ̄₁ ∩ E` off the opposite ruling.

Report the honest status per the arc's own vocabulary: **proven-informally** /
**proven on a named domain with the complement stated** / **measured with the
locus named** / **refuted with a witness**.

### Job 2 (FORCED) — a ROUTING check the coordinator raises, and it is cheap

Reading (BE-37)(iii) against (BE-47)(iii)'s caveat 7, the coordinator believes
the board's current ranking **understates the spread step**, and asks for a
one-paragraph confirmation or refutation as a by-product, not a
sub-investigation:

- **(BE-37)(ii)**'s reduction fails in exactly **4 of 91** arithmetic rows —
  `dim Z = 3`, `c₂ = 3`, `δ₁ ≤ 3`, `m = 2`, i.e. the `π_u = π_v` corner — and
  (BE-37)(iii) escapes them through **(BE-32)(ii)/(iii)/(+)**.
- **(BE-47)(iii)'s caveat 7** independently reports that at `dim Z = 3` the (b2)
  bound is `1` while `⟨ℓ_u, ℓ_v⟩` has dimension `2`, so **(b2) would fail
  outright** — escaping through the *same* (BE-32) family.

**If both readings hold, (BE-32)(+) — whose last 3.8 % is the spread step — sits
UNDER two different clauses of (β), not beside them**, and "the last 3.8 % of a
proved result" is the wrong way to price it. **State whether that is right.** A
refutation is just as useful: it would mean the two `dim Z = 3` escapes are
independent and the board's ranking stands.

### Job 3 (NOT FORCED) — the falsification arm, if job 1 does not close

Hunt for a piece and configuration with `ρ̄₁ ∩ E` an opposite-ruling pencil,
using (BE-37)(i)(2)'s safe direction: an empty hunt is real corroboration here,
not a shrug. Reuse `bsharp.py`'s guarded draw machinery and **(BE-48)(i)'s
adjacent-branch-vertex parametrization** by read-only import — it is the first
sampler past bearcase's shape guard, and its own cap (branch subgraph max degree
`≤ 2`, free vertices with `≤ 2` branch neighbours) must be disclosed with any
figure it produces.

### COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md` §7)

> *Provenance:* formed at this prep from (BE-33)'s three-mechanism
> classification and (BE-34)'s 607/607, both read at their own sites. It rests
> on **no measurement of its own**.
>
> **The hypothesis: (b3) is the CHEAPEST of the three clauses, not the
> hardest — its mechanism is already a proved lower bound and it has an
> `m = 1` smell.** (BE-33) makes the opposite ruling the `m = 1` mechanism
> specifically, and `δ₂ = min(m+1, 6) ≥ 2` is what the reduction leans on; if
> the opposite-ruling trap is confined to `m = 1` on the *piece* side too, (b3)
> may be free at every `m ≥ 2` by a confinement law already proved.
> *Evidence stratum:* (BE-33)'s classification of the **ear's** bad locus,
> applied to the **piece** by analogy — **the same transport BSHARP found
> unnecessary in one direction and wrong in another**, so treat it as the weak
> link and check `E`'s definition on the piece side before using it.
>
> **Where the coordinator expects to be wrong:** (b3) is a *shape* condition,
> and shape conditions have been the arc's expensive ones — §(K-Λ)'s (T5) frame
> died on exactly that (a bad locus gaining a second, equal-dimensional
> component). If (b3) is hard, expect it to be hard for that reason.

### What counts as a HIT — state which you got

1. **(b3) PROVED** on its honest domain. With BSHARP's (b1)/(b2) result, (β) is
   then down to **the window alone**. Report the consequence; **do not act on
   it**; the 2026-08-05 Lean hold binds regardless.
2. **(b3) reduced** to a named checkable condition, as (BE-47)(iii) did for the
   window.
3. **The routing verdict of job 2**, in either direction.
4. **An obstruction, located** — a configuration where `ρ̄₁ ∩ E` *is* an
   opposite-ruling pencil. Classify **mandatorily** ((b3) / the reduction / the
   ear case / (BE-14) / the conjecture); **candidate, never refutation**; read
   the direction-A pivot rule in `notes/Phase39.md` *Current state* first.

### Bars

- **Do not re-open the sharpening** ((BE-45): FALSE at an exact dichotomy) or
  the genericity proviso ((BE-46): DISCHARGED). **Do not attack the window**
  (BSHARP's successor (1)) or the **spread step** (BEARFULL's successor (2)) —
  job 2 asks about the spread step's *ranking*, not for work on it.
- **ZJACOB (JC-6)** — (b3) is a shape condition; **no dimension count may stand
  in for it**, and every count is labelled a count ((BE-27)).
- **Closed routes:** the ear-decomposition induction ((BE-43)); the `G²`
  apparatus ((BE-17)); the transversality count ((BE-16)(iv)); gauge-fixing
  (ZSHEAR); the gauge-group count ((BE-27)(ii)).
- **Out of scope:** `hK`, (GR-15), **(RS-5) and the (K-res) wave (a user call)**,
  class uniformity, W4 / `hcontract`, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F11** —
a driver per headline sentence; *"not an opposite-ruling pencil"* is a **shape**
claim, so say what tests the shape, not the dimension. **F27** — an exhibited
non-`y ∧ L` at a configuration is a proof for that piece by (BE-37)(i)(3); a
claim that a piece *does* trap needs multiple independent draws and the count
stated — and note (BE-37)(i)(2) makes a reported trap the **unsafe** direction
here, so escalate before believing one. **F25** — verification off the
**shipped** driver; every script committed; exact ℚ, printed literal seeds,
`assert_generic_star` **and** `verify_pencil_witness` on every draw. **Cap
disclosure MANDATORY**, including (BE-48)(i)'s sampler cap. **F12 — and it is
live on this one:** BSHARP corrected a landed prose clause but left the two
paragraphs that *state* it untouched (repaired in `1e4ae32c`). If this direction
corrects any summary, **the hunk list must show a hunk at the originating
prose**, not only at your own new section and the gap-map row. **Read
`notes/scripts/README.md` *Harness debt*** — the `w4/bear*` chain is **nine**
deep; extend the consumer list, **make no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/brule.py`

Extend `bsharp.py` (and through it the `bear*`/`bimage`/`btwocut`/`binduc`
chain) by **read-only import**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BRULE".)
§(K-bare-ext) **extends**, no new section; labels **(BE-49)–(BE-53)**, ***Steps
BE48–BE52***, exactly the tail BSHARP declared. `BRULE`, `brule`, `(BE-49)`,
`(BE-53)`, *`Step BE48`* and *`Step BE52`* each verified **0-hit** across
`*.md`, `*.tex`, `*.lean`, `*.py`, `*.m2`. **Return any unconsumed remainder.**
**Checked and NOT chosen:** `BOPP` (0-hit, but it abbreviates "opposite" to
something that reads as a typo next to `(b3)`) and `BRULING` (0-hit, but it
names the ruling rather than the clause under test).

### Gap-map and phase-note budget — RECOMPUTED, and this is the room it bought

The `(K-bare)` row was recomputed at `5ae57257`: **1 200 / 1 600** words, **400
of headroom** (was 32), zero labels dropped by scripted set-diff. `Phase39.md`
is at **555 / 580** lines, **25 of headroom**, after a third relocation. So this
landing folds in **normally** — but integrate into the row's current-state
sentences rather than appending a dated *"Since Steps …"* clause, which is the
shape three landings in a row have had to undo.

### BRULE — landing write-up (LANDED 2026-08-28, recon-opus, single design-pass commit)

**(b3) is DECIDED: proved on its honest domain, by a SEPARATION THEOREM that makes it disjoint from BSHARP's window.**

**HIT shape 1** (with shape 2 attached), `notes/Pencil-informal.md`
§(K-bare-ext) *Steps BE48–BE52*, driver `notes/scripts/w4/brule.py`
(`dom|sep|domin|wit|hunt|validate`).

- **Job 1 (b3): DECIDED, PROVED.** `Π_u = p_u ∧ L` and `Π_v = p_v ∧ L` are
  members of **the very ruling `y ∧ L` lives in**, and distinct members of one
  ruling of a quadric surface meet in `0`. So a (b3) failure at
  `y ∈ {p_u, p_v}` **refutes (b1)**, and at any other `y` forces
  `ρ̄₁ ∩ Π_u = ρ̄₁ ∩ Π_v = 0` — **the sharpening at BOTH ends**. By (BE-45) the
  sharpening fails whenever (M1) or (M2) fires, so **(b3) holds wherever either
  BSHARP mechanism fires — in particular THROUGHOUT (BE-47)(ii)'s residual
  window.** **(β)'s two remaining obligations are DISJOINT.** **(BE-50)**.
- **The honest domain, and three regimes where (b3) is STRUCK rather than
  proved.** It is posed only at `π_u ≠ π_v`, **cross-incidence-free** flags, and
  `m = 1`. At `uv ∈ E(G₁)`, `δ₁ ≤ 1` leaves nothing to contain a pencil; at
  `π_u = π_v` the line `L` does not exist, the clause is **ill-posed**, and its
  content is carried outright by (Z) — every 2-dimensional subspace of `Λ²π`
  meets every image pencil. And cross-incidence at a non-adjacent pair is a
  **configuration-level side-condition (BE-37)(ii) never states**. **(BE-49)**.
- **A landed INFERENCE corrected, with no measurement touched.** (BE-37)(ii)'s
  *"(b3) ⟹ `lossR = 0`"* is **false** — an equality test does not exclude
  containment at `dim(ρ̄₁ ∩ E) ≥ 3`. What holds is **`lossR ≤ lossZ`** (a plane
  of `P(E)` meets the quadric in a conic, so carries at most one member of each
  ruling). The conclusion, the 87/91 enumeration, and the landed
  `bimage.bad_predicate` — which makes the same equality test — all **stand**;
  verified 8/8 + 8/8 against `reach_measured` on newly built rows, **no move
  made** on any landed driver. **(BE-51)**.
- **One witness per shape is a proof**, by openness + **properness** (`P(M) ≅ P¹`
  is complete, the step (BE-46) did not need) + irreducibility. **(BE-52)**.
- **Measured: `0` failures at 637 guarded piece draws** across 49 pieces and
  both samplers; at **every** row with `dim(ρ̄₁ ∩ E) = 2` the Klein form does not
  vanish, so the intersection is not a pencil **at all**. The corrected
  containment form fires only at the vacuous `δ₁ = 6` corner (11 of 49 rows).
  And **(BE-34)(ii)'s landed *"0 hits on the `m = 1` opposite-ruling predicate
  anywhere"* IS (b3)**, already measured at 768 real piece subspaces — cited,
  not re-run. **(BE-53)(i)–(iii)**.
- **Job 2 (routing): CONFIRMED, extended to a THIRD clause, and corrected in its
  pricing.** (BE-37)(iii)'s 4 failing rows, (BE-47)(iii)'s caveat 7, and (b3)'s
  ill-posedness are the **same** `π_u = π_v` corner. But the escape **splits**:
  unforced `π_u = π_v` is avoided free by the existential (β) ((BE-37)(i)(3)),
  and **(BE-32)(+) is load-bearing on the FORCED branch only** — where it
  carries all three clauses at once. So it does sit *under* the (β) side, not
  beside it; *"the last 3.8 % of a proved result"* understates its position,
  while *"(β) stands or falls with it"* would overstate it. **(BE-53)(iv)**.
- **Job 3 (falsification): EMPTY**, and corroborating in the safe direction
  twice over ((BE-37)(i)(2) and (i)(3)). 392 guarded draws, 111 at the
  no-mechanism pieces (BE-50)'s only opening, `0` failures. **(BE-53)(ii)**.
- **COORDINATOR HYPOTHESIS: CONFIRMED in its headline, REFRAMED in its
  mechanism, and its named weak link DISSOLVED.** *"(b3) is the cheapest, not
  the hardest"* — **right**. Its proposed reason (*the opposite-ruling trap is
  confined to `m = 1` on the piece side too*) is **misframed**: (b3) mentions no
  `m` at all; the `m = 1` confinement is a property of the **consumer**
  (mechanism (R) exists nowhere else), so (b3) is simply **not consulted** at
  `m ≥ 2` — stronger and simpler than the conditional the hypothesis offered.
  The flagged weak link — transporting (BE-33)'s **ear** classification to the
  **piece** — is **unnecessary, not wrong**: `E = Π_u + Π_v` is a
  **shared-flag** object, read at its definition site, so nothing is
  transported. That is the **same** finding shape BSHARP reported at
  (BE-47)(i), two directions running. And *"where the coordinator expects to be
  wrong"* — *shape conditions have been the arc's expensive ones* — is
  **refuted here**: this shape condition is cheap **because** the two rulings
  are disjoint families, which turns the shape question into an incidence with
  `Π_u`.
- **Nothing refuted.** `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`,
  the 2-cut step, S-mark, (BE-32)(+), the short-cycle law, BSHARP's dichotomy
  and window identity all untouched. **Not a PENCIL event.** **TERMINATION E1:
  NO, E2: NO, E3: ARMED by GBAL, not fired.**
- **Reservation FULLY CONSUMED** — (BE-49)–(BE-53), *Steps BE48–BE52*, nothing
  returned. **F12 discharged**: the correction landed at the **originating
  prose**, (BE-37)(ii) itself, as well as at the new section and the gap-map
  row.
- **Successors, ranked.** (1) **BSHARP's window identity as a class statement**
  — *at a both-series piece with `δ₁ ≤ 4`, `ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩`* — now the
  **only** thing between the ear case's (β) side and a proof, and by (BE-50)(iii)
  independent of everything this direction touched. (2) **The spread step**,
  (BE-32)(+)'s last 3.8 %, whose position is now known to be *under* three
  clauses on the forced branch. (3) A **class-level (b3)** on the no-mechanism
  class, whose route is the census fact this direction measured but did not
  prove: `ρ̄₁ ∩ E` at dimension 2 is never totally singular at all.

## BWIN — fifty-first ordinal, the fifty-ninth direction (single dispatch, prepped 2026-08-28)

**Selection provenance: the LAST ITEM in (β), and this time the successor order
and the max-impact criterion agree.** BRULE proved **(b3)** and (BE-50)(iii)
proved it **disjoint** from this window, so the ear case's (β) side is down to
exactly one obligation. F26's residual-chasing worry does not apply here — the
consumer (BE-37)(ii) needs (b1) ∧ (b2) ∧ (b3), and this is the only gap left in
any of the three. Dispatched **un-named, single**, at **`recon-fable`**, for the
reason in *The crux* below: the deliverable is a **class** statement, which the
arc's own discharge machinery explicitly cannot produce.

### The target, stated exactly

> **(BE-47)(iii) as a CLASS statement.** For **every** window piece —
> (M1) at both ends, (M2) at neither, `δ₁ ≤ 4` (hence `dist ≥ 5`), at
> `dim Z = 4` — **`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` exactly.**

By (BE-47)(iii), *proved as an equivalence*, that **is** (b2) in the window. So
closing it closes (b2) everywhere, and with (b1) (BSHARP) and (b3) (BRULE)
already discharged, **(BE-37)(ii)'s reduction has all three clauses** and the
ear case's (β) side is proved outright, on the 87-of-91 domain the reduction
already enumerates.

### THE CRUX — read this before planning, because it is what makes the direction hard

The arc's standard discharge for a statement of this shape is
**(BE-46)(i)/(ii)** — openness on the constant-rank locus, irreducibility of the
free parametrization, hence *one exhibited exact-ℚ witness proves a whole
shape's stratum* — strengthened by BRULE's **properness** step ((BE-52)). BSHARP
used it to bank the identity at **5 of 5** window pieces.

**That machinery cannot deliver this target, and (BE-46)(iv) says so in its own
words:** it turns *one shape's* statement into a theorem from one witness, but
*"they do not produce the witness, and nothing here bounds the shapes needing
one"*. **So more exhibitions are more of the same non-class evidence.** What is
needed is a **uniform argument over the window**. Say plainly, at the top of
your write-up, which you produced.

### What is free — cite it, do NOT re-derive it

- **(BE-31)(i)**, proven: the **series** recursion, `ρ̄` sums across a cut vertex.
- **(BE-45)(i)**, proven: at a series end the far part is a leaf, so
  `ρ̄_{u,w₁}(A ∪ e) = K·ℓ_e` **exactly**.
- Together these give BSHARP's reformulation, which is the natural handle:
  **`ρ̄₁ = ⟨ℓ_u⟩ + ρ̄(middle) + ⟨ℓ_v⟩`**, so the target reads *"the middle
  contributes nothing to `Z` beyond the two leading lines"*.
- **(BE-50)**, BRULE: (b3) holds throughout the window, and **(BE-50)(iii)**
  proves this target independent of everything BRULE touched. The window is
  **isolated** — nothing you prove here can disturb (b1) or (b3).
- **(BE-48)(i)**, BSHARP: the adjacent-branch-vertex parametrization, and
  BSHARP's own load-bearing note that **the window lives outside bearcase's old
  shape guard** (pendant length `≥ 3` forces `δ₁ = 6`). Any sampler work starts
  there, with its cap (branch subgraph max degree `≤ 2`, free vertices with
  `≤ 2` branch neighbours) disclosed on every figure.

### Job 1 (PRIMARY, FORCED) — decide the class statement

Prove it uniformly over the window, or exhibit a window piece where
`ρ̄₁ ∩ Z ⊋ ⟨ℓ_u, ℓ_v⟩`. If neither closes, **reduce** it — name a checkable
condition on the middle, the way (BE-47)(iii) named this one.

### Job 2 (FORCED) — the cross-condition question, which the coordinator believes is the trap

> **COORDINATOR OBSERVATION — TO BE TESTED, NOT INHERITED
> (`RESEARCH-ARC.md` §7).** *Provenance:* formed at this prep by reading
> (BE-31)(i) and (BE-47)(iii) together; **no measurement, and no workbook
> sentence states it.**
>
> *"The middle's `ρ̄` misses `Z`"* **looks** like a statement about the middle,
> and it is not. `Z` is defined from `u` and `v` (it contains `Π_u` and `Π_v`),
> while `ρ̄(middle)` is a `w₁–w₂` object. **The identity is a CROSS-condition
> between the middle and the two ends**, and the coordinator's concern is
> precisely that this is the shape which *looks* like a clean induction on the
> middle and is not one. Before building any induction or recursion on the
> middle, **state whether the condition factors through the middle alone**, and
> if it does not, say what the coupling is.
>
> *Where the coordinator expects to be wrong:* the coupling may be cheap — the
> two leading lines `ℓ_u`, `ℓ_v` are pinned by the series ends, so the middle
> may see `Z` only through a 2-dimensional interface that the series recursion
> already describes. If so this job is a paragraph, not an obstacle. **Five of
> the last six coordinator predictions in this arc were refuted, split, or
> reframed by the direction they primed; price this one the same way.**

### Job 3 (NOT FORCED) — widen the window battery

BSHARP's 5 window pieces are all **barbells** (a pendant edge or short path from
`u` into a `θ`, and out of its far hub to `v`), `δ₁ ∈ {2,3,4}`, `dist ∈ {5,6,7}`.
If job 1 produces a candidate argument, test it on window pieces that are **not**
barbells — the honest question being whether "barbell" is the window or merely
the part of it the sampler reaches. **A negative here is a finding**: if the
window *is* exactly the barbells, say so, because that is a much smaller class
than "both-ends-series with `δ₁ ≤ 4`" and would change what a class statement
has to cover.

### What counts as a HIT — state which you got

1. **The class statement PROVED.** Then **(b1)+(b2)+(b3) all hold** and **the
   ear case's (β) side is proved** on the reduction's 87-of-91 domain. This is
   the largest single result the (BE-14) thread could return. Report the
   consequence for the board and the phase boundary; **do not act on either** —
   the phase-boundary call is the USER's (`notes/Phase39.md` *Status*), and the
   2026-08-05 Lean hold binds regardless of how good the news is.
2. **Reduced to a named checkable condition**, as (BE-47)(iii) did.
3. **The window characterized** (job 3) — e.g. *the window is exactly the
   barbells* — even without job 1.
4. **An obstruction, located** — a window piece with `ρ̄₁ ∩ Z ⊋ ⟨ℓ_u, ℓ_v⟩`.
   Classify **mandatorily** (the window / (b2) / the reduction / the ear case /
   (BE-14) / the conjecture); **candidate, never refutation**; read the
   direction-A pivot rule in `notes/Phase39.md` *Current state* first.

### Bars

- **Do not re-open** the sharpening ((BE-45): FALSE at a dichotomy), the proviso
  ((BE-46): DISCHARGED), or **(b3)** ((BE-50): PROVED, and disjoint from this).
- **Do not treat more exhibited witnesses as progress on the class statement** —
  see *The crux*. Banking a sixth witness is not a HIT.
- **ZJACOB (JC-6)**; label every dimension count as a count ((BE-27)).
- **Closed routes:** the ear-decomposition induction ((BE-43)); the `G²`
  apparatus ((BE-17)); the transversality count ((BE-16)(iv)); gauge-fixing
  (ZSHEAR); the gauge-group count ((BE-27)(ii)).
- **The spread step is not this direction** (BEARFULL's successor (2)), and
  BRULE's (BE-53)(iv) already settled its ranking question.
- **Out of scope:** `hK`, (GR-15), **(RS-5) and the (K-res) wave (a user call)**,
  class uniformity, W4 / `hcontract`, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F11** —
a driver per headline sentence; *"every window piece"* is an **exhaustiveness**
claim and needs a driver that **enumerates** the window, or an argument that
does not need one. **F27** — an exhibited identity at a configuration is a proof
for that piece by (BE-37)(i)(3); a claim that a piece *fails* needs multiple
independent draws, stated. **F25** — verification off the **shipped** driver;
every script committed; exact ℚ, printed literal seeds, `assert_generic_star`
**and** `verify_pencil_witness` on every draw. **Cap disclosure MANDATORY**,
including (BE-48)(i)'s sampler cap. **F12, and it is live:** if you correct any
summary, your **hunk list** must show a hunk at the **originating prose**, not
only at your new section and the gap-map row — BRULE did this correctly, BSHARP
did not and needed a repair commit. **F17, also live:** the fan-out doc's own
`**Status:**` header is a surface a landing must update — BRULE left it stale
and needed a second repair commit. **Read `notes/scripts/README.md` *Harness
debt*** — the `w4/bear*` chain is **ten** deep; extend the consumer list, **make
no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/bwin.py`

Extend `brule.py` (and through it `bsharp` and the rest of the chain) by
**read-only import**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BWIN".) §(K-bare-ext)
**extends**, no new section; labels **(BE-54)–(BE-58)**, ***Steps BE53–BE57***,
exactly the tail BRULE declared. `BWIN`, `bwin`, `(BE-58)` and *`Step BE57`*
verified **0-hit**; `(BE-54)` and *`Step BE53`* have **one hit each and both are
the tail POINTER** BRULE wrote, checked and not assumed. **Return any unconsumed
remainder.** **Checked and NOT chosen:** `BMID` (0-hit, but it names the middle,
and job 2's whole point is that the condition may **not** be about the middle
alone — a code asserting otherwise would prime the answer).

### Budget — measured at this prep, and both surfaces are tighter than at BRULE's

`notes/Phase39.md` at **569 / 580** lines after this prep (11 of headroom); the
route-σ block was **thinned to a pointer** here — it was a *third copy* of
material whose canonical homes (§(K-σ) *Step σ5*, the (K-σ) and (K-tight)
gap-map rows, strategy §8.4) were each checked to carry all of it before
thinning, so nothing was relocated and nothing deleted. `(K-bare)` sits at
**1 442 / 1 600** words: the `5ae57257` recompute bought 400 and BRULE spent
242, so **integrate into the current-state sentences**, and if this landing is
large, recompute *Steps BE14–BE33*'s per-direction history (BZAVOID/BINDUC/
BTWOCUT/BIMAGE) — already flagged in the row as the workbook's, not the cell's.

### BWIN — landing write-up (LANDED 2026-08-29, recon-fable, single design-pass commit)

**THE WINDOW IS CLOSED, BY A CLASS THEOREM — the deliverable is the spec's
first shape: the class statement PROVED by a uniform argument.**

**HIT shape 1**, `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE53–BE57*,
driver `notes/scripts/w4/bwin.py` (`dec|sweep|exc|cls|wide|validate`).

- **Job 1: the class statement, PROVED** — for **every** piece that is a
  series end at both ends with `δ₁ ≤ 4` (strictly containing the window; (M2)
  and `dist` are never consulted), constructed exact-ℚ configurations attain
  `dim ρ̄₁ = δ₁`, `dim Z = 4`, cross-incidence-free flags, and
  **`ρ̄₁ ∩ Z = ⟨ℓ_u, ℓ_v⟩` exactly** ((BE-57)). The machine is new to the arc
  and is **not** the one-witness machinery the spec barred: the double series
  peel makes `ρ̄₁ = ⟨ℓ_u⟩ + W + ⟨ℓ_v⟩` with `W` the middle's own screw space;
  the **modular law** turns the target into `W ∩ Z ⊆ ⟨ℓ_u, ℓ_v⟩` ((BE-54));
  `Z = μ^{⊥K} ∩ λ^{⊥K}`, so over a fixed `L` the whole end freedom acts on
  `W` through **one linear functional** vanishing identically on
  `⟨ℓ_u, ℓ_v⟩`, whose survivors are exactly `⟨ℓ_u, ℓ_v⟩` (the end-choice
  lemma, (BE-55)); and the **excess law** `excess ≤ max(0, δ₁ − 3)` ((BE-56))
  says `δ₁ ≤ 4` leaves at most the one dimension that functional kills. The
  quantifier over window shapes is carried by `W` being **arbitrary** — no
  enumeration (F11 met by argument). Two side conditions, named and vacuous
  at every drawn middle: `p_{w₁} ≠ p_{w₂}` at some attaining middle
  configuration, and no middle-forced relation pinning `λ` into `W^{⊥K}`
  ((BE-57)(iv)); the one forceable degeneration the arc knows —
  boundary planes equal — is covered by lemma ((BE-55)(iii)).
- **The consequence for the board:** with (BE-47)(iii) ((b2) ⟺ the identity),
  the `Π_u ∩ Π_v = 0` computation ((b1)), and (BE-50)(iii) ((b3), (M1)
  firing), **(BE-37)(ii) has all three clauses at every window piece** and
  the (β) side is **proved at the window** on the 87-of-91 domain, by
  (BE-37)(i)(3). What stays per-shape or measured is all **outside** the
  window: (BE-45)(iv)'s three no-mechanism rows, (b1)-at-`δ₁ = 5` (measured),
  the (BE-46)/(BE-52) witnesses behind the sharpened-at-one-end route, and
  the `π_u = π_v` corner ((BE-32)(+), forced branch) — the ledger is
  (BE-58)(iv). **Reported, not acted on**: the phase boundary is the user's,
  and the 2026-08-05 Lean hold binds.
- **Job 2, the coordinator observation: REFRAMED** (the prep priced it at
  five-of-six refuted/split/reframed, and reframed is what landed). The
  suspicion was right — the identity is a genuine cross-condition, not a
  statement about the middle — and the hedge was right in refined form: the
  interface is the two Klein pairings `⟨·, λ⟩`, `⟨·, μ⟩` plus the boundary
  pencils. **No induction on the middle appears**; the landed phrase "the
  middle contributes nothing to `Z`" survives only as "nothing beyond what it
  already shares with `⟨ℓ_u, ℓ_v⟩`" — at `t ≥ 3` the middle is FORCED to meet
  `Z`, and `δ₁ ≤ 4` is what forces that contribution inside the two leading
  lines ((BE-54)(iii)).
- **Job 3: the window is NOT the barbells.** Five constructed non-barbell
  window pieces — theta chains, a four-branch theta, and two **R-node
  (subdivided-`K₄`) middles** — plus a `K_{3,3}`-middle control at `δ₁ = 5`
  showing the boundary cuts through the R-node class ((BE-58)(i)). At every
  real window piece the trichotomy sits in the lowest regime (`t = δ₁ − 2`,
  `W ∩ ⟨ℓ_u, ℓ_v⟩ = 0`), which is why BSHARP's successor phrase measured
  true while being the special case ((BE-58)(iii)).
- **Verification:** 358 guarded configurations across five modes (every
  resweep re-gated through `assert_generic_star` + `verify_pencil_witness`);
  the end-to-end construction asserted at **160/160** window end draws; the
  per-`L` criterion (identity ⟺ `excess ≤ 1`) asserted at 84/84 resweeps
  with three MUST-FAIL controls failing at every end draw; `validate` ~112 s.
- **F12 hunks at the originating prose:** (BE-47)(iii) (marked PROVED as a
  class statement), BSHARP's successor bullet (*"the middle's own `ρ̄` misses
  `Z`"* refined at source — the provable form is `W ∩ Z ⊆ ⟨ℓ_u, ℓ_v⟩`, no
  measurement changed), and BRULE's successor bullet (marked LANDED).
- **Nothing refuted; not a PENCIL event** — `hK`, (GR-15), class uniformity,
  `hbareSplit`, (BE-14), the 2-cut step, S-mark and (BE-32)(+) untouched.
  E1/E2 NO; E3 still ARMED (GBAL), not fired. Reservation **fully consumed**
  ((BE-54)–(BE-58), *Steps BE53–BE57*); harness chain now **TEN** deep
  (`… → brule → bwin`), no move made.
- **Ranked successors:** (1) the **one-end-series case** by the same machine
  (one peel, budget `δ₁ ≤ 3`, or a second functional from the clean end) —
  it would retire the largest remaining per-shape component of (β); (2) the
  **spread step** ((BE-32)(+)'s last 3.8 %, the `π_u = π_v` corner's forced
  branch); (3) the **internal R-node** ((BE-31)(ii)).

## BRNODE — fifty-second ordinal, the sixtieth direction (single dispatch, prepped 2026-09-01)

**Selection provenance: a USER CALL, not a successor order.** Offered at the
2026-08-29 twelfth check-in against the spread step, discharging (S1)/(S2) and
the (K-res) wave, the user picked **the internal R-node**; the same call chose
*"recompute only, then hold"*, so this is the first dispatch of the resuming
session. It is **confirmed on the critical path** by BEARFULL's (BE-43)(v) — the
ear-decomposition route was refused precisely because it *"only re-hits the same
R-node"*. Dispatched **un-named, single**, at **`recon-fable`**: the deliverable
is a **description of an object the arc has never described**, so it is a class
statement by construction and no one-witness discharge ((BE-46)(i)/(ii),
(BE-52)) can produce it; and job 2's verdict re-ranks the board.

### The target, stated exactly

> **(BE-31)(ii)'s named residue.** Let `H` be a 2-connected piece with marked
> pair `{u,v}` whose SPQR tree carries an **internal R-node** — a 3-connected
> skeleton `B` at least one of whose virtual edges is replaced by a **flexible**
> child. **Describe `ρ̄_{u,v}(H)`**: a computation from `B` together with the
> children's own data, or a criterion for
> `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)` at the peel of a child, that does **not** go
> through a per-shape witness.

The leaf R-node is already closed — (BE-25)(iii), where the piece **is** the
3-connected skeleton minus its parent virtual edge, hence rigid by (BE-20),
hence `dim M = 6` and `ρ̄ = 0`, and the recursion terminates. The internal one is
not: `K₄` with one virtual edge replaced by an ear is BINDUC's `K₄ + ear(m)`,
with `δ ∈ {4,5}`.

### THE CONSUMER TRACE, run by the coordinator at this prep (F26), so it can be checked rather than trusted

The consumer is **(BE-22)(iii)** — *both pieces attain ⟹ (`G` attains ⟺
`dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)`)* — run as the induction step of the **S-mark**
frame ((BE-25)(ii)). At an internal R-node each virtual edge's endpoints `{x,y}`
**are** a 2-cut of `H`, so a child peels: `H = H' ∪ C_e` over `{x,y}`. The
criterion then wants `ρ̄_{x,y}(H')` and `ρ̄_{x,y}(C_e)` — and `H'` still contains
the 3-connected `B`, so **the peel does not reduce to a series-parallel piece**.
That is why (BE-31)(ii)'s residue is what the consumer actually takes, and the
trace is written here so the direction can **contradict it** rather than inherit
it.

**The carve-out that narrows the honest domain, and deciding how much is the
cheapest first result.** By (BE-22)(vi), if one side is **rigid** the
general-position half disappears entirely and the criterion collapses to the
single condition `ρ₁ = δ₁` — *a statement about ONE piece and its welding*. By
(BE-20) a 3-connected side is rigid. So the hard case is exactly **both sides
flexible**, which at an R-node means the skeleton *plus its remaining children*
is itself flexible. **Say how large that case is** — is there always a peel
order keeping one side rigid? A negative is expected (`K₄ + ear(m)` has
`δ ∈ {4,5}` on the skeleton side), but it has never been checked, and a positive
would collapse the whole direction to (BE-22)(vi).

### What is free — cite it, do NOT re-derive it

- **(BE-31)(i)**, proven at 12/12 seeded draws as identities of **subspaces**:
  **series** `ρ̄_{u,v}(H) = ρ̄_{u,z}(H₁) + ρ̄_{z,v}(H₂)` across a cut vertex,
  **parallel** `ρ̄_{u,v}(H) = ρ̄_{u,v}(H₁) ∩ ρ̄_{u,v}(H₂)` across a 2-cut.
- **(BE-31)(ii)**: iterating (i) computes `ρ̄` for every series-parallel piece
  from its hinge lines alone — `S`-node **sums**, `P`-node **intersects**, leaf a
  single edge with `ρ̄ = ⟨ℓ_e⟩`. The ear is the all-`S` case.
- **(BE-31)(iii)**, with a witness: the path-intersection bound
  `ρ̄ ⊆ ⋂_P ⟨P⟩` is a genuine **upper bound** and **NOT an equality** —
  `θ(3,3)` with a pendant edge gives `1` against `2`, because intersection does
  not distribute over sum. **Do not re-propose it.**
- **(BE-22)(i)**, proven: `dim M(G) = dim M(G₁) + dim M(G₂) − 6 − dim(ρ̄₁+ρ̄₂)`;
  **(ii)** `ρ_i ≤ δ_i` when the piece attains; **(iv)** `δ₁ = δ₂ = 0` composes
  free; **(vi)** one rigid side kills the general-position half.
- **(BE-20)**: 3-connected ⇒ `def₂ = 0`. **(BE-18)**: 1-cuts compose.
  **(BE-21)/(BE-23)**: the 2-cut `def₃` law is `max(g₁+g₂, f₁+f₂−6)`.
- **(BE-30)**, BIMAGE: for the **ear**, `ρ̄₂` is the span of a **chain on the
  Klein quadric** with ends `Π_u`, `Π_v` — the model answer for the SP case, and
  the shape a general description should specialize to.
- **(BE-39)/(BE-40)**, BEARFULL: `girth(Q) ≥ 6`, every cycle of length `≤ 6`
  forces `δ = 0`, and `δ ≤ max(0, L−6)` — free combinatorial bounds on `δ`.
- **(BE-43)(i)/(ii)/(iii)**, BEARFULL: the ear route is **refused** (every
  minimum-degree-`≥ 3` graph forces a single-edge ear in EVERY chord-free open
  ear decomposition); the chord step's **combinatorial half is FREE**,
  `def₃(G+uv) = max(def₃(G) − δ_uv, def₃(G) − 5)`, exhaustive at 189 587
  instances; its **geometric half is priced and not soft** — `Y°(G+uv)` is a
  proper closed subset of `Y°(G)`, and `dim M` is **upper** semicontinuous, so
  specialisation points the **wrong way**.

### Job 1 (PRIMARY, FORCED) — describe `ρ̄` at an internal R-node

Extend the recursion past the R-node, or reduce the R-node case to a named
checkable condition on `B`, or prove no description of that kind exists.

> **The sharpest form, and the cheapest thing to decide FIRST: is `ρ̄` at an
> R-node a function of the children's `ρ̄` at all?** The entire content of the SP
> recursion is that it **is**, at `S`- and `P`-nodes: (BE-31)(i) computes
> `ρ̄(H)` from `ρ̄(H₁)` and `ρ̄(H₂)` and nothing else. At a 3-connected skeleton
> that may fail — `ρ̄_{u,v}(H)` may depend on the children's realizations beyond
> their relative screw spaces. **This is decidable by two children with the same
> `ρ̄` and different geometry**, it is one driver mode, and a **negative kills the
> "extend the recursion" shape outright** (HIT shape 4). Run it before building
> any recursion.

### Job 2 (FORCED) — the routing question, and it is why the direction is at the top rung

> **COORDINATOR OBSERVATION — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md`
> §7).** *Provenance:* formed at this prep by reading (BE-30) against
> (BE-22)(iii); **no measurement, and no workbook sentence states it.**
>
> **The arc's hard half has never been *computing* `ρ̄`.** For the ear, `ρ̄₂` was
> described **exactly** by (BE-30) — a chain on the Klein quadric, a *bijection*
> — and BEARCASE/BEARFULL/BSHARP/BRULE/BWIN were still needed for (α) and (β),
> the **reach** and **general-position** halves. So a formula for `ρ̄` at an
> R-node may not move (BE-22)(iii) at all.
>
> **The job:** having answered job 1 (or having failed to), state **where the
> R-node's real content sits** — in the *description*, in the (α)-analogue
> (reach: what `dim ρ̄` is), or in the (β)-analogue (general position of `ρ̄₁`
> against `ρ̄₂`). Read (BE-22)(iii) and the S-mark frame, do not assume. **A
> negative — "the description is free and the content is all in (β)" — re-ranks
> the board and is a HIT, worth more than a partial job 1.**
>
> *Where the coordinator expects to be wrong:* the ear's (β) difficulty came
> from `ρ̄₁` being **arbitrary** while `ρ̄₂` was pinned; at an R-node peel both
> sides are structured, so the (β)-analogue may be *easier*, not harder, and
> the description may then be the whole job after all. **Five of the last six
> coordinator predictions in this arc were refuted, split, or reframed by the
> direction they primed; price this one the same way.**

### Job 3 (NOT FORCED) — price the chord step as the alternative coordinate

BEARFULL left the R-node a second local coordinate: the **chord step**,
*(BE-14) + the S-mark clause for `G` ⟹ for `G + uv`*, whose combinatorial half
is **free** ((BE-43)(ii)) and whose geometric half is **one sentence long** and
**priced not soft** ((BE-43)(iii)). Decide whether it is a cheaper coordinate
for the same obligation or a strictly harder one, and say which. This is a
**pricing** verdict, not an attack; a refutation of the chord step as a route is
worth as much as an endorsement.

### What counts as a HIT — state which you got

1. **`ρ̄` at an internal R-node DESCRIBED** — a computation from `B` and the
   children, or the SP recursion **extended to a complete recursion over the
   SPQR tree**. The largest result this thread could return: it is the step from
   *ear* to *general piece*.
2. **Reduced** to a named checkable condition on `B`, the way (BE-47)(iii)
   reduced the window.
3. **The routing verdict (job 2)** — the R-node's content located in the
   description / (α)-analogue / (β)-analogue, re-ranking the board. **A negative
   here is a HIT.**
4. **An obstruction, located** — most likely job 1's sharp form coming back
   **NO** (`ρ̄` at an R-node is *not* a function of the children's `ρ̄`), which
   would close the "extend the recursion" shape and redirect the 2-cut lemma's
   general piece. Classify **mandatorily** (the description / (BE-22)(iii) / the
   2-cut step / S-mark / (BE-14) / the conjecture); **candidate, never
   refutation**; read the **direction-A pivot rule** in `notes/Phase39.md`
   *Current state* first.

### Bars

- **Do not re-open:** the path-intersection bound as an equality ((BE-31)(iii),
  refuted with a witness); the **ear-decomposition induction** ((BE-43)); the
  sharpening ((BE-45)) and the proviso ((BE-46)); **(b3)** ((BE-50)); the `G²`
  apparatus ((BE-17)); the transversality / dimension count ((BE-16)(iv),
  (BE-27)); gauge-fixing (ZSHEAR); the gauge-group count ((BE-27)(ii)).
- **ZJACOB (JC-6):** no properness, smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness. Label every
  dimension count **as a count** ((BE-27)).
- **Not this direction, and ranked separately:** the **one-end-series** case
  (BWIN's successor 1), the **spread step**, **(S1)/(S2)** (BWIN's two side
  conditions), and BTWOCUT's bundle construction ((BE-29)(ii)).
- **Out of scope:** `hK`, **(GR-15)**, **(RS-5) and the (K-res) wave (a USER
  call)**, class uniformity, W4 / `hcontract`, and **any `.lean`** (the standing
  2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F26 is
this direction's own job 2** — the consumer trace above is the coordinator's and
may be wrong; do not skip the job because the trace looks convincing. **F11** — a
driver per headline sentence; *"a function of the children's `ρ̄`"*, *"no
description exists"* and any *"every / exactly / the only"* are **exhaustiveness**
claims needing a driver that **enumerates**, or an argument that needs no driver.
**F27** — an exhibited identity at a configuration is a proof for that piece by
(BE-37)(i)(3); a claim that a shape **fails** needs multiple independent draws,
and the return must say how many. **F25** — verification off the **shipped**
driver; every script committed (the 2026-08-05 reproducibility rule); exact ℚ,
printed literal seeds, `assert_generic_star` **and** `verify_pencil_witness` on
every draw. **Cap disclosure MANDATORY** — an exhausted cap is *"not found under
cap C"*, never *"does not exist"*, and the disclosure travels with the figure.
**F12** — if you correct any summary, your **hunk list** must show a hunk at the
**originating prose**, not only at your new section and the gap-map row.
**F17** — the fan-out doc's own `**Status:**` header is a surface a landing must
update; so is `notes/Phase39.md`'s, and BWIN needed a repair commit for exactly
that. **Read `notes/scripts/README.md` *Harness debt*** — the `w4/bear*` chain is
**eleven** deep (`… → brule → bwin`); extend the consumer list, **make no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/brnode.py`

Extend `bwin.py` (and through it `brule`/`bsharp`/`bearfull`/`bearcase`/`bimage`/
`binduc` and the rest of the chain) by **read-only import**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BRNODE".)
§(K-bare-ext) **extends**, no new section; labels **(BE-59)–(BE-63)**,
***Steps BE58–BE62***, exactly the tail BWIN declared and consumed nothing of.
`BRNODE`, `brnode`, `(BE-60)`–`(BE-63)` and *`Step BE62`* verified **0-hit**
across `*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2`; **`(BE-59)` and *`Step BE58`* have
one hit each, both on `notes/Pencil-labels.md:2216` and both opened and confirmed
to be the tail POINTER** BWIN wrote — the same carve-out BSHARP's and BWIN's
reservations needed. **Return any unconsumed remainder.** **Checked and NOT
chosen:** `BFLOW` and `BSPQR` (both 0-hit, but each names a *candidate answer* —
the coordinator's flow duality and an SPQR-tree recursion respectively — and job
1's sharp form may kill the second outright; a code asserting the answer is the
framing `RESEARCH-ARC.md` §7 forbids). `BGEN` rejected on the (L5) substring
rule (2 hits).

### Budget — measured at this prep

`(K-bare)` sits at **1 169 / 1 600** words: the `442c9363` recompute took it
1 550 → 1 162 and BWIN's landing is **already integrated**, so **431 words of
headroom** — integrate into the current-state sentences; no recompute is owed by
this landing unless it is very large. `notes/Phase39.md` is measured in the
commit message; the note's *Doc debt* watch item stands — **when it binds, the
question is "what here is reference rather than status?"**, not another
compression fold of *Decisions made*.

### BRNODE — landing write-up (LANDED 2026-09-01, recon-fable, single design-pass commit)

**THE INTERNAL R-NODE IS DESCRIBED, AND THE DESCRIPTION WAS NEVER THE HARD
PART — HIT shapes 1 and 3.**

`notes/Pencil-informal.md` §(K-bare-ext) *Steps BE58–BE62*, driver
`notes/scripts/w4/brnode.py` (`law|rec|carve [named|full]|route|validate`).

- **Job 1, the sharp form FIRST, as the spec ordered — and the answer is
  YES, by a proof.** The **boundary-pair lemma** ((BE-59)(i), extracted from
  (BE-22)(i)'s own proof): a connected child's image in `K⁶ ⊕ K⁶` at its
  terminals is `Δ ⊕ ({0} ⊕ ρ̄_e)` — its whole interface is a function of
  `ρ̄_e` alone. Hence the **decorated-skeleton law** ((BE-59)(ii)): `M(H)`
  restricted to `V(B)` is exactly the motion space of `B − uv` with each
  edge constrained by `m_x − m_y ∈ ρ̄_e` in place of a hinge line, and
  `ρ̄_{u,v}(H)` is its image at `(u, v)` — **exact at every configuration,
  no genericity**, with the many-piece fibre-product dim law ((BE-59)(iii))
  containing (BE-22)(i). So the SP recursion **extends to a complete
  recursion over the SPQR tree** ((BE-60)): leaf `⟨ℓ_e⟩`, `S` sums, `P`
  intersects, `R` the decorated kernel — (BE-31)(ii)'s named residue
  **closed as a computation** (HIT shape 1); the R-node case is a kernel,
  not a lattice expression, which is why the sum/intersect recursion could
  not see it. HIT shape 4 does **not** fire.
- **Job 2, the routing question (F26, tested not inherited): the
  coordinator's trace CONFIRMED in its central clause, REFRAMED in one.**
  The description is one elementary lemma, so it was never the consumer's
  missing piece — the ear precedent generalizes. Measured at **24
  both-flexible R-node peels** (guarded draws, both gates, (BE-22)(i)
  asserted at every one): both sides attained, welded attainment
  `ρ_i = δ_i` everywhere, general-position shortfall **0 at 24/24** — the
  (BE-22)(iii) criterion held outright, consistent with BTWOCUT's
  13 484/13 484. The reframe: the trace's "the peel does not reduce to a
  series-parallel piece" is true but immaterial — the decorated skeleton is
  the object, bounded, the same opaque-subspace move BWIN made. **Where the
  content sits ((BE-62)(iii), the named residue): the achievable-decorations
  class statement** — which tuples `{ρ̄_e}` pencil configurations achieve,
  a fibred product over the branch flags (children couple only through the
  flag at a shared vertex), known exactly for leaves and ears
  ((BE-30)(ii)), open in general.
- **The carve-out (the spec's cheapest-first question): negative, with an
  exact boundary.** The (BE-22)(vi) collapse at the peel of child `e` needs
  a `δ = 0` side; an ear child never supplies one, so for an all-leaf
  remainder the condition is **`δ_{xy}(B − uv − e) = 0`, a checkable
  function of `B`** ((BE-61)). Enumerated **exhaustively at `n = 4, 5, 6`**
  (1 + 26 + 1 768 labelled 3-connected skeletons — reproducing btwocut's
  1 795 census — 198 360 triples): collapse at 20.0 % / 70.9 % / 84.8 %.
  `K₄` collapses **exactly at the edge disjoint from `uv`** (the spec's
  parenthetical refined); the **prism at two rungs does not** (`δ = 1`) —
  one flexible child already leaves no collapse peel, and constructed
  both-flexible pieces **draw** (`K₄` + three long ears: `dim M = 7`,
  `ρ̄_{u,v} ≠ 0`, every peel both-sides-flexible).
- **Job 3: the chord step is the STRICTLY HARDER coordinate for this
  obligation** ((BE-63)) — its geometric half fights upper semicontinuity
  ((BE-43)(iii), the wrong way, no landed mechanism), while the decorated
  route's residue is right-way attainment statements plus one class
  statement of the species BWIN closed once. Kept as a coordinate only
  where the SPQR frame itself obstructs.
- **Verification:** 36 guarded draws over nine `law` pieces + 6
  equal-`ρ̄`/different-geometry interior-redraw pairs (full-span and flat
  `Λ²π` mechanisms); the lines-only SPQR recursion asserted at 3 nested
  pieces × 3 draws; the carve enumeration exhaustive at `n ≤ 6` in `carve
  full`; 24 route peels with (BE-22)(i) asserted at every one; exact ℚ,
  seed literal `20260901`; `validate` ~17 s. Caps disclosed: `K₄`/`K₃,₃`
  battery skeletons only (a two-hub triangle defeats the independent-planes
  sampler — the (BE-30)(iii)(c) mechanism — so prism pieces are
  combinatorial-only), and (BE-62)(ii) is a measurement, not the class
  statement.
- **F12 hunk at originating prose:** (BE-31)(ii)'s *"What has no such
  description is the R-node"* marked LANDED at source (BIMAGE section).
  **Nothing refuted; not a PENCIL event** — `hK`, (GR-15), class
  uniformity, `hbareSplit`, (BE-14), the 2-cut step, S-mark and (BE-32)(+)
  untouched. E1/E2 NO; E3 still ARMED (GBAL), not fired. Reservation
  **fully consumed** ((BE-59)–(BE-63), *Steps BE58–BE62*), nothing
  returned; the successor tail opens at (BE-64) / *Step BE63*. Harness
  chain now **ELEVEN** deep (`… → bwin → brnode`), no move made.
- **Ranked successors:** (1) the **achievable-decorations statement**
  ((BE-62)(iii)) — per-child achievable sets past ears (theta children
  first), then attainment of the decorated skeleton over the coupled
  flags: what (BE-22)(iii) at the R-node actually consumes; (2) BWIN's
  standing ranking (the one-end-series case, the spread step, (S1)/(S2)),
  unchanged by this landing.

## BDECOR — fifty-third ordinal, the sixty-first direction (single dispatch, prepped 2026-09-01)

**Selection provenance: BRNODE's successor (1), taken only AFTER the coordinator
re-ran the consumer trace — F26 applies to this pick by name.** BRNODE ranked the
achievable-decorations statement first, and this arc's worst recorded episode
(F26: five consecutive directions at (GR-104)(i)) was exactly *"ordered by the
previous direction's successor order, which mechanically chases residuals"*. So
the ranking was **not** inherited. The coordinator opened (BE-22)(iii) and
(BE-62)(iii) and confirms: the criterion needs some **achievable** decoration
tuple to attain `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)`, and BRNODE closed the
*computation* while leaving the *achievability* quantifier open. **That
quantifier is the consumer's remaining input, not a residual beside it.**
Dispatched **un-named, single**, at **`recon-opus`**: the mapped rung is the top
one (a class statement over a quantifier the arc has never characterized past
ears), and fable is unavailable this session, so the playbook's named substitute
applies — never a weaker rung than mapped where a stronger is reachable.

### The target, stated exactly

> **(BE-62)(iii).** For an internal R-node piece `H` with skeleton `B`: **which
> decoration tuples `{ρ̄_e}_{e ∈ E(B)}` are simultaneously achievable by pencil
> configurations of `H`?** BRNODE proved the shape of the answer — children
> incident to a branch vertex `z` are coupled **only** through the flag
> `(p_z, π_z)`, so the achievable tuples are a **fibred product over flag
> assignments on `V(B)`** of per-child achievable sets. Those sets are known
> exactly for **leaves** (`ℓ ∈ Π_x ∩ Π_y`) and **ears** ((BE-30)(ii), a
> bijection) and **open in general**.

Two halves, and the spec wants them separated: **(A)** the **per-child** sets
past ears — theta children first; **(B)** **attainment of the decorated
skeleton** over the coupled flags, i.e. that some achievable tuple meets
(BE-22)(iii)'s criterion.

### What is free — cite it, do NOT re-derive it

- **(BE-59)(i)/(ii)**, BRNODE, proven: a connected child's whole boundary trace
  at its terminals is `Δ ⊕ ({0} ⊕ ρ̄_e)` — a function of `ρ̄_e` alone — so
  `M(H)|_{V(B)}` **is** the decorated skeleton's motion space, exact at every
  configuration, no genericity.
- **(BE-60)**, BRNODE: the complete SPQR recursion — leaf `⟨ℓ_e⟩`, `S` sums,
  `P` intersects, `R` the decorated kernel.
- **(BE-62)(iii)**, BRNODE: the **flag-coupling factorization is PROVED**. The
  per-child sets are what is open.
- **(BE-30)(ii)**, BIMAGE, proven and a *bijection*: **stated at FIXED FLAGS**
  (its opening clause is *"Fix the shared flags"* — the coordinator opened it
  and confirmed this, because the whole hypothesis below turns on it). The
  achievable ear tuples are exactly: every `ℓ_i` on the Klein quadric,
  consecutive ones conjugate and distinct, `ℓ₁ ∈ Π_u`, `ℓ_{m+1} ∈ Π_v`, **and
  nothing further for `m ≥ 3`**.
- **(BE-30)(iii)** is the **correction at small `m`** that the ear hypothesis did
  not predict — read it before assuming short paths behave like long ones.
- **(BE-61)**, BRNODE: the collapse condition `δ_{xy}(B − uv − e) = 0`, exhaustive
  at `n ≤ 6`; the prism fails at two rungs, so **both-flexible pieces are
  nonempty at one flexible child** and the constructed family draws.
- **(BE-22)(iii)/(vi)**: the criterion, and the rigid-side collapse.

### Job 1 (PRIMARY, FORCED) — the per-child achievable set past ears

Characterize the achievable `ρ̄_e` set for a **theta child** at fixed terminal
flags, then say how far the method reaches (nested children, children with their
own R-nodes). A characterization, a reduction to (BE-30)(ii), or a proof that no
(BE-30)(ii)-style bijection exists past ears — all three are results.

### Job 2 (FORCED) — the coordinator's hypothesis, which may make job 1 cheap

> **COORDINATOR HYPOTHESIS — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md`
> §7).** *Provenance:* formed at this prep by reading (BE-62)(iii)'s
> factorization against (BE-30)(ii)'s **fixed-flag** statement, whose opening
> clause the coordinator opened and verified. **No measurement, no driver, and
> no workbook sentence states it.**
>
> **The P-node layer may be FREE.** A theta child between terminals `x, y` is a
> `P`-node over three internally-disjoint paths, so by (BE-60) its
> `ρ̄ = ⟨P₁⟩ ∩ ⟨P₂⟩ ∩ ⟨P₃⟩`. The three paths share **only** `x` and `y`, whose
> flags are fixed by the fibration; interior vertices are free. So the theta's
> achievable set should be exactly `{⟨P₁⟩ ∩ ⟨P₂⟩ ∩ ⟨P₃⟩}` over **independent**
> (BE-30)(ii)-legal chains at those flags — computed, not newly characterized.
> **If that holds, job 1's theta case is a corollary and the direction's real
> content is half (B), the skeleton-attainment statement over coupled flags.**
>
> *Where the coordinator expects to be wrong, named rather than hedged:*
> **(a)** (BE-30)(ii)'s *"nothing further"* is stated for `m ≥ 3` and
> **(BE-30)(iii)** is an explicit correction at small `m`, so short theta paths
> may not be free — that is the likeliest failure and it is checkable first.
> **(b)** In an *ear*, a terminal has degree **1** into the child; in a theta it
> has degree **3**, so three first-lines lie in `Π_x` simultaneously. `Π_x` is a
> pencil, so this looks harmless — but (BE-30)(ii)'s proof calls interior
> degree-2 vertices *"free vertices in btwocut's sense"*, and whether that
> freedom survives a degree-3 terminal is **not** something the ear case ever
> tested. **Check (b) before building on the hypothesis.**
>
> **Five of the last six coordinator predictions in this arc were refuted, split,
> or reframed by the direction they primed** — and BRNODE confirmed the last one,
> so the streak is not evidence of accuracy. Price this one the same way.

### Job 3 (NOT FORCED) — half (B), if job 1 closes cheaply

Attainment of the decorated skeleton over the coupled flags: does some achievable
tuple meet (BE-22)(iii)? BRNODE measured the criterion holding **outright** at
24/24 constructor-capped peels, so the honest question is whether that is a
theorem or a constructor artifact. **Say which**, and if it is a theorem for a
named class, name the class.

### What counts as a HIT — state which you got

1. **The per-child achievable set characterized past ears** (theta children, or
   wider), the (BE-30)(ii)-analogue delivered.
2. **The P-node layer shown free** (job 2's hypothesis confirmed), reducing job 1
   to (BE-30)(ii) and relocating the content to half (B).
3. **Half (B) settled for a named class** — attainment over coupled flags.
4. **An obstruction, located** — e.g. no (BE-30)(ii)-style bijection past ears,
   or the degree-3-terminal freedom failing. Classify **mandatorily** (the
   per-child set / the fibration / (BE-22)(iii) / the 2-cut step / S-mark /
   (BE-14) / the conjecture); **candidate, never refutation**; read the
   **direction-A pivot rule** in `notes/Phase39.md` *Current state* first.

### Bars

- **Do not re-open:** the decorated-skeleton law ((BE-59)/(BE-60), PROVED); the
  path-intersection bound as an equality ((BE-31)(iii)); the ear-decomposition
  induction ((BE-43)); the sharpening ((BE-45)); the proviso ((BE-46)); **(b3)**
  ((BE-50)); the `G²` apparatus ((BE-17)); the transversality count
  ((BE-16)(iv), (BE-27)); gauge-fixing (ZSHEAR); the gauge-group count
  ((BE-27)(ii)); the chord step as the cheaper coordinate ((BE-63), PRICED
  strictly harder).
- **ZJACOB (JC-6):** no properness, smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness. Label every
  dimension count **as a count** ((BE-27)).
- **Not this direction, and ranked separately:** the one-end-series case, the
  spread step, **(S1)/(S2)**, BTWOCUT's bundle construction.
- **Out of scope:** `hK`, **(GR-15)**, **(RS-5) and the (K-res) wave (a USER
  call)**, class uniformity, W4 / `hcontract`, and **any `.lean`** (the standing
  2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F11** —
a driver per headline sentence; *"exactly"*, *"nothing further"* and *"free"* are
**exhaustiveness** claims needing an **enumerating** driver or an argument that
needs none. **F27** — an exhibited tuple is a proof that it is achievable; a
claim that a tuple is **NOT** achievable needs multiple independent draws, stated,
and is *"not found under cap C"*, never *"does not exist"*. **Cap disclosure
MANDATORY**, and it travels with the figure. **F25** — verification off the
**shipped** driver; every script committed; exact ℚ, printed literal seeds,
`assert_generic_star` **and** `verify_pencil_witness` on every draw. **F12** — if
you correct any summary, your **hunk list** must show a hunk at the **originating
prose**. **F17** — the fan-out doc's own header and `notes/Phase39.md`'s
`**Status:**` header are surfaces a landing must update; BWIN needed a repair
commit for exactly that miss. **Read `notes/scripts/README.md` *Harness debt***
— the chain is **eleven** deep (`… → bwin → brnode`) with a new `bwin.dehom` row;
extend the consumer list, **make no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/bdecor.py`

Extend `brnode.py` (and through it `bwin`/`brule`/`bsharp`/`bimage`/`binduc` and
the rest of the chain) by **read-only import**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BDECOR".)
§(K-bare-ext) **extends**, no new section; labels **(BE-64)–(BE-68)**,
***Steps BE63–BE67***, exactly the tail BRNODE declared and consumed nothing of.
`BDECOR`, `bdecor`, `(BE-68)` and *`Step BE67`* verified **0-hit** across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2`; **`(BE-64)` and *`Step BE63`* have two
hits each — `notes/Pencil-fanout.md:7789` and `notes/Pencil-labels.md:2271`,
both opened and confirmed to be the tail POINTER** BRNODE wrote in the two places
it records one. Recorded because a bare hit count would read as a collision.
**Return any unconsumed remainder.** **Checked and NOT chosen:** `BTHETA` (0-hit,
but it names the theta child, which is only the spec's *first* sub-case — job 1
may find it the wrong cut, and a code that pins the scoping would prime it).

### Budget — measured at this prep

`(K-bare)` sits at **1 305 / 1 600** words (295 of headroom) — integrate into the
current-state sentences. `notes/Phase39.md` stood at **576 / 580** lines with an
in-flight block to add, so this prep **relocated the *Citations* section verbatim**
to `notes/Pencil-structure.md` §"Citations — the phase's verified bibliography" —
a bibliography is reference, not status, the seventh such block — leaving a
pointer and buying 43 lines. All 47 citation body lines were verified present in
the new home by **scripted set-diff, not by eye** (the F21 discipline). **A
direction that verifies a new source adds it THERE, in its landing commit.**

### BDECOR — landing write-up (LANDED 2026-09-01, recon-opus, single design-pass commit)

**HIT shapes 1 and 2, together, and in a stronger form than either was
stated.** Mathematics: `notes/Pencil-informal.md` §(K-bare-ext) continuation
(direction BDECOR), **(BE-64)–(BE-68)** / *Steps BE63–BE67*. Driver
`notes/scripts/w4/bdecor.py` (`prod|theta|small|chart|attain|validate`).

- **The headline: there is no "past ears".** (BE-62)(iii)'s fibration,
  recursed down to the **topological skeleton** — hubs joined by one edge per
  maximal degree-2 branch — makes every child an ear. At a **fixed** legal
  flag assignment on the hub set the legal configurations of any piece are
  the **literal product** `∏_b Ear(a_b; ϕ)` intersected with the harness
  gate's cross-branch genericity proviso `G`, because the pencil condition is
  *every closed star coplanar* and at a hub that is a **conjunction with one
  conjunct per incident branch**, each conjunct reading only that branch's own
  first interior vertex ((BE-64)(i)/(ii), proved). Hence the per-child sets
  (BE-62)(iii) left *"open in general"* are **never needed** ((BE-64)(iv)).
- **Job 2's hypothesis: CONFIRMED and STRENGTHENED.** The freedom is not a
  property of the P-node layer; it is a property of the pencil condition, and
  the SPQR tree was simply the wrong decomposition to ask it on. The theta
  child's achievable set is then a **corollary**: `⟨C₁⟩ ∩ ⟨C₂⟩ ∩ ⟨C₃⟩` over
  independent legal chains ((BE-66)(i)) — exactly the relocation the spec
  predicted (*"the direction's real content is half (B)"*).
- **The spec's two named weak links came out OPPOSITE ways, and that is the
  direction's most useful single sentence.** **(b)**, the degree-3 terminal —
  the one the spec said to check first — is **harmless and provably so**: the
  hub condition is a conjunction, so three first-lines in the pencil `Π_x` is
  three copies of the ear condition, not a new one. **(a)**, the small-`m`
  correction, is **real and stronger than the spec's reading**: it does *not*
  stay inside its branch. At `π_x = π_y` a length-3 branch has span **exactly
  `Λ²π`**, so two of them have **equal** spans and the P-node intersection
  does not drop; the law becomes `max(ambient, confined)` and `ρ̄` **exceeds**
  general position at **7 of 30** measured rows, by up to **3** ((BE-66)(iii)).
- **And that is a correction to (BE-62)(iii)'s own quantifier (F12).** All
  **7 of 7** exceeding rows sit at configurations that **do not attain** —
  which is exactly what (BE-22)(iii)'s *"if both pieces attain"* hypothesis
  excludes. The consumer's question is the **attaining**-achievable set, and
  the extra members of the full set are precisely the flag coincidences.
  Moreover the only landed mechanism forcing `π_x = π_y` is BZAVOID's
  triangle propagation ((BE-15)), which needs `x ∼ y` — impossible at the
  ends of a **virtual** edge of a simple 3-connected skeleton. So **no landed
  mechanism forces the confinement where the consumer needs it** ((BE-66)(iv);
  stated as *no landed mechanism*, not as *never*).
- **Where the residual coupling actually is: the FLAG BASE, and it is the
  arc's own §(K-chart) object.** The legal flag assignments are the pencil
  configurations of the **hub subgraph** `B_real` (the graph of length-1
  branches), so the base is a product of irreducible rational bundles **iff
  no two hubs are adjacent**, and otherwise the phase's own problem one level
  down ((BE-65)(i)). And (BE-64)'s parametrization **is** §(K-chart) *Step
  CH3*'s tower, the source of `widened.place_pencil_general` — so (CH-1)(a)/(e)
  already supply irreducibility, rationality over ℚ and **dense ℚ-points**,
  cited rather than re-proved, with its three hypotheses (`hcard`, min degree
  2, girth `≥ 4`) checked at **7/7** battery pieces ((BE-65)(ii)). A
  by-product worth recording: the arc's standing sampler cap **is** `hcard`,
  i.e. (CH-1)'s hypothesis — not an artifact.
- **Job 3 / half (B), and BRNODE's open question answered.** At **28 peels**
  over 7 pieces — **14 of them peeling a THETA child**, which BRNODE's 24/24
  did not contain, reaching `θ(6,6,6)` and `|V| = 28` — the (BE-22)(i)
  identity is asserted at every one, welded attainment `ρ_i = δ_i` holds at
  every side, and the general-position shortfall is **0 at 28/28**. BRNODE
  asked whether its 24/24 was *"a theorem or a constructor artifact"*:
  **a theorem for each piece measured** — every quantity is an exact-ℚ fact
  about an exhibited configuration, `rank ≤ target` is universal, and
  (BE-22)(iii) is a biconditional *at a configuration* — and an artifact only
  as to the **class** ((BE-67)).
- **Verification.** `prod`: **495/495** branch restrictions legal at joint
  draws from **three independent samplers** (branch, `bsharp-adj`, `widened`)
  over 8 pieces including a **nested two-level R-node**; the branch-decorated
  law asserted as **spaces** at **69** draws, 0 mismatches; the **MIX** test
  (chains drawn in *independent runs*, then glued) gate-passing at **8/8**
  theta shapes. `theta`: **30/30** on the generic law and **30/30** on
  `ρ = δ`. `small`: **30/30** on `max(ambient, confined)`. `chart`:
  **15/15** deficiency-oracle cross-check, **7/7** cross-sampler agreement.
  `attain`: 28 peels, 0 shortfalls. Exact ℚ, seed literal `20260901`,
  `assert_generic_star` **and** `verify_pencil_witness` on every draw;
  `validate` **≈ 182 s** in one foreground invocation. Caps disclosed in the
  workbook: the greedy hub placement, the minimum-over-draws convention, the
  one-constructor `attain` battery, and — the one that matters — **`G` is
  never shown nonempty in general**, so a *forced-empty* proviso would be a
  cross-branch obstruction (BE-64)(ii) does not see.
- **F12 hunks at originating prose:** (BE-62)(iii)'s *"open in general"*
  (closed) and its *"achievable by pencil configurations"* quantifier
  (sharpened to the attaining locus), both annotated at source in the BRNODE
  section. **Nothing refuted; not a PENCIL event** — `hK`, (GR-15), class
  uniformity, `hbareSplit`, (BE-14), the 2-cut step, S-mark, (BE-32)(+) and
  BWIN's window theorem untouched. E1/E2 NO; E3 still ARMED (GBAL), not
  fired. Reservation **fully consumed** ((BE-64)–(BE-68), *Steps BE63–BE67*),
  nothing returned; the successor tail opens at **(BE-69) / *Step BE68***.
  Harness chain now **TWELVE** deep (`… → brnode → bdecor`), `bwin.dehom`
  gains its second consumer (tripping the §2 rule-2 threshold) and `brnode`
  its first — **no move made**.
- **Ranked successors:** (1) **half (B)'s class quantifier** ((BE-67)(iii)) —
  now one statement per piece about one *irreducible* variety, with both
  failure modes named and both currently unwitnessed; the species BWIN's
  opaque-subspace theorem already closed once. (2) **The flag base off the
  no-adjacent-hubs class** ((BE-65)(i)) — a pencil-realization problem for
  `B_real`, small but the phase's own kind. (3) **The cross-branch
  genericity proviso `G`** — hunt a piece where it is *forced empty*; that
  would be the direction's own first refutation. (4) BWIN's standing ranking
  (the one-end-series case, the spread step, (S1)/(S2)), unchanged.

## BPEEL — fifty-fourth ordinal, the sixty-second direction (single dispatch, prepped 2026-09-01)

**Selection provenance: BDECOR's residue (1), taken after the coordinator re-ran
the consumer trace — F26, again by name.** Two directions in a row have now had
their successor ranking re-checked rather than inherited, because this arc's
worst episode was five directions ordered by the previous one's successor list.
The trace: **(BE-22)(iii)** needs `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)` at the peel,
under the hypothesis that **both pieces attain**. **(BE-67)(iii)** states exactly
that over the parameter space BDECOR made explicit. It is the consumer's
remaining input. Dispatched **un-named, single**, at **`recon-opus`** — the
mapped rung is the top one (a class statement over new mirror math), and fable is
unavailable this session, so the playbook's named substitute applies.

### The target, stated exactly

> **(BE-67)(iii).** For **every** internal R-node piece `H`: some point of
> `Chart(H)` — a legal flag assignment on the hub set `W`, then an independent
> (BE-30)(ii)/(iii)-legal chain per topological branch — makes **both peel sides
> attain** and puts **`ρ̄₁, ρ̄₂` in general position**.

**Two identified ways to fail, each already separately discharged:** the welded
half (BE-22)(iii)(a), **free at theta children** by (BE-66)(ii); and the
general-position half, whose **only located enemy** is (BE-66)(iii)'s flag
coincidence, **unforceable at an R-node peel** by (BE-66)(iv) (a virtual edge's
ends are non-adjacent, and (BE-15) needs `x ∼ y`).

### THE CRUX — read this before planning

**The open question is not either failure mode; it is whether they are the ONLY
two.** (BE-66)(iii)/(iv) is a *located* claim — BDECOR found two mechanisms and
discharged both — and **nothing in the arc proves there is no third**. So the
deliverable is an **exhaustiveness** argument over an explicit irreducible
variety, not a new geometric mechanism. Treating *"no third mechanism found"* as
*"no third mechanism"* is the one move this spec forbids outright: it is F11's
own rule, and (BE-66)(iii)'s own wording — *"only **located** enemy"* — is the
disclosure that makes the gap visible.

### What is free — cite it, do NOT re-derive it

- **(BE-64)**, BDECOR: the branch-product theorem — at a fixed legal flag
  assignment, `Config(H; ϕ) ≅ (∏_b Ear(a_b; ϕ)) ∩ G`. **The `∩ G` is part of the
  theorem** (see job 2); a summary that drops it was repaired at `db2deb03`.
- **(BE-65)**, BDECOR: the flag base **is** §(K-chart)'s own tower, so **(CH-1)**
  supplies irreducibility, rationality and dense ℚ-points — its three hypotheses
  checked 7/7. Free iff no two hubs are adjacent; otherwise a pencil-realization
  problem for the hub subgraph ((BE-65)(i), open, ranked).
- **(BE-66)(i)/(ii)**: the theta corollary — generic
  `dim ρ̄ = max(0, Σ_j min(a_j,6) − 12)`, welded attainment **FREE** (`ρ = δ`,
  30/30).
- **(BE-66)(iii)/(iv)**: the flag-coincidence mechanism, and its unforceability
  at an R-node peel.
- **(BE-67)(i)/(ii)**: half (B) holds at **28/28** measured peels as **per-piece**
  theorems — 14 with a theta child. Per-piece, **not** class.
- **(BE-54)–(BE-58)**, BWIN: the **opaque-subspace** machine — double peel,
  modular law, an arbitrary middle subspace carrying the quantifier, an excess
  budget. BDECOR says this target *"is the shape BWIN's opaque-subspace theorem
  had, one level up"*. **That is a coordinator-relayed sentence, not a proof** —
  see job 3.
- **(BE-30)(ii)/(iii)**: the ear achievable sets, at fixed flags, with the
  small-`m` correction that BDECOR showed propagates through a P-node.

### Job 1 (PRIMARY, FORCED) — the class statement

Prove it uniformly over internal R-node pieces, or reduce it to a named checkable
condition, or exhibit a piece where every point of `Chart(H)` fails. **An
exhaustiveness argument is what is wanted**; more per-piece witnesses are not
progress on a class statement, exactly as (BE-46)(iv) said one level down.

### Job 2 (FORCED) — the `G` question, in its sharp form

BDECOR disclosed that the cross-branch proviso `G` is **never shown nonempty in
general** and named a forced-empty `G` as the first thing to hunt. **The
coordinator sharpens what "fatal" means, and this is a correction to how the gap
reads:** the class statement is **existential over the whole chart**, so `G`
empty at an *isolated* flag is **absorbed** — another flag serves. The fatal case
is a piece where `G` is empty at **every** legal flag. **Hunt that**, and if you
find only isolated emptiness, say so — it downgrades the gap rather than closing
it, which is a result.

### Job 3 (FORCED) — does BWIN's machine transport?

> **COORDINATOR OBSERVATION — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md`
> §7).** *Provenance:* BDECOR's own closing sentence, relayed here **as a
> hypothesis, not a finding** — it is a shape comparison, and BDECOR did not
> attempt the transport.
>
> BWIN closed a class statement of similar shape by making the middle an
> **arbitrary subspace** and paying an **excess budget** with one rank-1
> functional, so no enumeration of shapes was needed. Here the analogue would
> make the *other peel side* opaque and carry the quantifier the same way. **Say
> whether it transports.**
>
> *Where the coordinator expects to be wrong:* BWIN's leverage was that the ends
> acted on the middle through **one hyperplane and one functional** — a rank-one
> interface forced by the series structure at both ends. An R-node peel has **no
> series ends**; the interface is a whole 2-cut, so the budget argument may have
> nothing to bound. If so, say it in a paragraph and do not force the analogy.
> Five of the last six coordinator predictions in this arc were refuted, split or
> reframed; BRNODE and BDECOR both confirmed theirs, which is not evidence of
> accuracy.

### What counts as a HIT — state which you got

1. **The class statement PROVED** — half (B) closed for internal R-node pieces.
   With (BE-64)/(BE-65) that would leave the 2-cut lemma's general-piece side
   standing on the flag base ((BE-65)(i)) and cross-pair welding alone. Report
   the board and phase-boundary consequence; **act on neither**.
2. **Reduced** to a named checkable condition.
3. **The exhaustiveness question settled negatively** — a **third** failure
   mechanism exhibited. That re-ranks the board and is a HIT.
4. **`G` settled** (job 2) — forced-empty found, or shown absorbed.
5. **BWIN's machine priced** (job 3), either way.

### Bars

- **Do not re-open:** the branch-product theorem ((BE-64)); the
  decorated-skeleton law ((BE-59)/(BE-60)); the ear-decomposition induction
  ((BE-43)); the path-intersection bound ((BE-31)(iii)); **(b3)** ((BE-50)); the
  sharpening ((BE-45)); the proviso ((BE-46)); the `G²` apparatus ((BE-17)); the
  transversality count ((BE-16)(iv), (BE-27)); gauge-fixing (ZSHEAR).
- **ZJACOB (JC-6):** no properness, smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness — and this
  target sits on an irreducible variety, which is exactly where that temptation
  is strongest. Label every dimension count **as a count** ((BE-27)).
- **Not this direction, ranked separately:** the flag base off the
  no-adjacent-hubs class ((BE-65)(i)); the one-end-series case; the spread step;
  **(S1)/(S2)**; cross-pair welding ((BE-28)(i)).
- **Out of scope:** `hK`, **(GR-15)**, **(RS-5) and the (K-res) wave (a USER
  call)**, class uniformity, W4, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F11 is
this direction's central rider:** *"the only two failure modes"* is an
**exhaustiveness** claim and needs a driver that **enumerates**, or an argument
that needs no driver — a search that finds no third mechanism is *"none found
under cap C"*. **F27** — a claim that a piece **fails** needs multiple
independent draws, stated; an exhibited attaining point is a proof for that
piece. **Cap disclosure MANDATORY.** **F25** — verification off the **shipped**
driver; exact ℚ, printed literal seeds, `assert_generic_star` **and**
`verify_pencil_witness` on every draw. **F12** — a corrected summary needs a hunk
at the **originating prose**. **F17** — the fan-out header and
`notes/Phase39.md`'s `**Status:**` header are surfaces a landing must update.
**And the lesson from `db2deb03`, which is this arc's fourth instance:** when
your theorem carries a proviso or a modulo-clause, **carry it onto every surface
that summarizes the theorem** — the gap-map row above all, since it is
authoritative for every status word. **Read `notes/scripts/README.md` *Harness
debt***; the chain is **twelve** deep (`… → brnode → bdecor`), fourteenth
`kbare/` consumer — extend the consumer list, **make no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/bpeel.py`

Extend `bdecor.py` (and through it `brnode`/`bwin`/`brule`/`bsharp` and the rest
of the chain) by **read-only import**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BPEEL".) §(K-bare-ext)
**extends**, no new section; labels **(BE-69)–(BE-73)**, ***Steps BE68–BE72***,
exactly the tail BDECOR declared. `BPEEL`, `bpeel`, `(BE-73)` and *`Step BE72`*
verified **0-hit**; **`(BE-69)` has two hits and *`Step BE68`* one**, all tail
POINTERS (`Pencil-fanout.md:8090`, `Pencil-labels.md:2323`), opened and
confirmed. **Return any unconsumed remainder.** **Checked and NOT chosen:**
`BCLASS` — rejected on the **(L5) substring rule**, 3 hits as `BCLASS` and 19 as
`bclass`; `BCHART` and `BFIBRE` (both 0-hit) name the method's frame rather than
the question's site, and job 3 may find the chart is **not** where the argument
lives.

### Budget — measured at this prep, and THIS ONE BINDS

**`(K-bare)` is at 1 518 / 1 600 words — 82 of headroom, and the landing will
not fit.** Per F21 a recompute is dispatched **with a target, not "under the
cap"**: bring the row to **≈1 150 words** by rewriting *Steps BE14–BE33*'s
per-direction history (BZAVOID/BINDUC/BTWOCUT/BIMAGE) as current state — the row
already flags it as the workbook's, not the cell's — which leaves room for this
landing **and** the ones queued behind it. **Verify label preservation by
scripted set-diff, never by eye** (a coordinator hand-recompute once dropped a
live label). `notes/Phase39.md` is at **545/580 lines, 484/525 header words**;
the *Citations* relocation bought the room, and the next relocation candidate is
named in the note's own *Doc debt* bullet.

### BPEEL — landing write-up (LANDED 2026-09-01, recon-opus, single design-pass commit)

**HIT shapes 2, 4 and 5. NOT shape 1 and NOT shape 3.** The class statement is
**not proved**; **no third failure mechanism is exhibited**, and none is claimed
to be absent. Mathematics `notes/Pencil-informal.md` §(K-bare-ext) *Steps
BE68–BE72* ((BE-69)–(BE-73)); driver `notes/scripts/w4/bpeel.py`
(`open|indep|law|force|gate|validate`).

**THE CRUX, ANSWERED THE ONLY WAY IT CAN BE.** The spec forbade reading
(BE-66)(iii)'s *"only **located** enemy"* as *"no third mechanism"*, and this
landing does not. It answers instead by **bounding what any mechanism can depend
on**:

1. **(BE-69), THE DICHOTOMY — PROVED.** `Good(H) := {both sides attain} ∩
   {dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)}` is **Zariski-open** on `Chart(H)` — the `δ_i`
   are combinatorial constants, so both conditions are plain rank **lower**
   bounds (labelled as counts, ZJACOB (JC-6)), and on the attaining locus the
   coranks are constant, making `ρ̄_i` the image of a bundle map. `Chart(H)` is
   **irreducible** by (BE-65)(ii)/(CH-1)(a), so `Good` is **DENSE or EMPTY**.
   Three consequences: one draw settles a piece **generically** (upgrading
   (BE-67)(ii)); a failing draw settles nothing, and the asymmetry **is** the
   semicontinuity direction (F27); and **a failure is never a phenomenon at a
   special point**. Measured signature: **16/16** peels where the first draw is
   already at the maximum over five.
2. **(BE-70), THE PEEL-INDEPENDENCE THEOREM — PROVED.** No topological branch
   crosses the peel's 2-cut (both terminals are hubs; branch interiors have
   degree 2) — **asserted 96/96**. So at a fixed flag assignment `ρ̄₁` and `ρ̄₂`
   are functions of **disjoint coordinate blocks** and, **modulo `G`**, the
   achievable pairs are the **full product**. **The two sides share exactly one
   datum: the flag pair.** Measured by a **CROSS-MIX** test — side 1's chains
   from one run, side 2's from another, at one fixed flag assignment: **42/42**
   gate-passing, **36** realizing a pair neither parent run drew.
3. **(BE-71).** Two lower bounds transfer from (BE-33)(ii) — the core, and the
   **two-sided confinement** in the shared `Z`. **Completeness is explicitly not
   claimed.** The direction's own third-mechanism candidate — two totally
   singular 3-spaces of the **same Klein ruling** always meet — is **examined
   and set aside**: the only landed confinement to a totally singular 3-space is
   `ρ̄ = Λ²π` at `π_x = π_y`, and the plane is the **shared** one, so the two
   β-planes are equal and the candidate collapses into the confinement.

**JOB 2 (`G`) — CLOSED on (CH-1)'s class, and the argument needs no driver.**
(BE-64)(ii) is a **bijection**, so `Chart(H)` is the union over flags of
`(∏ Ear) ∩ G`; hence **`G` empty at every legal flag ⟺ `Chart(H) = ∅`**, which
**(CH-1)(a)** forbids under `hcard` + min degree 2 + girth `≥ 4`. The
coordinator's sharpening is what makes that enough: isolated emptiness is
**absorbed**. Isolated emptiness is **real** — the named control, a **triangle
on two hubs**, has `G` **empty at 120/120** drawn flags with `π_z ≠ π_{z'}`,
which is (BE-30)(iii)(c) read as a `G` statement and exactly what girth `≥ 4`
excludes. **(BE-72)**.

**JOB 3 (BWIN's machine) — DOES NOT TRANSPORT, AND NEED NOT.** The
coordinator's stated expectation is **CONFIRMED for the reason given**: an
R-node peel has no series ends, the interface is a whole 2-cut, and the excess
budget has nothing to bound. What replaces it is **stronger**: (BE-70) carries
the quantifier by a **bijection** rather than a bound — the two sides are not
opaque to each other, they are **independent**. **(BE-73)(v)**.

**THE CORRECTION, AND THE RE-RANKING — the direction's most useful sentences.**
**(BE-66)(iv)'s stated reason is REFUTED (F12, annotated at source).** It says
*"the only landed mechanism forcing `π_x = π_y` is BZAVOID's triangle
propagation, which needs `x ∼ y`"*; that misses **(BE-15)(ii)'s own inline scope
correction**, which records the **general** rule as landed, triangle-free and
adjacency-free (`K_{3,3}`), implemented as `binduc.flat_forcing_closure`.
**`K_{2,3}` forces `π_u = π_v` at a non-adjacent pair** (asserted). **The
conclusion stands by a different and stronger argument**: one-sided forcing gives
`δ_i = 0` by **(BE-32)(+)**, and **(BE-22)(vi)** then removes the
general-position half outright — so the enemy is **self-defeating** wherever it
is one-sidedly forced, whatever the mechanism. The whole-piece reading of
(BE-32)(+) is **near-vacuous at a 2-cut**, because `δ_{uv}(H) = max(0, δ₁+δ₂−6)`
(proved from (BE-21)+(BE-18), **asserted at 19 991 peels**). **So the residue is
CROSS-CUT-ONLY forcing, and its proof obligation is the SPREAD step
((BE-41)(ii)) — which promotes the spread step from "the last 3.8 % of
(BE-32)(+)" to the last gap in half (B)'s discharge.** That is a board move, and
it is reported, not acted on.

**THE ENUMERATION (F11's requirement), with its cap and its non-vacuity.** Three
censuses, two independent enumerators. **Census 1** (all 2-cuts with `u ≁ v` of
every 2-connected graph; exhaustive `n ≤ 6`, 3 000 masks at `n = 7, 8`, max
degree `≤ 4`): 8 759 graphs, 13 004 peels, **5 704 forced**, 408 forced with both
`δ` positive, **0** R-node-shaped — *and the non-vacuity check disqualifies that
0*, since the tier carries **no** R-node-shaped peel with both `δ` positive.
**Recorded rather than smoothed, and it is why census 3 exists.** **Census 3**
(constructed: every branch-length profile of the `K₄` skeleton at lengths 1–4,
plus 1 500 seeded profiles each of the prism and `K_{3,3}`): **38 758** peels,
all R-node-shaped, **24 874** with both `δ` positive, **180** forced, **0** in
the intersection. **Census 2** (`btwocut.two_cut_census`, both `δ` positive by
construction): 12 756 instances, **0** non-adjacent-and-forced. **Total 3 497
forced R-node-shaped peels, every one with `min(δ₁,δ₂) = 0`.** *"None found
under cap"*, never *"there is no third mechanism"*.

**AND ONE POSITIVE FACT THE NULL RESULT CARRIES: the R-node hypothesis is
LOAD-BEARING.** Off the R-node shape — at P- and S-node peels, which
(BE-67)(iii) does **not** quantify over — forcing with both sides flexible is
**common (408 instances)**. A successor that widens the quantifier past internal
R-node pieces loses this discharge immediately.

**Caps, disclosed.** The enumeration is capped (exhaustive only at `n ≤ 6`, max
degree `≤ 4`; constructed tier one skeleton family). The aggressive closure
**over-claims** forcing, so *forced* is a candidate and *not forced* is sound —
the direction the hunt needs. `rnode_shaped` is a **computable stand-in** for
*"virtual edge of a simple 3-connected SPQR skeleton"*, not an SPQR
implementation, and says so wherever quoted. `open`/`indep` run on **one
constructor** (BDECOR's `R_BATTERY` plus the nested piece) and quote the
**maximum** over seeded draws — the opposite convention to BDECOR's `theta`,
because `dim` of a **sum** is lower semicontinuous. Both (BE-69)(ii) and
(BE-72)(iii) stand on **(CH-1)(a)**, *proven-informally* with three hypotheses,
so every class statement here is a statement **about that class**.

**Nothing landed is refuted except one stated reason.** `PencilPair K 3 G`,
`hbareSplit`, (BE-14)-for-all-`G`, the 2-cut step, S-mark, (BE-32)(+), BWIN's
window theorem and (BE-64)–(BE-67) are untouched. **Not a PENCIL event**; **E3
armed, not fired**; the phase-boundary consequence is **reported, not acted
on**.

**Reservation FULLY CONSUMED** — (BE-69)–(BE-73), *Steps BE68–BE72*; nothing
returned. **Gap-map recompute, dispatched with a target (F21):** the `(K-bare)`
row went **1 511 → 1 228 words** (gate's count; 1 600 cap), headroom **89 →
372**, by rewriting *Steps BE14–BE33*'s per-direction history as current state.
**Label preservation verified by scripted set-diff, not by eye: 0 of 56 labels
dropped, 5 added**; eight *clause* qualifiers (e.g. `(BE-22)(iii)`) were folded
into their parent label and each was verified **body-present** by the same
script (6–26 occurrences each). The row now also **names (S1)/(S2)** where it
previously only described them — the `db2deb03` lesson applied forward. The
landing lands at **1 228** against the spec's **≈1 150** target: the remaining
~80 words are the five new labels and their headline block, and cutting further
would drop live status rather than history.

**Successors this direction names**, in its own ranking: (1) **the SPREAD step**
((BE-41)(ii)) — now the last gap in the discharge, pure graph theory, and it was
already ranked; (2) **cross-cut-only forcing** at an R-node peel with both sides
flexible — combinatorial, driver-findable, none found under cap; (3) the
**uniformity of `reach`** over the class, which is what (BE-67)(iii) now
literally is; (4) the **flag base** off the no-adjacent-hubs class ((BE-65)(i)),
unchanged and untouched here.

## BSPREAD — fifty-fifth ordinal, the sixty-third direction (single dispatch, prepped 2026-09-01, **LANDED 2026-09-01**)

**Selection provenance: BPEEL's successor (1), and the hand-off's candidate 1 —
but the F26 consumer trace was re-run for the THIRD direction running, and this
time it did not merely confirm the ranking, it CORRECTED THE TARGET.** The trace
opened both consumers. **(BE-73)(ii)(b)**: one-sided forcing gives `δ_i = 0` by
(BE-32)(+), and (BE-22)(vi) then removes half (B)'s general-position content
outright — so the discharge inherits (BE-32)(+)'s residue exactly. **BRULE job
2**: the ear side's (β) ledger carries *"the `π_u = π_v` corner ((BE-32)(+),
forced branch)"* as a named residue ((BE-58)(iv)). Both consume (BE-32)(+) at the
**pair** level, so the ranking survives its own check. What did not survive is the
**statement**. Dispatched **un-named, single**, at **`recon-opus`** — the mapped
rung is the top one (this may re-route the (BE-14) thread and it settles new
mirror math), and fable is unavailable this session, so the playbook's named
substitute applies.

### THE CORRECTION — read this before anything else

**The sentence three surfaces call "the spread step" is REFUTED AS STATED, by its
own sibling, and the refutation is enforced by the shipped driver.**

> **(BE-41)(ii)** *(as landed)* What is left of (BE-32)(+) is **every
> aggressively-forced pair lies in one `≤6`-cycle class** … Measured: **203 723**
> forced pairs, **`0`** outside a `≤6`-cycle class.

> **(BE-41)(iii)** *(as landed, same direction)* Let `t₀ … t_k` be a path, let
> `x_i` complete the triangle `(t_i, t_{i+1})`, and let `v` be joined to `t₀`, to
> `x_{k−1}` and to a pendant. The closure admits every `t_i` and then admits `v`
> on `{v, t₀, x_{k−1}}` — and the **shortest cycle through `v` has length
> `k + 2`** … the `k ≥ 5` members have shortest cycle `7` and `8` and are **NOT**
> in a common `≤6`-cycle class with `t₀`.

`(v, t₀)` is an aggressively-forced pair lying in **no** `≤6`-cycle class. So
(BE-41)(ii) is **false as a universal statement**, and BEARFULL **said so in
prose** — *"the `≤6`-cycle certificate is not merely unproved past 6, it is
**absent**"*. The coordinator verified it **off the shipped driver, not off the
prose** (`RESEARCH-ARC.md` §4's own standard): `bearfull.py chain` carries

```
assert esc, 'the boundary family produced no escape -- the claim is empty'
```

and, at every member, `assert spread_ok` (no witness triple makes the step
star-2) and `assert ... r[5] == 0` (`δ = 0`). **The escape set is asserted
NON-EMPTY.** `δ = 0` holds at all 8, so **(BE-32)(+) itself is untouched** — what
is dead is the `≤6`-cycle **route** to it.

**Where the defect actually sits, stated fairly.** BEARFULL wrote both halves. The
damage is in the **summary surfaces** that re-stated (ii) without (iii)'s
carve-out, and in the two **downstream consumers** that then inherited the wrong
form as the thing to prove:

1. **BEARFULL's confidence table** — *"(BE-41)(ii) forced ⟹ `≤6`-cycle class |
   **MEASURED** at 203 723 + 27 414 pairs, 0 escapes"*. Those are the two
   **random/enumerated** tiers; the **constructed** tier escapes by design and is
   tabulated on the *next row* as if it were a different claim.
2. **BEARFULL's cap 3** — *"It reads 'no aggressively-forced pair outside a
   `≤6`-cycle class was found under this cap', never 'none exists'."* That is
   **weaker than the truth**: one is known to exist, by construction. A cap
   disclosure that under-reports a known refutation is the F11/§5 hazard running
   backwards.
3. **(BE-41)(ii)'s own measurement line**, which reports `0` escapes with no
   pointer to (iii).
4. **BPEEL (BE-73)(iv)** — *"Its proof obligation is the **SPREAD step**
   ((BE-41)(ii))"* — and BPEEL's *What would change this* — *"A proof of the
   SPREAD step ((BE-41)(ii)) would upgrade (BE-73)(ii)(b) … to a theorem"*. Both
   name a statement that has a counterexample.
5. **`notes/Phase39.md`'s hand-off candidate 1**, which stated the `≤6`-cycle
   form verbatim — **corrected in this prep's own commit**, along with the note's
   in-flight block.

The **`(K-bare)` gap-map row is CLEAN** and was checked: it says *"residue the
geometry-free **SPREAD step** ((BE-41))"*, naming the label family, not the
refuted clause. Do not "fix" it into the refuted form.

### The target, stated exactly

> **(BE-32)(+), at the spread steps.** Let the aggressive closure admit a hub `v`
> on the strength of three points `x, y, z ∈ N[v] ∩ A` **no two of which lie in a
> common closed star** (a **SPREAD** step — the complement of (BE-41)(i)'s
> star-2 step). Show that the resulting forced pairs still satisfy
> **`δ = 0`** — or restrict the closure operator so that spread steps do not
> produce forced pairs at all — or exhibit a genuinely-forced pair with
> `δ ≠ 0`.

**55 of 401 544** forcing steps are spread steps; **7 680 of 203 723** pairs
(3.8 %) are unproved because of them. Pure graph theory: no configuration, no
genericity, no constructor. **The merge inequality cannot be the tool** — a
6-cycle of `Q` is tight and a 7-cycle has slack `−1` (`5·7 = 35 < 36`), which is
(BE-41)(iii)'s own reason the boundary family exists.

### THE COORDINATOR'S ROUTE HYPOTHESIS — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md` §7)

> *Provenance, named as §7 requires:* this is **not** measured and **not**
> derived from any landed step. It comes from **one docstring** —
> `binduc.flat_forcing_closure`'s — plus BEARFULL's own successor sentence
> (*"a successor needs a different tool **or a restriction of the closure
> operator**"*). Evidence stratum: **a comment and a sentence**. Five of the last
> seven coordinator predictions in this arc were refuted, split or reframed.
>
> The docstring says the closure is *"**Aggressive** = assumes every 3 forced
> points are independent, which **OVER-claims** forcing; a hit is a
> **CANDIDATE**"*, and the implementation is exactly `len(star & A) >= 3` — a
> count of **vertices**, with **no independence test at all**. The genuine rule
> needs three points of `N[v]` in `π` that are **not collinear**; three collinear
> ones force nothing. So the aggressive relation is a **superset** of genuine
> forcing, and (BE-32)(+) for it is **strictly stronger than the consumers need**
> — both consumers ((BE-73)(ii)(b), BRULE job 2) quantify over *genuine*
> coincidences in *real* configurations.
>
> **The hypothesis:** at a spread step the three witnesses can be made
> **collinear** in some legal pencil configuration, so the step is not a genuine
> forcing certificate; dropping spread steps leaves the **star-2-only** closure,
> for which (BE-41)(i) already **PROVES** (BE-32)(+) outright. If that holds,
> (BE-32)(+) closes for genuine forcing with no new geometry.
>
> **Where the coordinator expects to be wrong.** (a) Collinearity of three
> specified vertices is a **realizability** question inside the pencil stratum,
> not a free choice — the rest of the pencil conditions may forbid it, and at a
> hub `v` the closed star is already coplanar, so the three witnesses lie in
> `π ∩ π_v` *only if* `π ≠ π_v`, which is what is being established, not
> assumed. (b) Blocking one derivation of a pair does not show the pair is
> unforced — **another** derivation may reach it, so the honest object is *"is
> there a legal configuration with `π_u ≠ π_v`?"*, one existential per pair, not
> a per-step veto. (c) The retreat changes the object (BE-32)(+) quantifies over,
> which touches **every** surface that cites it, including BINDUC's (BE-23)(ii)
> and BZAVOID's (BE-15) — a scope change, and it must be priced as one. **If the
> hypothesis is wrong, say so in a paragraph and do not force it**; the
> alternative half of BEARFULL's sentence — a *different tool* for the spread
> steps as they stand — is equally in scope and is job 1's other half.

### What is free — cite it, do NOT re-derive it

- **(BE-41)(i)**, the **star-2 step**: two of the three witnesses in one closed
  star (non-degenerate) ⟹ `v, w` on a common `3`- or `4`-cycle ⟹ `δ_{vw} = 0`
  by (BE-40), composing by (BE-39)(ii). **PROVED**, 401 489/401 544 steps.
  (BE-32)(ii)/(iii) are its base case, and **the first step is always of this
  shape**.
- **(BE-39)/(BE-40)**, the **short-cycle law**: `g` supermodular, `girth(Q) ≥ 6`,
  `δ = 0` an **equivalence relation**, and `δ_{xy} ≤ max(0, L−6)` on a common
  `L`-cycle. **PROVED**; and **(BE-40) cannot reach past 6** ((BE-41)(iii)).
- **(BE-41)(iii)**, the boundary family and its blind re-finding: **8**
  constructed members, `k = 3…6 ×` 1 or 2 pendants, plus **2 541** blind graphs
  at `n = 9…13` giving **27 414** forced pairs, **0** escapes in the blind tier
  and **3 802** direct `δ` computations, **0** violations.
- **(BE-73)(ii)(a)**, the 2-cut `δ` law `δ_{uv}(H) = max(0, δ₁+δ₂−6)`, asserted
  at **19 991** peels — and its consequence that the **whole-piece** reading of
  (BE-32)(+) is near-vacuous at a 2-cut, so only the **one-sided** reading has
  content.
- **(BE-73)(iii)**'s three censuses: **3 497** forced R-node-shaped peels, all
  with `min(δ₁,δ₂) = 0`; **24 874** both-flexible R-node peels, none forced;
  **408** forced-with-both-`δ`-positive instances **off** the R-node shape.
- **(BE-23)(ii)** and **(BE-15)(ii)**'s scope correction: the landed *general*
  forcing rule is triangle-free and adjacency-free (`K_{3,3}`, `K_{2,3}`),
  implemented as `binduc.flat_forcing_closure` — the **same operator** this
  direction is about.

### Job 0 (FORCED, CHEAP, FIRST) — confirm or refute the correction, then annotate at source

Re-derive the correction above **from the driver, not from this spec**, and say
which. If confirmed, land an **F12 hunk at every originating surface** — items
1–4 of *Where the defect actually sits* — restating (BE-41)(ii) in a form the
boundary family does not refute and repointing BPEEL's two consumer sentences.
**If the coordinator is wrong**, say so plainly and in full: that is a clean
result and it costs this direction nothing.

### Job 1 (PRIMARY, FORCED) — the spread steps

Close (BE-32)(+) at the spread steps by **either** half of BEARFULL's own
sentence — a **different tool** for the 55 steps as they stand, or a **restriction
of the closure operator** that removes them (the coordinator's hypothesis above is
one candidate restriction and is **not** privileged) — **or** exhibit a
genuinely-forced pair with `δ ≠ 0`. Per-instance re-measurement of the 55 is
**not** progress; (BE-46)(iv)'s rule applies one level up. A **reduction to a
named checkable condition** is a result.

### Job 2 (FORCED) — cross-cut-only forcing, the hunt BPEEL left sharpest

BPEEL's successor (2), and *"the sharpest single question this landing leaves"*:
a coincidence `π_u = π_v` forced at an **R-node-shaped** 2-cut peel by the two
sides **together**, inside neither alone, with **both sides flexible**. It is not
covered by (BE-73)(ii)(b) (which needs one-sidedness) and the whole-piece reading
is vacuous by (ii)(a). **None was found under BPEEL's cap.** Widen the cap, or
give an argument that none exists — and note that the same object is what job 1
governs, since a cross-cut-only certificate that is a **spread** step is exactly
where both gaps meet. **F11 binds:** *"none exists"* needs an enumeration; a wider
search that finds nothing reports *"none found under cap C"*.

### What counts as a HIT — state which you got

1. **(BE-32)(+) PROVED outright** — for the aggressive operator, or for a
   restricted operator that both consumers accept (say **which**, and price the
   scope change per (c) above). That closes the `π_u = π_v` corner of (β) **and**
   upgrades (BE-73)(ii)(b) to a theorem.
2. **Reduced** to a named checkable condition.
3. **A genuinely-forced pair with `δ ≠ 0`** — HIT shape 4 in BEARFULL's numbering,
   classified against (BE-23)(ii). Report the board consequence; **act on none**.
4. **Cross-cut-only forcing found** (job 2), or shown impossible under a stated
   argument.
5. **The correction landed** (job 0), either way.

### Bars

- **Do not re-open:** the short-cycle law ((BE-39)/(BE-40)); the star-2 step
  ((BE-41)(i)); the Grassmann bound ((BE-42)(i)); the ear-decomposition induction
  ((BE-43), S-mark's pin STANDS); the branch-product theorem ((BE-64)); the
  decorated-skeleton law ((BE-59)/(BE-60)); the peel-independence theorem
  ((BE-70)); `G` on (CH-1)'s class ((BE-72)); the `G²` apparatus ((BE-17)); the
  transversality count ((BE-16)(iv), (BE-27)); gauge-fixing (ZSHEAR).
- **ZJACOB (JC-6):** no properness, smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness. Label every
  dimension count **as a count** ((BE-27)).
- **Not this direction, ranked separately:** the one-end-series case;
  **(S1)/(S2)**; the flag base off the no-adjacent-hubs class ((BE-65)(i)); the
  uniformity of `reach` ((BE-67)(iii)); cross-pair welding ((BE-28)(i));
  BTWOCUT's bundle construction ((BE-29)(ii)).
- **Out of scope:** `hK`, **(GR-15)**, **(RS-5) and the (K-res) wave (a USER
  call)**, class uniformity, W4, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F11 is
this direction's central rider, and job 2 is where it bites:** *"no cross-cut-only
forcing exists"* is an **exhaustiveness** claim and needs a driver that
**enumerates**, or an argument that needs no driver. **F27** — a claim that a step
or pair **fails** needs multiple independent draws, stated. **Cap disclosure
MANDATORY**, and this direction has a live reason to take it literally: item 2 of
*Where the defect actually sits* is a cap disclosure that **under**-reported a
known refutation. **F25** — verification off the **shipped** driver; exact ℚ,
printed literal seeds, `assert_generic_star` **and** `verify_pencil_witness` on
every geometric draw. **F12** — job 0 **is** an F12 sweep; a corrected summary
needs a hunk at the originating prose, and BPEEL's own (BE-66)(iv) annotation is
the model. **F17** — the fan-out header and `notes/Phase39.md`'s `**Status:**`
header are surfaces a landing must update. **Read `notes/scripts/README.md`
*Harness debt***; the chain is **thirteen** deep (`… → bdecor → bpeel`), sixteenth
`kbare/` consumer — extend the consumer lists, **make no move**.

### Driver — expected, at the pinned path `notes/scripts/w4/bspread.py`

Extend `bearfull.py` (for `forcing_derivation`, `step_shape`, `cycle_classes`,
`tri_chain`, `g_exact` via `btwocut`) and `bpeel.py` (for the peel censuses) by
**read-only import**. The 55 spread steps are already enumerable by
`bearfull.py forced`; do not re-implement the closure.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BSPREAD".)
§(K-bare-ext) **extends**, no new section; labels **(BE-74)–(BE-78)**, ***Steps
BE73–BE77***, exactly the tail BPEEL declared. `BSPREAD`, `bspread`,
`(BE-75)`–`(BE-78)` and *`Steps BE74–BE77`* verified **0-hit**; **`(BE-74)` and
*`Step BE73`* have one hit each**, the tail POINTER in `Pencil-labels.md`, opened
and confirmed. **Return any unconsumed remainder.** **Checked and NOT chosen:**
`BFORCE`, `BSTAR` (both fail the **(L5)** substring rule) and `BINDEP` — rejected
because `bindep` hits as a substring **and** because it names the coordinator's
*hypothesised* mechanism rather than the question's site, which §7 warns against.

### Budget — measured at this prep

**`(K-bare)` is at 1 228 / 1 600 words — 372 of headroom**, recomputed to a target
by BPEEL one landing ago, so **no recompute is dispatched with this direction**;
the landing fits. **`notes/Phase39.md` is at 560/580 lines, 420/525 header
words** — the prep relocated the `**Status:**` header's (BE-14)-thread
per-landing detail **verbatim** to `notes/Pencil-structure.md` as **block 8**,
exactly the move the note's own *Doc debt* watch item named in advance, taking the
header 505 → 420 and buying **105** words where three prior folds recovered 2–5
lines each. Lines are the tighter of the two: **20 spare**.

### LANDING — BSPREAD, 2026-09-01, `recon-opus`

**Mathematics:** `notes/Pencil-informal.md` §(K-bare-ext) continuation
(direction BSPREAD), ***Steps BE73–BE77***, labels **(BE-74)–(BE-78)**.
**Driver:** `notes/scripts/w4/bspread.py` (`lemma|chain|peel|validate`).
**Reservation CONSUMED IN FULL; nothing returned.** **No `.lean`** — the
2026-08-05 hold binds.

**WHICH DELIVERABLE: HIT shapes 1, 2 and 5. NOT shape 3 and NOT shape 4** —
and shape 4 is not merely un-hit, it is **closed**: there is no
genuinely-forced pair with `δ ≠ 0` because there is no aggressively-forced one.

**THE RESULT, in one sentence.** (BE-39)(i) — the quotient sparsity law
`5 e_Q(S) ≤ 6(|S|−1)`, which BEARFULL extracted and spent on **cycles of `G`**
where it runs out at `6` — spent instead on the **closure's own admission
rule** proves (BE-32)(+) outright: at `|S| = 2, 3, 4` it says two blocks of an
optimal partition are joined by at most **one** edge of `G` and the quotient
`Q` has no triangle and no `4`-cycle, so a vertex `v` outside a block `B`
reaches `B` by an **edge route** or a **path route** and the three exclusions
(edge + path = triangle; two paths = `4`-cycle or two parallel edges; two edges
= one edge) leave `B` absorbing **at most two** points of `N[v]` — *exactly*
`{v, b}` when `v` has a neighbour `b ∈ B`, at most one otherwise. The closure
admits on **three**. **(BE-74)**.

**Job by job.**

- **Job 0 (forced, cheap, first) — the coordinator is CONFIRMED IN FULL, and
  the check was made from the driver.** `bspread.py chain` re-derives the
  boundary family from `bearfull`'s own shipped objects (`tri_chain`,
  `forcing_derivation`, `step_shape`, `cycle_classes`, `short_cycles`,
  `def3_fast`) and not from the spec: **8** members, escape set **asserted
  non-empty** with **4** members at shortest cycle `7` / `8`, every admitting
  step asserted a genuine spread step, `δ = 0` asserted at all 8. So
  **(BE-41)(ii) is FALSE as a universal statement**. **F12 hunks landed at all
  five surfaces** the spec named — BEARFULL's confidence-table row, its cap 3
  (the disclosure that under-reported a known refutation), (BE-41)(ii)'s own
  statement and measurement line, and BPEEL's (BE-73)(iv) plus its *What would
  change this* — and the `(K-bare)` gap-map row was **checked and not "fixed"
  into the refuted form**, exactly as instructed. **(BE-76)**.
- **Job 1 (primary) — HIT shape 1.** Not a per-instance re-measurement of the
  55, and not the coordinator's restriction: a **different tool**, which is the
  other half of BEARFULL's own successor sentence. The conclusion delivered is
  **stronger** than `δ = 0` (*no optimal partition separates a forced pair*),
  and it holds for the landed operator **and three widenings of it** — any
  admitted vertex, any seed, both — at 274 168 (pair, optimal partition)
  instances with `0` separations. **(BE-74)/(BE-75)**.
- **Job 2 (forced) — HIT shape 2, plus a vacuity correction.** The closure
  **factorizes at a peel** (39 736 runs, `0` violations): the run cannot cross
  the cut before a terminal is admitted, so the **first** terminal is always
  admitted one-sidedly and only the **second** terminal's admission can
  straddle. With (BE-74) on each side that forces the witness split to be
  exactly `(2,2)` in the shape `{v, b₁, b₂}`, and merging `[v]` into the block
  of `u` across that single edge gives **`δ₁ = δ₂ = 1`**. BPEEL's **408**
  off-R-node forced-both-flexible instances are **408/408** at `(1,1)` — a
  population BPEEL recorded as a bare count. And **`0`** of BPEEL's 24 874
  R-node both-flexible peels sit at `(1,1)`, so its census-3 zero had **`0`
  chances**, not 24 874. Re-aimed hunt: **43 763** R-node peels and **932**
  `(1,1)` peels over two independent tiers, intersection **empty** — *"none
  found under cap"*, never *"none exists"* (F11). **(BE-77)**.

**THE COORDINATOR'S ROUTE HYPOTHESIS — MOOT, and that is the cheapest of the
three possible verdicts.** It proposed **restricting** the closure (make a
spread step's three witnesses collinear, so the step is not genuine, leaving the
star-2-only closure). (BE-74) proves the statement for the **unrestricted**
operator and for three widenings, so the retreat is unnecessary and its own
item **(c)** — the scope change across (BE-23)(ii), (BE-15) and every citing
surface — is **never paid**. Its item **(b)** (*blocking one derivation does not
unforce a pair*) was **right**, and is exactly why a theorem about the
**over-claiming** operator is the better object: it holds a fortiori for genuine
forcing with no realizability question asked. Its item **(a)** is untested and
does not need to be. `RESEARCH-ARC.md` §7's tally: this is a coordinator
prediction neither confirmed nor refuted but **made unnecessary**, which is a
fourth outcome the §7 count has not seen before and should record as such.

**What this landing does NOT touch, said plainly.** `PencilPair K 3 G`,
`hbareSplit`, **(BE-14)**, the 2-cut composition lemma (S-mark), (BE-67)(iii)'s
class quantifier and the uniformity of `reach`, the flag base ((BE-65)(i)),
cross-pair welding ((BE-28)(i)), **(S1)/(S2)**, `hK`, **(GR-15)**, the (K-res)
wave, class uniformity of the escape. **Not a PENCIL event.** The
phase-boundary consequence of a HIT shape 1 is **reported, not acted on**
(`notes/Phase39.md` *On a future HIT*).

**Ranked successors this landing leaves.**

1. **Can an R-node-shaped 2-cut peel have `δ₁ = δ₂ = 1`?** — the whole of job
   2's residue, now **closure-free, geometry-free and combinatorial**: two
   deficiencies and one 3-connectivity test. Cheap, driver-findable, and a
   *no* closes half (B)'s last general-position enemy outright. **This is the
   sharpest single question this landing leaves**, and it is much sharper than
   the one it replaces.
2. **(BE-67)(iii)'s class quantifier** — the uniformity of `reach` over the
   class, BPEEL's own named successor, untouched here.
3. **The one-end-series case by BWIN's machine**, and **(S1)/(S2)** — both
   unchanged and still ranked.
4. **BTWOCUT's bundle construction** ((BE-29)(ii)), skipped five times.

**Riders.** **E1: NO. E2: NO** except two stated things — (BE-41)(ii) as a
universal statement (refuted by its own sibling; annotated here, not discovered
here) and (BE-73)(iii)'s non-vacuity **denominator** (corrected here); every
landed *measurement* stands. **E3: ARMED by GBAL, not fired.** **F11**: job 2's
zero is *"none found under cap"* and says so. **F27**: the negative is drawn in
**two independent tiers** built by different generators. **F25**: verification
off the **shipped** driver, exact integer arithmetic, printed literal seed
`20260901`. **F12**: five hunks at source. **F17**: fan-out header,
`notes/Phase39.md` `**Status:**` header, *Hand-off*, *Decisions made* and the
ROADMAP Status row all updated in this commit. **Harness debt**: the chain is
now **fourteen** deep (`… → bpeel → bspread`), **sixteenth** `kbare/` consumer;
**no move made**, consumer lists extended.

## BONEONE — fifty-sixth ordinal, the sixty-fourth direction (single dispatch, prepped 2026-09-01)

**Selection provenance: BSPREAD's own successor, and the F26 consumer trace was
re-run for the FOURTH direction running.** BSPREAD reduced job 2 — cross-cut-only
forcing at an R-node peel with both sides flexible, half (B)'s last
general-position enemy — to **one purely combinatorial question**, and the trace
confirms it is the consumer's remaining input rather than an adjacent one:
**(BE-22)(iii)** needs `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)` at the peel; **(BE-22)(vi)**
kills the general-position half outright when a side is rigid; **(BE-73)(ii)(b)**
now unconditionally supplies `δ_i = 0` whenever the forcing certificate is
one-sided, because **(BE-32)(+) is a theorem** ((BE-74)); **(BE-77)(i)** shows the
closure factorizes at a peel so only the second terminal's admission can straddle
the cut; and **(BE-77)(ii)** then forces `δ₁ = δ₂ = 1`. Nothing else stands
between the enemy and its discharge. Dispatched **un-named, single**, at
**`recon-opus`** — fable is unavailable this session, so the playbook's named
substitute applies to the mapped top rung.

### The target, stated exactly

> **Can an R-node-shaped 2-cut peel have `δ₁ = δ₂ = 1`?**
>
> Prove **no** — for the class the consumer needs — or exhibit a **yes** witness,
> or reduce to a named checkable condition.

**A `no` removes half (B)'s last general-position enemy outright.** A `yes` is not
a refutation of anything: it is a witness that must then be tested for
**cross-cut-only forcing** by (BE-77)(ii)'s exact certificate shape `{v, b₁, b₂}`,
which is cheap, and only a forcing witness re-opens the enemy.

### THE DEFINITIONAL ITEM THE TRACE TURNED UP — settle it in the first paragraph

**`rnode_shaped` is a per-SIDE predicate, and BSPREAD's census combines the two
sides with `or`:** `rn = rnode_shaped(E1,u,v) or rnode_shaped(E2,u,v)`
(`bspread.py`, coordinator-read off the body). Its own docstring is precise about
what it tests — *"is the side's skeleton, with the virtual edge `uv` put back and
every degree-2 vertex suppressed, SIMPLE and 3-CONNECTED?"*, rejecting a parallel
pair (P-node) and a degree-2 marked vertex (S-node) — and discloses that it is a
**stand-in** for *"`uv` is a virtual edge of a simple 3-connected SPQR skeleton"*,
not an SPQR implementation.

**Which side does the consumer actually need?** (BE-67)(iii) quantifies over
**internal R-node pieces** `H`, and the peel splits `H`. **State the answer
explicitly**, and note the safe direction while you are there: `or` makes the
R-node-shaped population **larger**, so *"no R-node-shaped peel is at `(1,1)`"*
under the inclusive reading implies it a fortiori under any narrower one. If the
consumer needs **both** sides R-node-shaped, the theorem you want is weaker than
the one the evidence is about — say so, and prove the one the consumer needs.

### The evidence, and why it points at a structural reason rather than a thin cap

- **Tier A** (`bspread.py peel`, random 2-connected, `n = 6…10`, **no**
  max-degree filter — BPEEL's census 1 carried one, which is why its R-node peels
  were rigid on one side): **16 800** peels, **5 005** R-node-shaped, **932** at
  `(1,1)`, **intersection empty**.
- **Tier B** (BPEEL's constructed subdivided-skeleton tier): **38 758**
  R-node-shaped peels, **`0`** at `(1,1)`.
- **The tier-A shape is the informative one**: *both* populations are large and
  *disjoint*. A thin cap would show a small intersection, not an empty one
  between two four-figure sets. That is a reason to look for a **theorem**, not to
  widen the search first.
- **BPEEL's census-3 zero is VACUOUS at this shape** and is corrected at source
  ((BE-77)(iii)): `0` of its 24 874 R-node both-flexible peels sit at `(1,1)`, so
  it had `0` chances, not 24 874. **Do not quote it as evidence here.**

### THE COORDINATOR'S ROUTE HYPOTHESIS — TO BE TESTED, NOT INHERITED (`RESEARCH-ARC.md` §7)

> *Provenance, named as §7 requires:* this is **arithmetic on landed laws plus the
> tier-A shape above**, not a derivation — and §7's tally now stands at five
> instances and four kinds (refuted, split, reframed, **moot** — BSPREAD's, one
> landing ago). Expect this one to be killed too.
>
> The three landed facts that look like they should meet: **(BE-20)**
> *3-connected ⇒ `def₂ = 0`*; **(BE-21)/(BE-23)**'s 2-cut `def₃` law
> `f = max(g₁+g₂, f₁+f₂−6)`; and **(BE-39)(i)** at `|S| = 2`, which BSPREAD just
> showed is the sharp tool for *"how much can one block see of another"*. An
> R-node-shaped side is 3-connected **after degree-2 suppression**, and `δ_i = 1`
> is the *minimum positive* deficiency drop — the same `−6 + 5·1 = −1` single-edge
> merge that (BE-77)(ii) *Step 3* uses in the other direction. **The hypothesis:**
> 3-connectivity of the suppressed skeleton forces `δ_i` away from exactly `1` —
> either to `0` (enough connectivity that merging `u,v` is free) or to `≥ 2` — so
> the `(1,1)` shape is excluded structurally.
>
> **Where the coordinator expects to be wrong.** (a) The suppression is doing real
> work and `δ` is *not* invariant under it — degree-2 vertices are exactly what a
> subdivision adds, and (SD-6) prices a subdivision at `ℓ − 6`, so a claim about
> the suppressed skeleton may say nothing about `H_i`. (b) "3-connected ⇒ `δ = 0`"
> is **not** a landed statement — (BE-20) is about `def₂` of the **whole** graph,
> not about a peel side's `δ`, and reading one as the other is exactly the
> level-confusion the playbook's P-rating calibration warns about. (c) The tier-A
> disjointness may be an artifact of the **generator**, not of the graphs: random
> 2-connected graphs at `n ≤ 10` with `m ≤ 2n` may simply not reach the region
> where both hold. **Test (c) before believing the hypothesis** — a widened
> generator that still finds nothing is worth more than an argument built on a
> sampling artifact.

### What is free — cite it, do NOT re-derive it

- **(BE-74)**, the block-absorption lemma, and **(BE-32)(+) as a theorem** — for
  the aggressive operator and three widenings.
- **(BE-77)(i)**, the peel factorization of the closure (39 736 runs, 0
  violations), and **(BE-77)(ii)**, the `δ₁ = δ₂ = 1` confinement with its exact
  certificate shape `{v, b₁, b₂}` — **including its stated hypotheses**: `u ≁ v`,
  both sides carrying an interior vertex, `δ_i ≥ 1`.
- **(BE-73)(ii)(a)**, `δ_{uv}(H) = max(0, δ₁+δ₂−6)`, asserted at 19 991 peels —
  note it gives `δ_{uv}(H) = 0` at `(1,1)`, so the whole-piece reading says
  nothing here.
- **(BE-39)(i)**, quotient sparsity, and **(BE-40)**, the short-cycle law.
- **(BE-18)/(BE-20)/(BE-21)/(BE-23)**, the decomposition's composition laws.
- **(BE-70)**, peel independence, and **(BE-69)**, the Zariski dichotomy — the
  geometry that makes this the *last* general-position item rather than one of
  several.

### Job 1 (PRIMARY, FORCED) — the question

Settle it. A **proof** is the deliverable; a wider search that finds nothing is
**not** a proof and reports *"none found under cap C"* (F11). If the answer is
**yes**, run (BE-77)(ii)'s certificate test on the witness in the same pass and
report whether the enemy actually re-opens — a `(1,1)` peel that is not
cross-cut-only forced changes nothing.

### Job 2 (FORCED) — what a `no` actually closes, stated against the consumer

If job 1 is **no**, write down precisely what half (B) then has left. The
coordinator's reading, **to be checked rather than transcribed**: the residue
becomes exactly **(BE-67)(iii)'s uniformity of `reach`** and **the flag base off
the no-adjacent-hubs class ((BE-65)(i))** — two items, no third. Confirm or
correct that, because it is what the next pick is chosen from.

### Job 3 (FORCED, CHEAP) — the harness question BSPREAD's chain raises

The `w4/` sibling-import chain is now **fourteen** deep (`… → bpeel → bspread`)
and this direction would be the **seventeenth** `kbare/` consumer. The standing
rule is **record, make no move** — a dispatch may not edit a landed driver
another direction may be importing in flight. **Follow it.** But state, in one
paragraph for the harness-debt list, whether a fifteen-deep chain is still
importing *devices* or has become a de-facto shared layer — the §2 rule-2
threshold question the debt list has been carrying since 2026-08-20 without a
verdict.

### What counts as a HIT — state which you got

1. **`No`, PROVED** — half (B)'s last general-position enemy is gone, and
   (BE-73)(iv)'s residue closes. Report the board and the phase-boundary
   consequence; **act on neither**.
2. **Reduced** to a named checkable condition.
3. **A `yes` witness**, with its forcing test run.
4. **The consumer's residue restated** (job 2), confirmed or corrected.
5. **The chain-depth verdict** (job 3).

### Bars

- **Do not re-open:** (BE-32)(+) / the block-absorption lemma ((BE-74)); the
  peel factorization and the confinement ((BE-77)(i)/(ii)); the short-cycle law
  ((BE-39)/(BE-40)); (BE-41)(ii), **refuted as stated and RETIRED, not repaired**
  ((BE-76)) — do not try to rescue the `≤6`-cycle form; the branch-product
  theorem ((BE-64)); the decorated-skeleton law ((BE-59)/(BE-60)); peel
  independence ((BE-70)); `G` on (CH-1)'s class ((BE-72)); the `G²` apparatus
  ((BE-17)); the transversality count ((BE-16)(iv), (BE-27)); gauge-fixing
  (ZSHEAR).
- **ZJACOB (JC-6):** no properness, smoothness or transversality from a
  codimension count, a Jacobian criterion, or Cohen–Macaulayness. Label every
  dimension count **as a count** ((BE-27)).
- **Not this direction, ranked separately:** (BE-67)(iii)'s uniformity of `reach`;
  the flag base ((BE-65)(i)); the one-end-series case; **(S1)/(S2)**; cross-pair
  welding ((BE-28)(i)); BTWOCUT's bundle construction ((BE-29)(ii)).
- **Out of scope:** `hK`, **(GR-15)**, **(RS-5) and the (K-res) wave (a USER
  call)**, class uniformity, W4, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — **E3 ARMED (by GBAL)**; report, never fire. **F11 is
this direction's central rider**: *"no R-node-shaped peel has `δ₁ = δ₂ = 1`"* is
an **impossibility** claim and needs a **proof**, or it reports *"none found under
cap C"*. **F27** — a claim that a peel **fails** a property needs multiple
independent draws, stated. **Cap disclosure MANDATORY**, and note that BSPREAD's
own (BE-77)(iii) is the live cautionary case: a zero read against the **wrong
denominator** is worse than no measurement, so state the denominator every figure
is over. **F25** — verification off the **shipped** driver; exact integer
arithmetic, printed literal seeds. **F12** — a corrected summary needs a hunk at
the originating prose. **F17** — the fan-out header and `notes/Phase39.md`'s
`**Status:**` header are surfaces a landing must update. **Read
`notes/scripts/README.md` *Harness debt*** before touching the harness; job 3 is
the only thing this direction says about it, and it says *record, no move*.

### Driver — expected, at the pinned path `notes/scripts/w4/boneone.py`

Extend `bspread.py` (for `rnode_shaped` via `bpeel`, the peel censuses, and the
`(1,1)` classifier) and `btwocut.py` (for `deltas_at` / `g_exact` /
`def3_multi`) by **read-only import**. Do not re-implement the deficiency
oracles; cross-check against `kbare_common.exact_deficiency` as the chain
already does.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BONEONE".)
§(K-bare-ext) **extends**, no new section; labels **(BE-79)–(BE-83)**, ***Steps
BE78–BE82***, exactly the tail BSPREAD declared. `BONEONE`, `boneone`,
`(BE-80)`–`(BE-83)` and *`Steps BE79–BE82`* verified **0-hit**; **`(BE-79)` and
*`Step BE78`* have two hits each**, both tail POINTERS in the registry, opened
and confirmed. **Return any unconsumed remainder.** **Checked and NOT chosen:**
`BRPEEL` (a reader-side collision with the landed `BPEEL`), `BFLEX` and `BDELTA`
(both 0-hit, both naming a hypothesis rather than the site — §7). **Prefer prose
names to new parenthesized tokens**, as BSPREAD did.

### Budget — measured at this prep

**`(K-bare)` is at 1 400 / 1 600 words — 200 of headroom.** That fits this
landing but leaves little behind it, so **if the landing does not fit, recompute
the row to a TARGET, not to "under the cap"** (F21), and **verify label
preservation by scripted set-diff, never by eye**. **`notes/Phase39.md` is at
565/580 lines, 450/525 header words** — **lines are the binding constraint here,
not words**, with 15 spare; the prep rotated the header's landed-direction block
rather than appending to it, and the landing should do the same. The next
relocation candidate, if one is needed, is named in the note's own *Doc debt*
bullet — and the *"On a future HIT"* block is **not** it.

### LANDING WRITE-UP — BONEONE, 2026-09-01: **YES, and the enemy is LIVE**

**HIT shapes 3, 2, 4 and 5; NOT shape 1.** The target was *"prove `no` for the
class the consumer needs, or exhibit a `yes` witness and run (BE-77)(ii)'s
certificate test on it, or reduce to a named checkable condition"*. The answer
is **`yes`**, the witness is **minimal**, the certificate test is **positive**,
and the coordinator's route hypothesis is **REFUTED** — its own item **(c)**,
*"the tier-A disjointness may be an artifact of the generator; test (c) before
believing the hypothesis"*, was right, and testing it first is what produced
the landing. `RESEARCH-ARC.md` §7's tally becomes **six instances and five
kinds** — refuted, split, reframed, moot, and now **refuted with its own named
escape clause vindicated**.

**Job 1's definitional item, settled in the first paragraph as instructed.**
The consumer needs the **`or`** reading, and not merely because it is safe:
(BE-67)(iii) quantifies over internal R-node **pieces**, and at a peel of such a
piece it is the **rest-of-piece** side whose skeleton is the R-node's, with
nothing known about the child — so *"some side is R-node-shaped"* is the only
hypothesis the consumer can actually supply. `WIT16` refutes the `and` reading
as well, so nothing turns on the disclosed stand-in.

**The method, and it is the transferable part.** *`δ_i` and `rnode_shaped` are
both **per-side**, and any two sides glue* ((BE-79)(i)). So the question was
never about peels: it asks whether **one** side can be R-node-shaped at
`δ = 1`. Searching *peels* for a conjunction of two independent *per-side*
properties is exactly what made two four-figure populations look like disjoint
sets instead of two independent draws from two different size regimes.

**The answer.** The side `H₁` on **9** vertices — skeleton `K₄` on `{u,v,C,D}`,
virtual edge `uv` absent, branch lengths `(1,1,1,6,1)` on `(uC,uD,vC,vD,CD)` —
has `δ = 1` and is R-node-shaped. Glued to `{ua,ub,ab,av}` (4 vertices,
`δ = 1`) it gives **`WIT11`**: an R-node-shaped 2-cut peel at `δ₁ = δ₂ = 1` on
**11** vertices, 14 edges, max degree 4. Two copies of `H₁` give **`WIT16`**.

**Why both tiers saw nothing, and neither reason is evidence** ((BE-80)). An
R-node-shaped side with `def₃ ≥ 1` has `|V| ≥ 7 + min_s[5s + φ(q−p−1−s)] ≥ 9`,
with `9` attained **only** at `q = p+2`, i.e. **only over `K₄`**; a side with
`δ = 1` has `|V| ≥ 4`; so the smallest R-node-shaped `(1,1)` peel has **11**
vertices — **one above tier A's `n ≤ 10`**. And **every** 2-cut of a subdivided
skeleton has a **path side**, whose `δ` is `min(L,6)` and never `1`, so tier B
— `bpeel.constructed_tier`, which by its own body yields a peel only at a
skeleton edge with `prof[i] ≥ 2` — had **0 chances at any cap**. *"43 763
R-node-shaped peels and 932 at `(1,1)`, intersection empty"* is `0` of `0`.
**This is the second consecutive landing whose finding is a denominator**, and
this time on the very measurement that motivated the direction.

**The forcing test, run as job 1 requires — and it comes back positive**
((BE-81)). Of the **48** R-node-shaped `(1,1)` peels on 11 vertices (exhaustive
over that class), **24** force `π_u = π_v`; 312 of 720 and 56 of 160 at
`n = 12`. Every certificate is exactly (BE-77)(ii)'s **`{v, b₁, b₂}`**, split
`(2,2)` by the cut, with the first terminal admitted one-sidedly as (BE-77)(i)
(b) requires and every step classified `star2` by `bearfull.step_shape`. So
**(BE-66)(iv)'s CONCLUSION is REFUTED**, not merely unproved; and its
*"the R-node hypothesis is LOAD-BEARING"* corollary is corrected — the
hypothesis **raises the size floor** from 4 vertices to 11, and both halves of
the comparison behind it were measured at `n ≤ 8`, where the R-node half cannot
occur.

**Job 2, corrected rather than transcribed** ((BE-82)). The coordinator's
reading — *"two items, no third"* — was written for a `no`, so it does not
apply: half (B)'s residue is **three** items, the two named plus the
**RE-OPENED** flag-coincidence enemy of (BE-66)(iii). **The price, stated as
one:** everything here is the **aggressive** operator, which over-claims. Every
consumer clause is *proved for* it, which makes each stronger than needed; a
**witness against** it is *weaker*, so the enemy is a **candidate**, not a
proven counterexample. What is certain is that the sufficient route is dead.
What is open is **genuineness** — whether `{v,b₁,b₂}` is three *independent*
points at a `Chart(H)` configuration, and whether a genuinely forced
coincidence actually drops `dim(ρ̄₁+ρ̄₂)` below `2`. Both are **geometric**,
so (BE-77)(iv)'s closure-free, geometry-free residue is neither again.

**Job 3, answered** ((BE-83)(iii)). *Record, no move* — followed. The verdict
the debt list has been owed since 2026-08-20: **fifteen deep is no longer a
device chain, and has not been since roughly the tenth link.** §2 rule 2 is
about a *device* with two consumers; `w4/` is a **stratified layer** whose
levels are the arc's **oracles**, not helpers. A helper moved down is a
refactor; an **oracle** moved down re-baselines every landed figure measured
through it, which is why every dispatch has correctly declined. The actionable
debt is therefore **not** a move-down but an interface decision — a
coordinator/user call, recorded, nothing moved.

**What did NOT move.** **(BE-32)(+) / (BE-74)** is untouched and still a
theorem; **(BE-73)(ii)(a)/(b)** untouched, **(b) still unconditional**;
**(BE-77)(i)/(ii)** untouched and **CONFIRMED on a live instance** — it is
their hypothesis `(1,1)` that turns out satisfiable; **(BE-14)**, `hbareSplit`,
S-mark, (BE-64), (BE-69)/(BE-70)/(BE-72), (BE-59)/(BE-60), the `G²` apparatus,
the transversality count, (S1)/(S2) and cross-pair welding all untouched.
BPEEL's 3 497 and 408 stand. **Not a PENCIL event**; the phase-boundary
consequence is **reported, not acted on**.

**Deliverable.** `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE78–BE82* /
**(BE-79)–(BE-83)**; driver `notes/scripts/w4/boneone.py`
(`side|bound|force|validate`, 54 s, `VALIDATE: OK`); the `(K-bare)` gap-map
row recomputed (1 474 words, label set-diff scripted); reservation **consumed
in full**. Run at **`recon-opus`** (fable unavailable this session).

## BGENUINE — fifty-seventh ordinal, the sixty-fifth direction (single dispatch, prepped 2026-09-01)

**Selection provenance: BONEONE's own successor, and the F26 consumer trace was
re-run for the FIFTH direction running.** BONEONE re-opened half (B)'s last
general-position enemy with 392 exhibited witnesses and named, in the same
breath, the clause that blunts its own result: **everything is the AGGRESSIVE
operator**, which over-claims forcing, so what it exhibited is a **candidate**
enemy, not a confirmed one. The trace confirms this is the consumer's remaining
input and not an adjacent question: **(BE-22)(iii)** needs
`dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)` at the peel, which at a `(1,1)` peel is **exactly
`2`**; the enemy bites only if a *genuine* coincidence pushes that sum **below
2**. Both halves of that sentence are **geometric**, and neither has been
measured. Dispatched **un-named, single**, at **`recon-opus`** — a verdict that
could produce a counterexample class for half (B) is top-rung-mapped, and fable
is unavailable this session.

### The target, stated exactly

At the witness family BONEONE printed (`boneone.py force`, **392** forced
R-node-shaped `(1,1)` peels across three exhaustive rows, minimal member
`WIT11`):

> **(a) GENUINENESS.** At a configuration of `Chart(H)`, are the three witnesses
> `{v, b₁, b₂}` of the admitting step **affinely independent** — so that
> `π_v` really is forced to the common plane — or does the aggressive operator's
> over-claim **evaporate** here, the three being collinear at every legal
> configuration?
>
> **(b) DOES IT BITE.** If genuine, does the forced `π_u = π_v` actually drop
> `dim(ρ̄₁ + ρ̄₂)` below `min(δ₁+δ₂, 6) = 2`?

**A `0` shortfall relabels the enemy harmless** and half (B) survives with its
residue unchanged in kind. **A positive shortfall is a counterexample class** to
half (B) as stated, and the direction says so plainly rather than softening it.

### THE PRICE THE OPERATOR EXACTS, AND WHICH DIRECTION IT CUTS

This is worth stating precisely because the arc has now used it in **both**
directions in consecutive landings and they are not symmetric:

- **A clause proved FOR the aggressive relation holds a fortiori for genuine
  forcing** — that is why (BE-74) is stronger than the consumers need, and why
  BSPREAD's theorem is safe.
- **A witness exhibited AGAINST it is weaker than a genuine one** — that is why
  BONEONE's 392 are candidates. **This direction is the one that converts, or
  fails to convert, a candidate into a real enemy.**

`binduc.flat_forcing_closure`'s own docstring is the source: *"Aggressive =
assumes every 3 forced points are independent, which OVER-claims forcing; a hit
is a CANDIDATE."* The word **CANDIDATE** is the landed disclosure this direction
discharges.

### What is free — cite it, do NOT re-derive it

- **(BE-79)–(BE-82)**, BONEONE: the per-side reduction, `WIT11` and `WIT16`, the
  two vacuous zeros, the forcing test at 392 witnesses, and the price.
- **(BE-77)(i)/(ii)**, the peel factorization and the `(1,1)` confinement with the
  exact certificate shape `{v, b₁, b₂}` split `(2,2)` by the cut — **every one of
  the 392 has this shape**, so the geometric question is about *one* configuration
  of *one* shape, not a family of shapes.
- **(BE-74)**, the block-absorption lemma, and **(BE-32)(+) as a theorem**.
- **(BE-69)**, the Zariski dichotomy: the good locus is **open** on the
  irreducible `Chart(H)`, hence **dense or empty**. **This is the instrument that
  makes (b) decidable by one draw** — a shortfall at a generic point is not a
  special-point artifact, and a non-shortfall at a generic point settles the
  piece. Use it, and label what it does and does not give.
- **(BE-70)**, peel independence: at fixed flags `ρ̄₁, ρ̄₂` are functions of
  **disjoint** coordinate blocks sharing only the flag pair. **Read this against
  (b) before measuring:** if the two sides are independent given the flags, then a
  forced flag *coincidence* is precisely the one datum that could couple them, and
  that is the mechanism (b) is asking about.
- **(BE-67)(i)**'s own instrument — the per-piece exact-ℚ draw — is what (b)
  should be measured with. **(BE-30)(ii)/(iii)**, the ear achievable sets, with
  the small-`m` correction.
- **(CH-1)** for irreducibility, rationality and dense ℚ-points of the chart, under
  its three hypotheses — **check `WIT11` against them by name**, since (BE-72)(iii)
  and (BE-69)(ii) both rest on them and a witness off that class makes both
  unavailable.

### Job 1 (PRIMARY, FORCED) — genuineness

Settle (a) at `WIT11` first and then across the family. **Note the asymmetry in
what a finding means:** *collinear at every legal configuration* is a class claim
needing an argument or an exhaustive-in-the-right-sense enumeration; *independent
at one configuration* is a **proof for that witness**, by the same openness
argument (BE-52) used one level down — state which you have. If the over-claim
evaporates at every witness, say so: that **closes** the enemy and is the best
outcome available here.

### Job 2 (FORCED) — does it bite

Measure the shortfall. `min(δ₁+δ₂,6) = 2` at every member of the family, so the
question is whether `dim(ρ̄₁+ρ̄₂)` is `2` or `1`. **Run it at `WIT11` with
(BE-67)(i)'s instrument**, exact ℚ, `assert_generic_star` **and**
`verify_pencil_witness` on every draw, and report the drawn value **and** the
generic one per (BE-69). Do this **even if job 1 returns `not genuine`** — the
measurement is cheap, it is the thing every future consumer will ask for, and a
`0` shortfall at a non-genuine witness still tells the board the mechanism is
harmless twice over.

### Job 3 (FORCED) — the classification, written down before it is needed

**If the shortfall is positive**, classify it before anything else, per the
phase note's *direction-A pivot rule*: is it (i) a **half-(B) counterexample**
(the class statement as posed is false — a *route* finding), (ii) a
**counterexample to (BE-22)(iii)'s hypothesis** at a real piece, or (iii)
something that reaches **(BE-14)** itself? These are very different board moves
and the phase note's *On a future HIT* block binds on all three. **Report the
classification and the phase-boundary consequence; act on neither.** A first
positive return is **not confirmed** — the bar is (GR-83)/(GR-113), and
`RESEARCH-ARC.md` item 4 makes the corrective mechanism the **next** pass, so
price a confirming pass rather than declaring.

### What counts as a HIT — state which you got

1. **Not genuine, by an argument** — the enemy closes and half (B)'s residue
   returns to two items ((BE-67)(iii)'s uniformity, the flag base).
2. **Genuine but `0` shortfall** — the enemy is relabelled harmless; say what
   that leaves.
3. **Genuine with a positive shortfall** — a counterexample class, classified per
   job 3. **Report the board; act on nothing.**
4. **Reduced** to a named checkable condition.
5. **The `WIT11`-against-(CH-1) check** answered either way.

### Bars

- **Do not re-open:** the answer to *can an R-node-shaped peel sit at `(1,1)`*
  (**yes**, (BE-79)) and the two vacuous zeros ((BE-80)) — **do not re-hunt**;
  (BE-32)(+) / the block-absorption lemma ((BE-74)); the peel factorization and
  the confinement ((BE-77)(i)/(ii)); (BE-41)(ii), **retired**; the branch-product
  theorem ((BE-64)); peel independence ((BE-70)); the Zariski dichotomy ((BE-69));
  `G` on (CH-1)'s class ((BE-72)); the `G²` apparatus ((BE-17)); the transversality
  count ((BE-16)(iv), (BE-27)); gauge-fixing (ZSHEAR).
- **ZJACOB (JC-6) binds harder here than on the last five directions**, because
  this one is geometric and sits on an irreducible variety: **no properness,
  smoothness or transversality from a codimension count, a Jacobian criterion, or
  Cohen–Macaulayness.** Label every dimension count **as a count** ((BE-27)).
- **Not this direction, ranked separately:** (BE-67)(iii)'s uniformity of `reach`;
  the flag base ((BE-65)(i)); the one-end-series case; **(S1)/(S2)**; cross-pair
  welding ((BE-28)(i)).
- **Out of scope:** `hK`, **(GR-15)**, **(RS-5) and the (K-res) wave (a USER
  call)**, class uniformity, W4, and **any `.lean`** (2026-08-05 hold).

### Riders

**TERMINATION E1/E2/E3** — read them against their **actual definitions**
(`notes/Pencil-fanout-archive.md`): **E2** fires only if the target is refuted
*and* the ledger has no entry left in state open-with-a-named-dispatchable-attack;
**E3** only if the target is **proven** and every remaining entry is
adjudication-gated. **E3 is ARMED (by GBAL)**; report, never fire. **F25 is this
direction's central rider** — it is the arc's **first geometric direction in
six**, and the guards that lapsed elsewhere are the ones that matter here: exact
ℚ throughout, every rng seeded with a **printed literal**, every configuration
through `assert_generic_star` **and** `kbare_common.verify_pencil_witness`, and
every claimed identity of spaces asserted **as spaces**, not as dimensions.
**F27** — a claim that a configuration **fails** a property needs multiple
independent draws, stated; an exhibited good configuration is a proof for that
witness. **F11** — *"collinear at every legal configuration"* is an
**exhaustiveness** claim and needs an argument or a real enumeration. **Cap
disclosure MANDATORY, and state the denominator every figure is over** — the last
two landings each corrected a zero read against the wrong denominator. **F12** — a
corrected summary needs a hunk at the originating prose. **F17** — the fan-out
header and `notes/Phase39.md`'s `**Status:**` header are surfaces a landing must
update. **Read `notes/scripts/README.md` *Harness debt***; BONEONE's job 3
recorded the chain as a **de-facto shared layer** at fifteen deep — **record, make
no move**, and do not re-litigate that verdict.

### Driver — expected, at the pinned path `notes/scripts/w4/bgenuine.py`

Extend `boneone.py` (for the witness family and `force`'s certificate output) and
reach the chart / `ρ̄` instruments through `bdecor.py` / `bpeel.py` by **read-only
import**. Do not re-implement the witness generator or the deficiency oracles.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BGENUINE".)
§(K-bare-ext) **extends**, no new section; labels **(BE-84)–(BE-88)**, ***Steps
BE83–BE87***, exactly the tail BONEONE declared. `BGENUINE`, `bgenuine`,
`(BE-85)`–`(BE-88)` and *`Steps BE84–BE87`* verified **0-hit**; **`(BE-84)` and
*`Step BE83`* have one hit each**, a tail POINTER, opened and confirmed.
**Return any unconsumed remainder.** **Checked and NOT chosen:** `BREACH` (the
(L5) substring rule — `breach` hits 5 files, and `reach` is a live technical term
in this arc), `BBITE` and `BSHORT` (0-hit, but naming the *second* sub-question
when the gating one is genuineness). **Prefer prose names to new parenthesized
tokens.**

### Budget — measured at this prep, and the LINE cap is what binds

**`(K-bare)` is at 1 474 / 1 600 words — 126 of headroom**, which is thin. **If
the landing does not fit, recompute the row to a TARGET, not to "under the cap"**
(F21), and **verify label preservation by scripted set-diff, never by eye**; the
natural material is *Steps BE34–BE57*'s per-direction history, which the row can
carry as current state the way BPEEL rewrote *BE14–BE33*. **`notes/Phase39.md` is
at 568/580 lines, 504/525 header words** — the prep bought room by thinning the
*Citations* pointer and **demoting the BRNODE/BDECOR entry to one paragraph**
under the note's own oldest-demotes rule, then spent most of it on the in-flight
block. **The landing should ROTATE the header's landed-direction block rather
than append to it**, which is what the last two landings did successfully. The
*"On a future HIT"* block is **not** relocatable — and this direction is the most
likely in the arc's history to need it.

### LANDING WRITE-UP — BGENUINE, 2026-09-01: **GENUINE, and it does NOT bite**

**HIT shapes 2, 5 and 4; NOT shape 1, NOT shape 3.** The target was *"(a) is
the coincidence genuine, and (b) does it bite?"*. **(a) yes**, and by an
argument rather than a draw; **(b) no**, at every one of the 392, on exhibited
exact-ℚ certificates. The spec's HIT list ranked *"not genuine, by an
argument"* first because it would close the enemy; that is **not** what
happened, and the second-ranked outcome is what landed — with the enemy
relabelled harmless rather than removed.

**Job 1, and the whole direction turns on one observation.** The aggressive
operator's disclosure — *"assumes every 3 forced points are independent, which
OVER-claims"* — is a statement about **arbitrary** triples. (BE-77)(ii)'s
certificate is not arbitrary: *Step 2* of that theorem derives `b₁, b₂` as
`v`'s unique neighbours in the two `u`-blocks, so the triple is **a vertex and
two of its own neighbours** — a **hinge pair** in the arc's existing sense. And
`binduc.assert_generic_star`, the `plane_basis`-class guard every landed
measurement in this arc runs under, asserts *exactly* `rank[p̂_v, p̂_a, p̂_b] = 3`
at every vertex and every pair of its neighbours. So the aggressive operator
and the genuine one **agree pointwise** on this family — no draw, no
genericity, no irreducibility. **The shape theorem the last two directions
proved is what makes the guard applicable**, which is why (BE-77)(ii) is now
load-bearing twice. Census: **1 836 / 1 856** admitting steps are hinge pairs,
**372 / 392** whole derivations are, and the remaining **20** steps — three
distinct neighbours of the admitted vertex — measure **rank 3** at a draw.
**(BE-84)**.

**Job 2, and the answer needed a correction to the criterion before it could
be read.** With `a_i := dim M_i − 6 − f_i` the side's own attainment loss,
(BE-22)(i)+(ii)+(BE-21) give the criterion **without** (BE-22)(iii)'s
*both-pieces-attain* hypothesis:

> **`H` attains ⟺ `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6) + a₁ + a₂`.**

At **392 / 392**: `dim(ρ̄₁+ρ̄₂) = 2 + a₁ + a₂` exactly, `ρ̄₁ ∩ ρ̄₂ = 0` **as
spaces**, `ρ_i = δ_i + a_i` (so (BE-22)(iii)(a), welded attainment, is **free**)
and `dim M(H) = 6 + def₃(H)` — **`H` attains**. Attainment is *existential*, so
each exhibited configuration is a **proof for its witness**. **(BE-86)**.

**The cap disclosure that this direction is actually about.** Measured against
`min(δ₁+δ₂,6) = 2` **alone**, the same 392 draws read `0` at 292 and **`−1` at
100** — an apparent *excess* over general position. The 100 are exactly the
rows where **one side loses attainment** at the forced configuration, and the
loss cancels the excess. **The `(K-bare)` gap-map row had quoted (BE-22)(iii)
with its proviso dropped, and this spec inherited the drop** — so the
denominator error was in the dispatch's own framing, not only in a reading of
it. Corrected in the row, annotated at *Step BE21*. This is (BE-66)(iii)'s
*"`ρ̄` exceeds general position at `π_x = π_y`, all NON-ATTAINING"* mechanism,
identified at a 2-cut and shown **benign**. **(BE-86)(iii)**.

**Job 3 is VACUOUS, and that is the report.** No positive shortfall anywhere,
so none of the three classifications fires and the phase note's *On a future
HIT* block does **not** apply. One clause half-fired and is worth the board's
attention: **(BE-22)(iii)'s hypothesis genuinely fails at 100 of the 392** —
job 3's option (ii) at a real piece — but harmlessly, because the corrected
criterion covers it. The right board entry is *"a hypothesis that was never
needed at this width"*, not *"a counterexample to a hypothesis"*.

**HIT item 5, answered `no` — and it is a real finding.** Every one of the 392
has **girth 3**; only 8 have `hcard`; **0** satisfy all three (CH-1)
hypotheses. The reason is structural on the `n₁ = 9` side (`0 / 12` of the
`K₄`-skeleton `δ = 1` sides are triangle-free, and the arithmetic says why) and
on the `n₂ = 4` side (`0 / 4`). So **(CH-1)(a) irreducibility, (BE-69)(ii)'s
dichotomy and (BE-72)(iii) are all unavailable here** — and it costs nothing,
because (BE-84) is **pointwise** and (BE-86) is **existential**. What is
genuinely lost is only the step from *"`π_u = π_v` at every **guarded**
configuration"* to *"at every configuration of `Chart(H)`"*, and that step is
never taken. **(BE-85)(iii)**.

**One row beyond the cap, minted here.** (BE-81)'s census stops at
`(n₁,n₂) ∈ {(9,4),(9,5),(10,4)}`. The next cell — **`(10,5)` at `n = 13`** — is
run: **2 400** peels, **648** forced, girth `3` at **648/648**, hinge pairs
**3 168 / 3 264**, and the same four asserts at **81/648**. Its triangle-free ×
triangle-free sub-row is the **first cell of the generator in which a
girth-`≥ 4` peel is combinatorially possible at all**, and it has **648 pairs
and 0 forced**. Stated with F11's discipline: a *none-found* claim over a
**non-vacuous** denominator, explicitly not upgraded to a theorem — whether a
triangle is *necessary* for the forcing is open (`K_{2,3}` is the obvious
triangle-free admitting shape). **(BE-85)(iv)/(BE-86)(v)**.

**A harness finding the successor should know.** `bdecor.sample_by_branches`
**cannot draw these charts.** Its flag stage places hub points under the
rank-`≤ 3` constraints only, never discovers the forced coplanarity, and
consequently pushes `u` onto the line `CD`, where the guard rejects it. The
driver's own `draw_flat` places the forced set in a plane and everything else
freely, and every draw goes through **both** standing gates — so a passing draw
is a point of `Chart(H)` whatever route found it. That the route is *complete*
is not assumed: **3 580 / 3 580** confinement controls and **1 100 / 1 100**
freedom controls establish it. **(BE-85)(i)/(ii)**.

**What did NOT move.** **(BE-79)–(BE-83) are untouched** — the witness,
`WIT16`, the size theorem, both vacuity findings and the 392 all stand exactly
as landed, and *"an R-node-shaped peel at `(1,1)` cannot be forced"* stays
**false**. **(BE-32)(+) / (BE-74)**, **(BE-73)(ii)(a)/(b)**, **(BE-77)(i)/(ii)**,
**(BE-14)**, `hbareSplit`, S-mark, (BE-64), (BE-69)/(BE-70)/(BE-72),
(BE-59)/(BE-60), the `G²` apparatus, the transversality count, (S1)/(S2) and
cross-pair welding are all untouched. BPEEL's 3 497 and 408 stand; BONEONE's
38 580, 4 330 and three census rows stand. **Not a PENCIL event**; the
phase-boundary consequence is **reported, not acted on**, and the 2026-08-05
Lean hold binds regardless.

**Deliverable.** `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE83–BE87* /
**(BE-84)–(BE-88)**; driver `notes/scripts/w4/bgenuine.py`
(`cert|chart|bite|wider|validate`, 145 s, `VALIDATE: OK`); the `(K-bare)`
gap-map row recomputed (1 475 → **1 545** words, label set-diff scripted at
every pass, **0 lost**) and its (BE-22)(iii) proviso drop **repaired at source**;
reservation **consumed in full**. Run at **`recon-opus`** (fable unavailable
this session).

## WTRI — fifty-eighth ordinal (single dispatch, prepped 2026-09-01) — **the sequence's FIRST W4-side direction**

> **LANDED 2026-09-02 — HIT shape 1: §(SAFE-RES) (T) IS A THEOREM.** Verdict in this
> file's header; mathematics in `notes/Pencil-W4-informal.md` §(SAFE-RES)
> *Steps TF1–TF6*; driver `notes/scripts/w4/wtri.py`. The spec below is kept as the
> dispatch record. Two of its framings did not survive: **job 2's two-pendant-triangle
> structure is EMPTY** (no residual carries one triangle), and **job 1's three routes are
> moot** — the answer was route 3 in a form *Step 4* had not listed, a landed feasibility
> **transfer** rather than a new necessary condition.

**Selection provenance: a DELIBERATE DEVIATION from the ranked list, and the
reason is the standing criteria rather than a new finding.** BGENUINE handed half
(B) back a two-item residue and `notes/Phase39.md`'s ranked list promoted the
flag base to candidate 1. The coordinator did not take it. **Nine consecutive
directions (49–57) have run on the (BE-14) thread**, and in the same period
carried item **#2** — `hcontract`, one of exactly **three** things between the
landed successor `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` and
`PencilPair K 3 G` — has had **zero directions in the whole 65-direction
sequence**, while this note's own *Blockers* has said since **2026-08-02** that
three of its four costs are *"slice-sized and need no adjudication"*. All three
standing criteria point the same way:

- **Max impact on proving or disproving `PencilPair K 3 G`.** Route 3 was
  **adjudicated** on 2026-08-02 and cannot close without (T), (V), (E-loc) and
  (K-res). (T) is one of the three that need no user call.
- **Falsification / architecture-testing as a positive criterion.** (T) is
  **landed-invisible**: the search's own feasibility certificate for `G` is L6b,
  which *requires* triangle-freeness, so a triangle-carrying residual **can never
  appear in a certified sweep**. Attacking it is architecture-testing in the
  literal sense — it is a blind spot of the instrument, not a gap in the data.
- **Diversification.** First W4-side direction of the arc; different carried
  item, different workbook, different label family, and a question with no
  geometry in it.

**The (BE-14) ranked list is NOT dropped** — the flag base stays candidate 1 for
the next pick on that thread. Dispatched **un-named, single**, at **`recon-opus`**
(fable unavailable this session).

### The target, stated exactly

`notes/Pencil-W4-informal.md` §(SAFE-RES) *Step 3* states the successor
(SAFE-RES′) and decomposes it into (E), (T), (V). This direction is **(T)**:

> **(T)** *A residual `G` is **triangle-free**.*
>
> Prove it, **or** discharge route 3's need for it by one of the three routes
> *Step 4* already names, **or** exhibit a triangle-carrying feasible residual.

**Route 3, packaging (b) is ADJUDICATED (2026-08-02) and is not reopened by this
direction.** (T) is a cost *inside* it, not a choice about it.

### THE THING THAT MAKES THIS DIRECTION DIFFERENT — read it before planning a driver

**Numerics cannot settle (T), and the 255/255 already recorded is NOT evidence.**
*Step 3* says so in its own words, and *Step 4* explains why: the sweep's
feasibility certificate is L6b, **which requires triangle-freeness**, so a
triangle-carrying residual is invisible to a certified search *by construction*.
A driver that sweeps harder reproduces the blind spot at greater cost. **This is a
derivation-first direction** — and the reservation therefore makes `w4/wtri.py`
**conditional**: ship one only if it tests something the blind spot does not
cover (a *necessary*-condition candidate, say), and if you ship none, say so and
why. That is a legitimate landing shape here and is **not** a gap in the work.

### What *Step 4* already proves — cite it, do NOT re-derive it

Let `Δ = {x,y,z}` be a triangle of a feasible `G` with `|V(G)| > 3`. By **(R5)**
`x,y` have degree 2 and `z` is a hub, so `Δ` is a **pendant** triangle and a
proper rigid subgraph. Its contraction is simple and equals `G − x − y` with
`z ↦ v*`, `deg v* = deg z − 2`; the only degree that changes is `z`'s and it only
**drops**, so no vertex gains hub status. Hence **`hcard(G/Δ)` always holds**, and
`¬Feasible(G/Δ)` can only be witnessed, landed-wise, by a **second** triangle in
`G − x − y`. Consequences already landed: **(i)** `G` must carry `≥ 2` triangles,
and two pendant triangles pass every landed test, so **(T) is not provable from
the landed set**; **(ii)** such a `G` is middle-zone, hence invisible to a
certified search. The **bowtie** (`|V| = 5`) does die — either triangle contracts
to the spanning `C₃`, landed-feasible by L7c-3.

### Job 1 (PRIMARY, FORCED) — settle (T), by one of the three named routes

*Step 4* names them and this direction should pick among them with reasons, not
invent a fourth without saying so:

1. **Carry (T) as a hypothesis** — price what that costs route 3 downstream, and
   say precisely which consumer then owes it.
2. **Add triangle-freeness to branch 4's dispatch condition**, routing the
   triangle case elsewhere — say *where* it routes and whether that arm can
   absorb it. Note **`hnoGood'` is known NON-vacuous** (2026-08-02), so branch 4
   needs content regardless.
3. **Land a new feasibility-*necessary* condition that kills pendant triangles.**
   This is the only route that discharges (T) outright; the others relocate it.

**A relocation is a legitimate result and must be labelled as one** — the
playbook's *"an abstraction that defers the crux as a hypothesis is not progress
on the crux"* applies with full force, so if (T) ends up carried, say **where**
the obligation now sits and **who** discharges it.

### Job 2 (FORCED) — the two-triangle structure, since that is where the answer lives

*Step 4* reduces (T)'s failure to `G` carrying **≥ 2** pendant triangles. **That is
a strong structural handle and nobody has pulled it.** Two pendant triangles at
hubs `z₁, z₂` (possibly `z₁ = z₂`, the bowtie) inside a residual — what does the
residual's own definition force about them? The bowtie dies at `|V| = 5`; **does
it die in general, and if not, what is the smallest survivor?** An explicit
survivor is the cleanest possible answer to job 1 (it refutes (T) and forces route
2 or 1); an argument that none exists **proves (T)**.

### Job 3 (FORCED, CHEAP) — say what (V) then costs

*Step 3* makes **(V)** *"elementary given (E) and (T)"* and lists three residues,
of which *"`j = 2` with `u = u'` (a pendant triangle)"* is **killed by (T)**. So
(T)'s disposition changes (V)'s. In one paragraph: if (T) is carried rather than
proved, is (V) still elementary, and which of its three residues re-opens? This is
the consumer trace one level down and it is cheap to run while the structure is in
front of you.

### What counts as a HIT — state which you got

1. **(T) PROVED** — route 3 loses a cost outright.
2. **(T) REFUTED by an exhibited residual carrying two pendant triangles** — route
   3 must take route 2 or carry it; a **clean** and useful result.
3. **Route 2 or 3 of *Step 4* priced and recommended**, with the relocated
   obligation named.
4. **(V)'s cost under a carried (T)** (job 3), either way.
5. **The two-triangle structure characterized** (job 2), even short of a verdict.

### Bars

- **Do not re-open:** the route-3/packaging-(b) adjudication (2026-08-02); the
  `hnoGood'` vacuity refutation (`|V| = 19`); **(SAFE-RES) itself, REFUTED** at
  `S29`; the `W19` counterexample; (E)'s reduction to **(E-loc)**; and the whole
  **(BE-14) thread** — this direction does not touch half (B), the 2-cut lemma,
  or anything in §(K-bare-ext).
- **The Lean hold (2026-08-05) binds**: no `.lean`. The **W4 build** (W4-L4b
  onward) is **parked** and is not this direction's business; (T) is informal
  mathematics, which is precisely why it is dispatchable today.
- **Not this direction, ranked separately:** (E-loc); (V) beyond job 3's
  paragraph; **(K-res)**, which is a **USER call** and stays one; the flag base;
  (BE-67)(iii)'s uniformity; the one-end-series case; (S1)/(S2).
- **Out of scope:** `hK`, **(GR-15)**, class uniformity.

### Riders

**TERMINATION E1/E2/E3** — read against their actual definitions
(`notes/Pencil-fanout-archive.md`); **E3 is ARMED (by GBAL)**, report, never fire.
Note that E1/E2/E3 are phrased for the **(K)** arc, so state explicitly how you
read them on the W4 side rather than asserting a verdict by analogy. **F11** —
*"no residual carries two pendant triangles"* is an **impossibility** claim and
needs an argument; a search that finds none reports *"none found under cap C"*,
**and here it must also disclose the L6b blind spot**, which is stronger than a
cap. **Cap disclosure MANDATORY with the DENOMINATOR named** — three consecutive
landings have now turned on a denominator (BSPREAD's, BONEONE's, BGENUINE's), and
this direction's recorded 255/255 is the arc's clearest example of a figure whose
denominator is the wrong one. **F12** — a corrected summary needs a hunk at the
originating prose. **F17** — the fan-out header and `notes/Phase39.md`'s
`**Status:**` header are surfaces a landing must update; **`notes/Phase39.md`
*Blockers*' W4 bullet is a third**, and it is the one a fresh session reads for
this item. **Read `notes/scripts/README.md` *Harness debt*** only if you ship a
driver.

### Where the write-up goes — and the two things that differ on this side

- **Mathematics → `notes/Pencil-W4-informal.md` §(SAFE-RES)**, extending it with
  *Steps TF1–TF6* / **(TF-1)–(TF-6)**. **Do NOT extend the `(BE-…)` family** — it
  belongs to §(K-bare-ext) in the other workbook.
- **There is NO gap-map row for the W4 side and this direction does not open
  one.** The *State of (K)* map is the (K) arc's status object by its own header;
  W4's status lives in the W4 workbook's confidence verdicts and
  `notes/Phase39.md` *Blockers*. So `notes/check-gapmap-cells.py` will not fire —
  **state that in the commit message rather than skipping the gate silently**.
  `notes/check-phase-note.py` **does** fire.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction WTRI".) Labels
**(TF-1)–(TF-6)**, ***Steps TF1–TF6***, owning file `notes/Pencil-W4-informal.md`
§(SAFE-RES). All **0-hit**. **Return any unconsumed remainder.** **Checked and NOT
chosen:** extending the `SR-` family — the bare `(T)` is *already* in this file's
collision table (§(K-pitch)'s transfer claims vs W4's triangle-freeness), so
minting `(T1)`, `(T2)` beside it would deepen a recorded collision, which (L4)
forbids. **Qualify every citation of the bare `(T)` with its owner** per (L3).

### Budget — measured at this prep

**`notes/Phase39.md` is at 565/580 lines, 480/525 header words** — **lines bind**.
The prep bought 15 by **merging the (BE-14) thread's five per-landing *Hand-off*
blocks into one paragraph** and compressing the *Doc debt* bullet, which is the
same relocation-not-fold move that produced block 8. **The landing should MERGE or
ROTATE, not append.** The **`(K-bare)` gap-map row is at 1 544 / 1 600 words** —
**this direction does not touch it**, but the next (BE-14) landing will need a
recompute **to a target** (F21), with label preservation verified by scripted
set-diff; the natural material is *Steps BE34–BE57*'s per-direction history.

## WELOC — fifty-ninth ordinal (single dispatch, prepped 2026-09-02) — the second W4-side direction

**Selection provenance: the F26 consumer trace was re-run for a SIXTH direction
running, and it OVERTURNED the successor WTRI named.** WTRI's return ranked **(V)**
next, calling it *"the cheapest non-user-call item in the phase"*. The coordinator
opened both remaining costs in `notes/Pencil-W4-informal.md` and did not take it:

- **(V) is DOWNSTREAM of (E).** §(SAFE-RES) *Step 3* words it exactly — *"(V) the
  local choice — **elementary given (E) and (T)**"* — and the proof it sketches
  begins *"(E) supplies a branch `β` with `j ≥ 2` interior vertices"*. (T) is now a
  theorem; **(E) is not**, and (E) is what (E-loc) discharges. Proving (V) first
  means proving it modulo an open hypothesis.
- **(E-loc) has TWO consumers**, not one: *Step 3* says discharging it *"fixes gap
  **(E)** of §(SAFE-RES) *Step 3*, and with it the `hfresh` discharge of Step 0"*.
- **(E-loc) already has its obstruction narrowed to two named shapes** — see below.
  That is further along than (V)'s open half, which is still *"a full proof of (V)
  must show that not every `≥ 2`-interior branch of a residual is of those two
  shapes"*.

*Cheapest* is not the standing criterion; **max impact on proving or disproving
`PencilPair K 3 G`** is, and on that axis (E-loc) is upstream, has two consumers,
and is better prepared. **(V) is not dropped** — it is candidate 2 and gets cheaper
the moment (E) lands. Dispatched **un-named, single**, at **`recon-opus`** (fable
unavailable this session).

### The target, stated exactly

> **(E-loc)** *Every residual `G` has a degree-`2` vertex `v₀` with `E(G − v₀)`
> independent in the `(6,6)` count matroid.*

Prove it, **or** exhibit a residual with no such vertex, **or** reduce it to a
named checkable condition. **Numerics: 255/255** (`widened.py --ebound`).

### What is free — cite it, do NOT re-derive it

- **The reduction of (E) to (E-loc)** (§widened kernels *Step 3*), including the
  line-by-line reading of `edgeBound_of_noRigid_of_degree_two`
  (`ReducibleVertex.lean:1270`): it consumes `hnp` at **exactly one point**, to
  prove `hindep` for the `5`-fold fiber of the edges avoiding `v`; everything after
  is pure counting, giving `5(|E| − 2) + 6 ≤ 6(|V| − 1)`, i.e. `f(V(G)) ≤ 4`. And
  the key asymmetry already recorded: **the conclusion is about `G`, not about
  `v`**, so (E) follows as soon as *some* degree-`2` vertex satisfies it — **it need
  not be the vertex the split uses**.
- **The witness is typically NOT split-usable** — at `W19` it is `c1`/`c3`, at
  `S29` it is `m1`/`m2`, the **core's own** degree-`2` vertices, disjoint from the
  split-usable set in both. 210 of 255 do have a split-usable witness (which also
  buys `s₀ = 0`); `W19`/`S29` are among the 45 that do not. **Do not conflate the
  two roles.**
- **(T) is now a theorem** ((TF-5)) — every residual is triangle-free, and that is
  a hypothesis you may use freely.
- **(R1)/(R5)** and the residual anatomy of §(SAFE-RES) *Step 4* / *Steps TF2–TF5*.

### THE STRUCTURE THAT IS ALREADY DONE — start here, do not rediscover it

§widened kernels *Step 3* records this and it is the direction's natural spine:

> `f` is **supermodular** (`|E(·)|` is supermodular, `−6(|W| − 1)` is modular), so
> `f(W₁ ∪ W₂) ≥ f(W₁) + f(W₂) − f(W₁ ∩ W₂)`. When `W₁ ∩ W₂` is a single vertex
> `f(W₁ ∩ W₂) = 0`; when it is count-independent `f(W₁ ∩ W₂) ≤ 0`. Either way two
> count-dependent sets meeting like that **merge** into a count-dependent union.

**Hence the obstruction to (E-loc) is one of exactly two shapes**, and *Step 3*
names them:

1. **two count-dependent vertex sets meeting in an independent set** — in
   particular two **disjoint** proper rigid subgraphs with `f > 0`;
2. **a single dependent "brick"** all of whose vertices have `G`-degree `≥ 3`.

**Neither occurs anywhere in the pool.** So the direction's job is not to hunt
blind — it is to decide these two shapes against the residual definition.

### Job 1 (PRIMARY, FORCED) — kill the two shapes, or exhibit one

**Shape 2 looks like the one the residual definition should forbid outright** and
is the coordinator's guess at the cheaper half — a residual is 2EC with a
degree-`2` vertex somewhere by (R1)/(R5)-adjacent structure, and a brick all of
whose vertices have degree `≥ 3` has to coexist with that. **Say whether that is
actually an argument or whether the brick can sit disjoint from the degree-`2`
vertices** — the second reading is the whole question and the coordinator does not
know which holds.

**Shape 1 is where two disjoint proper rigid subgraphs would live**, and the
residual definition constrains proper rigid subgraphs directly (that is what WTRI
just exploited on the triangle). **Ask what the residual's own `∃`-rigid clause and
its contraction requirement say when there are two disjoint ones** — and note this
is exactly the *"two pendant triangles"* shape one level up, which WTRI dissolved
by finding a landed transfer rather than by a hunt.

### Job 2 (FORCED) — the landed-inventory question, asked ONCE and in general

WTRI's whole result came from *Step 4* having enumerated the feasibility
**criteria** and omitted the feasibility **transfers**. That was not a one-off: it
is now a logged check (`notes/dispatch-log.md`, 2026-09-02). **Run it here before
concluding anything is unprovable:** *Step 3* says (E) is *"landed only under
`hnoRigid`"* and proposes a *"`noRigid`-free sibling ... verbatim-prefix
extraction"*. **Grep the tree for what is actually landed around the count matroid
and reducible vertices** — `ReducibleVertex.lean` and its neighbours — and report
whether a second declaration already gives what (E-loc) needs, the way
`pencilNondegFeasible_induce_of_pendant_deg3` did for (T). **This is cheap and it
is the highest-expected-value hour in the direction.**

### Job 3 (FORCED, CHEAP) — what (V) costs once (E) lands

If job 1 proves (E-loc), then (E) follows and **(V) becomes "elementary given (E)
and (T)"** with both hypotheses discharged. In one paragraph: does (V) then close
outright, or do its two `C₄`-carrying residues (`j = 3` with `u = u'`; `j = 2` with
`u ~ u'`) still need the argument *Step 3* says they need? This is the consumer
trace one level down and it decides the next pick.

### What counts as a HIT — state which you got

1. **(E-loc) PROVED** — (E) falls, `hfresh`'s Step-0 discharge falls with it, and
   W4's cost list drops to **(V)** and **(K-res)**.
2. **A residual with no count-independent degree-`2` deletion** — refutes (E-loc)
   and re-opens (E); a clean result that re-routes route 3.
3. **One of the two shapes decided**, even short of the full statement.
4. **A landed declaration found** (job 2) that shortcuts the whole thing.
5. **(V)'s post-(E) cost** (job 3), either way.

### Bars

- **Do not re-open:** **(T)**, now a theorem ((TF-5)) — use it, do not re-prove or
  re-hunt it; the route-3/packaging-(b) adjudication (2026-08-02); `hnoGood'`'s
  vacuity refutation (`|V| = 19`); **(SAFE-RES)** itself, refuted at `S29`; the
  `W19` counterexample; and the whole **(BE-14) thread** — this direction does not
  touch half (B), the 2-cut lemma or §(K-bare-ext).
- **The Lean hold (2026-08-05) binds**: no `.lean`. The *"cheap Lean leaf"* §widened
  kernels *Step 3* names (the `noRigid`-free sibling) is **parked** — you may say it
  is cheap and pin its statement, you may not build it.
- **Not this direction, ranked separately:** **(V)** beyond job 3's paragraph;
  **(K-res)**, a **USER call**; everything on the (BE-14) side.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity.

### Riders

**TERMINATION E1/E2/E3** — read against their actual definitions
(`notes/Pencil-fanout-archive.md`) and state how you read them on the W4 side, as
WTRI did rather than asserting by analogy. **E3 is ARMED**; WTRI was the first
landing whose *first* conjunct held, and its second failed because (E-loc)/(V) are
dispatchable. **If this direction proves (E-loc), check E3 again** — the second
conjunct moves closer, and it is a **report**, never a firing.
**F11** — *"no residual has shape 1 / shape 2"* is an **impossibility** claim and
needs an argument; a sweep that finds none reports *"none found under cap C"*.
**Cap disclosure MANDATORY with the DENOMINATOR named.** **And the disclosure that
differs from WTRI's, which you must get right:** (T)'s 255/255 was worthless
because L6b *requires* triangle-freeness, so the sweep could not see the failure
mode. **(E-loc) is not in that blind spot** — count-independence is not part of any
feasibility certificate — so the 255/255 is ordinary evidence. **But the POOL is
still generated**, so state what the pool's own construction can and cannot reach,
and do **not** reuse WTRI's blind-spot sentence here. **F12** — a corrected summary
needs a hunk at the originating prose. **F17** — the fan-out header,
`notes/Phase39.md`'s `**Status:**` header **and its *Blockers* W4 bullet**, and
**`ROADMAP.md`'s Status row** are all surfaces a landing must update; the ROADMAP
row was missed at WTRI's landing and the coordinator repaired it at `571de184`.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction WELOC".) Labels
**(EL-1)–(EL-6)**, ***Steps EL1–EL6***, owning file `notes/Pencil-W4-informal.md`
§widened kernels (routes 1/3). All **0-hit**. **Return any unconsumed remainder.**
**Checked and NOT chosen:** `WCOUNT` (names the instrument, not the question);
extending `WK-`, since `(E-loc)` and `(K-res)` already sit there as bare tokens.
**Qualify every citation of the bare `(E)` with its owner** (L3).

### Budget — measured at this prep

**`notes/Phase39.md` is at 569/580 lines, 509/525 header words** — **lines bind**,
with 11 spare. The prep rotated the header's landed block and **merged the BWIN
paragraph into a settled-frame paragraph** under the note's oldest-demotes rule.
**The landing should MERGE or ROTATE, not append.** The `(K-bare)` gap-map row is
at **1 544 / 1 600** and **this direction does not touch it** — it is the (BE-14)
thread's, and the next landing on *that* thread needs a recompute to a target
(F21), not this one.

### LANDING WRITE-UP — WELOC, 2026-09-02: **(E-loc) is REFUTED, and the other shape is IMPOSSIBLE**

**HIT shapes 2 and 3, then 4 and 5; NOT shape 1.** The spec ranked *"(E-loc)
PROVED"* first and *"a residual with no count-independent degree-`2` deletion"*
second. The second is what landed — **`T32`**, `|V| = 32`, two **disjoint**
count-dependent `C₄` cores — and shape 3 landed with it, because the *other*
obstruction is now a **theorem in the negative**. Both shapes are therefore
decided, which is more than either HIT alone: **(E-loc) fails, and shape 1 is the
only way it can.**

**The coordinator's guess was right, and it was the cheap half.** Shape 2 — *"a
dependent brick all of whose vertices have `G`-degree `≥ 3`"* — is **impossible in
a residual** ((EL-4)), and the spec's own worry (*"can the brick sit disjoint from
the degree-`2` vertices?"*) is answered *yes it can, and that is exactly why it
cannot exist*: sitting away from the degree-`2` vertices is what makes it
**shielded**, and shieldedness is what closes L6b's `¬hcard` escape. Two landed
items do the work, and *Step EL1* is the **job-2** find that supplies them:
`isKDof_zero_of_cycle`/`cycle_isProperRigidSubgraph` (**every** cycle of length
`≤ 6` is rigid, not just the `C₄` this arc had been citing), and the `hcard`
necessary condition read as a **transfer** — composed with the
`PencilNondegFeasible` existential it says *every hub of a residual has `≤ 2` hub
neighbours* ((EL-1)), which the arc had only ever used as a certified-infeasibility
test on a contraction. **WTRI's inventory lesson repeated at one remove: the item
was landed AND inventoried — in one of its two roles.**

**The brick argument, in one line.** A brick is a hub `C₄` or `C₅` ((EL-3), from
(EL-1) + (T)); all its outside neighbours are then degree-`2`, so its contraction
satisfies `hcard`, so L6b would certify it feasible unless the contraction is
non-simple or carries a triangle — and each of those extends the set by an ear of
`j = 1` or `j = 2` **preserving the same property**, until the chain hits a co-1
rigid subgraph or a spanning-`C₃` contraction, both forbidden. It is *Step 2*'s
own (C1)+(C5) with **maximality replaced by shieldedness**, which is what those two
arguments actually consume — so no new mathematics, and **(T) is spent twice** (no hub
`C₃`; no triangle off `v*`), hours after WTRI proved it.

**`T32` is certified to the `W19`/`S29` standard, with no middle zone.** Simple,
2EC, girth 4 and `hcard` ⟹ feasible by the landed-**sufficient** L6b; exactly two
proper rigid vertex sets, the two `C₄` cores, on **three** independent oracles
(pebble game / tree packing / partition enumeration); no co-1 (`4 ≤ |V| − 2`); and
both contractions **simple** with `closedHubNbhd(v*)` of size **4**, infeasible by
the landed-**necessary** `hcard`. (E-loc) then fails for the simplest available
reason: `f = 2` at each core and the cores are disjoint, so every one of the 22
degree-`2` vertices misses a whole dependent core. **It is a family, not a point** —
the `(m, a, b)` scan certifies **24** refuting residuals, `T32` the smallest, `C₅` cores
included, and a `C₄` core and a `C₅` core sit in one residual at `|V| = 33`.

**What is NOT refuted, and the new extremal fact.** **(E) stands.** `f(V(T32)) = 4`
— *exactly* the bound (E) asserts, attained — so the witness satisfies (E), and
**(E) is now known TIGHT**: the pool's maximum was `2`, so *"`f ≤ 3`"* could not
previously be ruled out and now is. `T32` also satisfies (SAFE-RES′) (8 deep split
vertices, 16 split-usable) and is triangle-free, as (T) requires. **Only the route
dies.**

**And it dies by more than a hair.** Generalizing the landed argument gives
`f(V(G)) ≤ 4 + κ(v)` for every degree-`2` `v`, with `κ(v)` the corank of the
`v`-avoiding fiber — `edgeBound_of_noRigid_of_degree_two` is the `κ = 0` case. At
`T32` `min_v κ(v) = 2`, so the sharpest conclusion the counting argument can reach
is `f ≤ 6` against a true `f = 4`. **The argument's only free parameter is which
vertex you delete, and no choice works.**

**The successor, and it is cheaper than what it replaces.** *Step 0* records that
(E) reaches the split arm only through
`exists_adjacent_degree_two_pair_of_edgeBound`, whose conclusion is *two adjacent
degree-`2` vertices*. So the honest obligation is **(E-pair)**, weaker than (E),
true at 255/255 and at `T32`, and a statement about **branch lengths** — where the
Ear Lemma and the no-good-contraction clause are already the working tools, as
(EL-4) demonstrates. **(V) needs (E) only through the same neighbourhood** (a
branch with `j ≥ 2` interior vertices), so the two remaining non-user-call W4
items now share one upstream target. **Job 3's premise is void** — (E) did not
land — but its substance is answered: (V) is unchanged, its two `C₄`-carrying
residues untouched, and it holds outright at `T32` by the `j ≥ 4` branch.

**A second consumer that was never one.** *Step 0*'s *"the `hfresh` discharge
collapses into (E) exactly like (S1)/(S2)"* is true of the landed **proof** and
not of the **obligation**: the edge bound is used there only to contradict
`E(G′) = univ`, and a residual is `Simple`, so `|E| ≤ |α|(|α|−1)/2` discharges it
at the price of a larger `β` headroom in the consumer-facing headline. **(E) has
ONE real consumer**, and the sentence is annotated at source (F12), as are three
over-statements in *Step 3*'s own (E-loc) paragraph — merging does not remove
shape 1, the brick is not merely *"all degree `≥ 3`"*, and *"neither occurs in the
pool"* is empty.

**The denominator disclosure, and it is a `0` — not a cap, and NOT (T)'s blind
spot.** Of the pool's 255 residual inhabitants (all 255 certified STRONG), **160
carry no count-dependent set at all** and **95 carry exactly one**; **zero** carry
two. So the pool holds **no instance of the only configuration that can decide
(E-loc)**, and the recorded 255/255 was never evidence about it — the honest
denominator is `0`. The cause is structural but *not* an invisibility: unlike (T),
where L6b's own triangle-freeness hypothesis made a counterexample impossible for
any sweep to certify, count-independence appears in **no** feasibility certificate,
so a sweep *could* have seen this failure. `family_g` and `family_core_ring` simply
build **exactly one** core cycle each, and the random sweeps produce no residual at
all. The pool's maximum `f = 2` against `T32`'s `4` is the same gap from the
arithmetic side.

**TERMINATION E1/E2/E3, read against their (K)-arc definitions
(`notes/Pencil-fanout-archive.md`), not by analogy.** **E1** (a g-flank) is a
§(K-grid) object with no W4 instance; its nearest W4 reading — *an exhibited object
refuting the direction's target class* — is **satisfied in the narrow sense**
(`T32` refutes (E-loc)), but (E-loc) is a **gap on a route**, not the arc's target
class, and refuting it removes a route while leaving `PencilPair K 3 G` exactly
where it was. **E1 does not fire.** **E2** needs the target refuted or
unprovable-as-posed *with no successor as specified*; the target **is** refuted,
and the successor **is** specified ((E-pair), (EL-6)), which is the clause E2 turns
on. **E2 does not fire — and this is the closest any W4 landing has come to it,
worth recording.** **E3 is ARMED (by GBAL)**: its first conjunct needs the target
*proven*, and it was refuted, so E3 does not fire on the first conjunct this time
(WTRI's landing satisfied it); its second conjunct still fails, since (V) and
(E-pair) are dispatchable and need no adjudication. **E3 DOES NOT FIRE —
reported, not acted on.**

**What did NOT move.** (T) ((TF-1)–(TF-6)) is untouched and is *used* three times.
(SAFE-RES) stays refuted, (SAFE-RES′) open, `W19`/`S29` intact; the `hnoGood'`
vacuity refutation stands and gains a third inhabitant. **(K-res), *Step 4*'s
minimal widened statements, *Step 5*'s numerics and the route-3/packaging-(b)
adjudication are untouched** — (E-loc) was never an input to any of them — and
**(K-res) stays a USER call**. Nothing on the (BE-14) side, `hK`, (GR-15) or class
uniformity is touched. **A PENCIL event on the W4 side; the phase-boundary
consequence is reported, not acted on, and the 2026-08-05 Lean hold binds
regardless.**

**Deliverable.** `notes/Pencil-W4-informal.md` §widened kernels (routes 1/3)
*Steps EL1–EL6* / **(EL-1)–(EL-5)**, plus F12 hunks at *Step 0*, *Step 1*'s K1
row, *Step 3*, both section headers and §(SAFE-RES) *Step 3*'s (E) bullet; driver
`notes/scripts/w4/weloc.py` (`validate|witness|brick|pool|hunt`, 114 s); reservation
consumed **five of six** — **(EL-6) is returned unconsumed**, the sixth step
carrying no new labelled claim. `notes/check-gapmap-cells.py` **did not fire and
was not skipped**: there is no gap-map row on the W4 side and this direction did
not open one. Run at **`recon-opus`** (fable unavailable this session).

## WPAIR — sixtieth ordinal (single dispatch, prepped 2026-09-02) — the third W4-side direction

**Selection provenance: WELOC's own recommendation, TAKEN — but the consumer trace
was re-run for a seventh direction running and it is the trace, not the
recommendation, that authorizes the pick.** WELOC refuted (E-loc) with `T32` and
named **(E-pair)** as (E)'s successor target, *"the pick the direction
recommends"*. The coordinator opened the consumer rather than inheriting the
sentence, and it holds — **verified off the landed body, not the note**:

> `exists_adjacent_degree_two_pair_of_edgeBound` (`ReducibleVertex.lean:1068`)
> concludes exactly
> `∃ v a, v ∈ V(G) ∧ a ∈ V(G) ∧ G.degree v = 2 ∧ G.degree a = 2 ∧ ∃ e, G.IsLink e v a`
> from `6 ≤ bodyBarDim n`, `3 ≤ |V(G)|`, `G.TwoEdgeConnected` and the edge-count
> hypothesis `hedge`.

So **(E) reaches the split arm only through `hedge`**, and the arm consumes only
the *conclusion*. Proving **(E-pair)** directly bypasses (E) entirely. That is the
same shape of find as WTRI's — read the consumer's actual conclusion and the
obligation turns out weaker than the thing being proved — and it is why this pick
dominates a second assault on (E).

**It serves BOTH remaining non-user-call costs.** WELOC records that *"(V)'s
dependence on (E) is only through (E-pair)'s branch-length statement"*, so W4's two
slice-sized items now share one target. **(K-res) remains a USER call** and is out
of scope.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this
session).

### The target, stated exactly

> **(E-pair)** *Every residual `G` carries two adjacent degree-`2` vertices.*

Prove it, **or** exhibit a residual with no adjacent degree-`2` pair, **or** reduce
it to a named checkable condition. It holds at **255/255** of the pool and at
**`T32`**.

### What is free — cite it, do NOT re-derive it

- **The consumer trace above**, and *Step EL6*'s reduction of (E) to (E-pair).
- **(T) is a THEOREM** ((TF-5)): every residual is triangle-free. Use it freely.
- **(EL-4)**: **no residual carries a brick** (a hub `C₄`/`C₅` sitting away from the
  degree-`2` vertices) — proved by the **shieldedness** argument, which is *Step 2*'s
  (C1)+(C5) with maximality replaced by shieldedness. **This is the arc's worked
  example of exactly the tool pair this direction needs** (Ear Lemma +
  no-good-contraction), and *Step EL4* says so.
- **(EL-1)**: in a feasible `G` every hub has **≤ 2 hub neighbours** — from
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`)
  composed with the existential in `PencilNondegFeasible`. **Coordinator-verified
  off both bodies.** WELOC's job-2 find was that the arc had only ever used that
  lemma as a *certified-infeasibility test on a contraction*; as a structure theorem
  about the residual itself it is new, and it is likely the most useful free fact
  here.
- **(EL-3)/(EL-2)**: a brick is a hub `C₄`/`C₅`; the count identity
  `f = 5c − |W| + 1` and the anatomy of a minimal dependent set.
- **`isKDof_zero_of_cycle`** (`Deficiency.lean:743`) / **`cycle_isProperRigidSubgraph`**
  (`Operations.lean:1082`): **every** cycle of length `≤ 6` is rigid, not just the
  `C₄` this arc habitually cites — WELOC's second job-2 find.
- **`T32`** itself (`weloc.py --witness`), a certified residual with `f = 4`, two
  disjoint `C₄` cores, 22 degree-`2` vertices — a free test instance, and
  **(E-pair) holds there**.

### Job 1 (PRIMARY, FORCED) — (E-pair)

The statement is about **branch lengths**: a residual's degree-`2` vertices are the
interiors of its branches, and two *adjacent* ones means some branch has `≥ 2`
interior vertices. So (E-pair) says: **no residual has every branch of interior
length `≤ 1`**. Attack it with the tools *Step EL4* already used — the **Ear
Lemma** (an ear through the relevant set needs `≥ 6` interior vertices) and the
**no-good-contraction** clause — and with **(EL-1)**, which caps hub adjacency at
2 and therefore constrains how short every branch can simultaneously be.

**The counting shape to check first, and the coordinator does NOT know the answer:**
if every branch has `≤ 1` interior vertex then `|V|` and `|E|` are both controlled
by the hub set, so `f(V(G))` is a function of the hub subgraph alone. **Does the
residual's own feasibility (L6b: `hcard` + triangle-free) plus (EL-1) make that
impossible?** That is a finite question about hub subgraphs of bounded adjacency,
which is the kind of thing the last three W4 landings have each settled.

### Job 2 (FORCED) — the landed-inventory question, third time and now standing

WTRI closed (T) by finding two landed **transfers** an inventory had omitted;
WELOC's job 2 found **two more** landed facts the arc had under-used ((EL-1)'s
composition, and cycles up to `6` being rigid). **Run it again before concluding
anything is unprovable**, and this time report it as a *standing* result: after
three directions, is there a systematic gap between what the arc cites and what
`ReducibleVertex.lean` / `Deficiency.lean` / `Operations.lean` / `Motive.lean`
actually prove? A one-paragraph answer is enough, but it is worth having — this
check has now paid three times running.

### Job 3 (FORCED, CHEAP) — close the (V) trace

If (E-pair) lands, **(V)** is *"elementary given (E) and (T)"* with (T) a theorem
and (E)'s only consumed consequence supplied. In one paragraph: does (V) close
outright, or do its two `C₄`-carrying residues (`j = 3` with `u = u'`; `j = 2` with
`u ~ u'`) still need their own argument? **WELOC already reports (V) holds outright
at `T32`** — so say whether that is a witness or a theorem.

### What counts as a HIT — state which you got

1. **(E-pair) PROVED** — the split arm's obligation is discharged, and W4's
   non-user-call cost list collapses toward **(V)** alone.
2. **A residual with no adjacent degree-`2` pair** — refutes (E-pair) and re-opens
   the arm; a clean result that re-routes route 3.
3. **Reduced** to a named checkable condition (e.g. a finite hub-subgraph check).
4. **The standing inventory verdict** (job 2).
5. **(V)'s status** (job 3) — witness or theorem.

### Bars

- **Do not re-open:** **(T)** ((TF-5)); **(EL-4)**, no residual carries a brick;
  **(E-loc)**, REFUTED by `T32` ((EL-5)) — **do not attempt to rescue it**, and do
  not re-hunt for a second refuting witness; **(E)** itself, which is open, tight
  (`f = 4` at `T32`) and **explicitly not this direction's target** — the point of
  (E-pair) is to avoid it; the route-3/packaging-(b) adjudication (2026-08-02);
  `hnoGood'`'s vacuity refutation; **(SAFE-RES)**, refuted at `S29`; and the whole
  **(BE-14) thread**.
- **The Lean hold (2026-08-05) binds**: no `.lean`. The *"cheap Lean leaf"*
  (`noRigid`-free sibling) stays **parked** — pin a statement, do not build it.
- **Not this direction, ranked separately:** **(V)** beyond job 3; **(K-res)**, a
  **USER call**; everything on the (BE-14) side.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity.

### Riders

**TERMINATION E1/E2/E3** — read against their actual definitions
(`notes/Pencil-fanout-archive.md`) and state how you read them on the W4 side.
**E2 came closest of any W4 landing at WELOC** (target refuted, but the successor
*was* specified — the clause it turns on), so if this direction refutes (E-pair),
**say explicitly whether a successor is specified**, because that is the E2 clause.
**E3 is ARMED**; report, never fire. **F11** — *"no residual has all branches of
interior length ≤ 1"* is an **impossibility** claim and needs an argument; a sweep
reports *"none found under cap C"*. **Cap disclosure MANDATORY with the DENOMINATOR
named** — and note WELOC's own precedent: it reported the honest denominator as
**0, not 255** (zero pool residuals carry two dependent sets), which is the standard
to match. **This question is NOT in (T)'s blind spot** either — branch length is in
no feasibility certificate — so do not copy that sentence forward. **F12** — a
corrected summary needs a hunk at the originating prose. **F17** — four surfaces:
the fan-out header, `notes/Phase39.md`'s `**Status:**` header **and** its *Blockers*
W4 bullet **and** *Hand-off*, and **`ROADMAP.md`'s Status row**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction WPAIR".) Labels
**(PAIR-1)–(PAIR-6)**, ***Steps PR1–PR6***, owning file
`notes/Pencil-W4-informal.md` §widened kernels (routes 1/3). All **0-hit**.
**Return any unconsumed remainder** — WELOC returned (EL-6) and that is the good
habit. **`EP-` was rejected on the (L5) substring rule**: `(EP-1)`/`(EP-2)`/`(EP-4)`
hit inside **`STEP-1`**, **`STEP-4`** and `perp-transport` in three Phase-23 /
archive files. **Qualify `(E)`, `(E-pair)` and especially `(S1)`–`(S5)` with their
owners** (L3) — that token has three owners across the doc set.

### Budget — measured at this prep

**`notes/Phase39.md` is at 570/580 lines, 512/525 header words** — both tight, and
**the prep does not have room to spend**: it rotates the header's landed block and
otherwise adds only the in-flight lines. **The landing must MERGE or ROTATE, not
append** — three landings running have done so successfully. The `(K-bare)` gap-map
row is at **1 544 / 1 600** and is **not this direction's** (it is the (BE-14)
thread's); the next landing on *that* thread needs a recompute to a target (F21).

### LANDING WRITE-UP — WPAIR, 2026-09-02: **(E-pair) is REDUCED to one hub-graph condition, and two strata of it are PROVED**

**HIT shapes 3, 4 and 5; NOT shape 1, NOT shape 2.** The spec ranked *"(E-pair)
PROVED"* first, *"a residual with no adjacent degree-`2` pair"* second and
*"reduced to a named checkable condition"* third. **Shape 3 is what landed** — the
**seed condition (PAIR-5)** — but it landed with two strata of shape 1 proved
outright and with the obligation's arithmetic pinned exactly, so the reduction is
not a restatement: it names a condition with no feasibility geometry in it, and it
comes with a proof that the two configurations the arc could previously not exclude
are excluded.

**The coordinator's counting guess was right, and it is an exact identity, not an
estimate.** The prep offered *"if every branch has `≤ 1` interior vertex then `|V|`
and `|E|` are both controlled by the hub set"* as a guess. It is (PAIR-1):

> if `G` is simple with min degree `≥ 2` and its degree-`2` vertices form an
> **independent set** — the exact negation of (E-pair) — then
> `f(V(G)) = 6 + e₀ + 2σ`, with `e₀ = |E(G[hubs])|` and
> `σ = Σ_{hubs}(deg − 3) ≥ 0`.

So ¬(E-pair) forces `f(V(G)) ≥ 6 + e₀ ≥ 6`, with equality exactly at the **full
subdivision of a 3-regular multigraph**. Three things fall out at once: **(E-pair)
follows from `f ≤ 5`**, one unit weaker than (E)'s `f ≤ 4`; a counterexample to
(E-pair) would **refute (E)** as well; and the whole ¬(E-pair) habitat is the
*over-braced* regime, the opposite of the two-small-cores regime that killed
(E-loc).

**The engine is (EL-4) strictly generalized, and the generalization is what does
the work.** (PAIR-2) computes the contraction criterion at an **arbitrary** rigid
set `U`: the (R1) closure makes every boundary attachment a hub, so `hcard(G/U)`
holds **iff at most two outside vertices adjacent to `U` are hubs** — `hcard` has
three slots, `v*` takes one, and the other two are *free*. Then (PAIR-3): **no
residual carries a rigid set with `|∂_hub U| ≤ 2`** (a *seed*), because the two ear
moves of *Step EL4*'s chain **never increase** `|∂_hub ·|` — an absorbed hub always
arrives with a hub neighbour already inside, by (EL-1) — so the chain runs from any
seed to a certified good contraction, a co-1 rigid subgraph or a spanning `C₃`.
(EL-4) is the corollary at `∂_hub = ∅`. The progression is now three deep and
worth naming: **(C1)+(C5) at a maximal cluster → (EL-4) at a shielded set →
(PAIR-3) at two free `hcard` slots.**

**One stratum of (E-pair) is PROVED.** If the hubs are independent (`e₀ = 0`, i.e.
`G` is a full subdivision) then *every* rigid set has `∂_hub = ∅` — the boundary of
a rigid set can only be reached through a hub–hub edge — so (PAIR-3) applies to the
rigid set the residual is required to carry. Hence **(PAIR-4)**: a counterexample
has `e₀ ≥ 1` and `f(V(G)) ≥ 7`, i.e. **(E-pair) follows from `f ≤ 6`**, two units
weaker than (E). The `f = 6` stratum — the one a naive search reaches first — is
closed.

**What remains is (PAIR-5), and it is a finite-per-instance question about the hub
graph.** By (EL-1) the hub graph `Λ = G[hubs]` has max degree `≤ 2`, so its
components are paths and cycles, and by (EL-4) every cycle component has length
`≥ 7`; `|∂_hub U|` counts the **dangling `Λ`-ends** of `U ∩ hubs`. A rigid set
whose hub part is a single `Λ`-sub-path is therefore automatically a seed, so a
counterexample needs **every** rigid set's hub part spread across `Λ` with `≥ 3`
dangling ends — while ¬(E-pair) makes the graph over-braced (`f ≥ 7`) and hence
rigid-set-rich. That tension is the content of (PAIR-5), the named successor, and
the natural attack is named with it: grow a rigid set *along* a `Λ`-run with the
Ear Lemma, the branches hanging off a run having interior length `≤ 1`.

**Job 3 over-delivers: (V) is a THEOREM given (E-pair).** The spec asked whether
(V) closes outright or whether its two `C₄`-carrying residues still need their own
argument. They do not: each residue's `C₄` is attached to at most **two** outside
hubs by (EL-1) — a *seed* — so (PAIR-3) forbids it ((PAIR-6)). Since (E-pair)
supplies exactly the `j ≥ 2` branch (V)'s case analysis consumes, and (T) kills the
third residue, **(V) closes the moment (E-pair) does**. WELOC's *"(V) holds outright
at `T32`"* is a **witness**; this is the theorem, and it holds for the same reason
(EL-4) does. **So W4's non-user-call cost is now ONE obligation, (PAIR-5)**, with
(K-res) the only other open item and a **USER call**.

**Job 2 paid a fourth time, and the standing verdict is: YES, and the gap has one
shape.** *The arc inventories landed CONCLUSIONS and records landed HYPOTHESES in
prose.* `ReducibleVertex.lean` carries **five** producers of "two adjacent degree-2
vertices", not the one *Step EL6* cited (`:893` the KT-4.6 root, `:1068` the
edge-bound form, `:1206` the deficiency form, `:1384` the degree-2 form, plus the
two edge bounds `:1270`/`:330` behind them) — and the cited one's `hedge` is
`(D−1)|E| < D(|V|−1) + (D−1)`, i.e. **`f ≤ 4`: it IS (E)**, not "an edge-count
hypothesis". Worse (better): `:893`'s **body** proves (E-pair) by the very double
count this direction needed, and that count only ever needs `f ≤ 5` — so the landed
statement carries a **one-unit slack**. Same shape as WTRI's transfers-vs-criteria
find and WELOC's one-role-of-two find. **The standing fix, one line:** before
declaring an obligation unprovable from the landed set, grep the owning file for
every declaration whose *name* contains the obligation's conclusion and read each
one's hypotheses **in the arc's own arithmetic**, never its docstring. Three of the
four finds would have been unmissable under that rule.

**Riders, each answered.** **F11** — *"no residual has all branches of interior
length `≤ 1`"* is an impossibility claim and is **not** claimed from a sweep: what
proves is (PAIR-3)+(PAIR-4), and the sweep is reported as *"0 residuals and 313/313
seed condition under cap C"*, with C disclosed (`≤ 16` branches ⇒ `≤ 10` hubs; the
pairing-model generator builds no `Λ`-cycle of length `≥ 7`, precisely what (EL-4)
leaves open). **Cap disclosure with the denominator named, matching WELOC's
standard:** the honest denominator over the 255-residual pool is **0, not 255** —
¬(E-pair) needs `f ≥ 6` and the pool's maximum is `2` (`T32` reaches `4`), so no
pool instance is even a candidate, and the recorded *"(E-pair) holds 255/255"* is a
restatement of `f ≤ 4` there. **And this is NOT (T)'s blind spot** — branch length
appears in no feasibility certificate, so a sweep *could* have seen a failure; what
rules the pool out is the arithmetic, not the certificate. **F12** — corrected
summaries carry hunks at their originating prose: §widened kernels' header
paragraph and *"what would change this"*, *Step EL6*'s 255/255 sentence and its (V)
paragraph, §(SAFE-RES)'s header paragraph and *Step 3*'s (E) bullet, (V) headline
and (V) residue bullet, and the *Confidence verdict* entry. **F17** — four surfaces
updated: this file's header, `notes/Phase39.md`'s `**Status:**` header **and** its
*Blockers* W4 bullet **and** *Hand-off*, and `ROADMAP.md`'s Status row.

**TERMINATION E1/E2/E3, read against their definitions
(`notes/Pencil-fanout-archive.md`) and reported, never fired.** They are stated
over the **kernel-(K)/(GR-15) ledger**; on the W4 side the reading is: **E1** wants
a counterexample to a *carried* obligation (its (K)-side form is a g-flank) — none
was exhibited, so **E1 does not fire**. **E2** wants the target refuted or
unprovable-as-posed **with no dispatchable attack left**: the target is neither
refuted nor unprovable — it is **reduced**, and the reduction *is* a named
dispatchable attack ((PAIR-5), with its Ear-Lemma-along-`Λ` route named), so **E2
does not fire**; the spec's E2 clause about specifying a successor applies to a
refutation, which did not happen. **E3 is ARMED and does NOT fire** — and the
claim that it comes within one step of firing is **CORRECTED by the coordinator at
this landing** (the loop assigns the E1/E2/E3 re-run to the coordinator, not to the
direction). Two things were conflated. **First, the corpus carries TWO E3
formulations**: GEXIST's — *target proven* **and** every remaining ledger entry
adjudication-gated — and the later spec's **deliberate deviation**, *"the target is
**proven** — full stop"*, which dropped the second conjunct on the recorded ground
that entries 2–4 stay dispatchable on any HIT. **Second, and this is the actual
error: "the target" in E1–E3 is the ARC's target, stated "over the ledger and the
target's status", never a direction's local obligation.** (E-pair) is not the arc's
target under either formulation. What proving it would empty is **W4's**
dispatchable list — not the phase's, since the whole (BE-14) thread stays
dispatchable — and E3's own stated purpose (the next spend becomes a user call,
because the Lean hold's release condition is met by a standalone-significant
informal proof) is not met either: `hcontract` is one of **three** carried items,
so proving (E-pair) does not release the hold. **E3 is not one landing away.**
The substantive report stands: (PAIR-6) removed (V) from the dispatchable list, so
**W4's non-user-call work is the single obligation (PAIR-5)**. Reported, not acted
on.

**What did NOT move.** (T) ((TF-1)–(TF-6)) is untouched and is *used* twice more
(the third (V) residue; (PAIR-2)(iv)'s triangle clause). (E-loc) stays **refuted**
and was not rescued; **(E) itself is untouched** — still open, still tight at
`f = 4` — and this direction deliberately did not attack it. (EL-1)–(EL-5) are
untouched and (EL-4) is *subsumed, not corrected*. (SAFE-RES) stays refuted,
(SAFE-RES′) open with `W19`/`S29`/`T32` intact; the `hnoGood'` vacuity refutation
stands. **(K-res), *Step 4*'s minimal widened statements, *Step 5*'s numerics and
the route-3/packaging-(b) adjudication (2026-08-02) are untouched**, and **(K-res)
stays a USER call**. Nothing on the (BE-14) side, `hnoGood'`'s vacuity, `hK`,
(GR-15) or class uniformity is touched. **A PENCIL event on the W4 side; the
phase-boundary consequence is reported, not acted on, and the 2026-08-05 Lean hold
binds — no `.lean`, and the `noRigid`-free cheap leaf stays parked.**

**Deliverable.** `notes/Pencil-W4-informal.md` §widened kernels (routes 1/3)
*Steps PR1–PR6* / **(PAIR-1)–(PAIR-6)**, plus the F12 hunks listed above; driver
`notes/scripts/w4/wpair.py` (`validate|sub|hunt|vee|pool`, 282 s, byte-identical at
pinned `PYTHONHASHSEED`); reservation consumed **six of six, nothing returned**.
`notes/check-gapmap-cells.py` **did not fire and was not skipped**: there is no
gap-map row on the W4 side and this direction did not open one.
`notes/check-phase-note.py` **did fire** and passes; the phase note was **merged and
rotated**, not appended. Run at **`recon-opus`** (fable unavailable this session).

## WGROW — sixty-first ordinal (single dispatch, prepped 2026-09-02) — the fourth W4-side direction

**Selection provenance: WPAIR's own named residual, taken under the standing
research-pick delegation — and the three binding criteria all point here.** *Max impact
on proving or disproving `PencilPair K 3 G`* (tenth check-in): **(PAIR-5) is the single
remaining non-user-call obligation of carried item #2**, so a HIT empties W4's
dispatchable list outright, leaving only the (K-res) **user call**. *Falsification as a
positive criterion* (seventh check-in): the refutation branch is unusually valuable here
— a counterexample that is a genuine **residual** refutes **(E)** as well, because
¬(E-pair) forces `f ≥ 7` ((PAIR-1)+(PAIR-4)) against (E)'s `f ≤ 4`. *Diversification*:
**this is the fourth consecutive W4-side direction, and that is a new concentration — it
is stated, not hidden.** The mitigation is structural rather than promised: on a HIT the
W4 thread's non-user-call list is **empty**, so the concentration self-terminates at this
dispatch; on a MISS the coordinator alternates back to (BE-14) candidate 1. Before WTRI
the W4 thread had taken **zero of sixty-five**, so four is a correction, not a habit.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this session).

### The target, stated exactly

> **(PAIR-5) Seed condition.** *Every simple, 2EC, triangle-free graph whose closed
> hub-neighbourhoods have `≤ 3` members, whose degree-`2` vertices form an independent
> set, and which carries a proper rigid subgraph, has a rigid `U ⊆ V(G)` with
> `3 ≤ |U| ≤ |V(G)| − 2` and `|∂_hub U| ≤ 2`.*

By **(PAIR-3)** that implies **(E-pair)**, hence **(V)** ((PAIR-6)), hence everything W4
needs short of (K-res). Prove it, **or** exhibit a counterexample in the class, **or**
reduce it to a named checkable condition. `wpair.py --hunt` found it holding **313/313**
under a cap that never generated the open configuration (below).

### THE COORDINATOR'S THREE READINGS — labelled TO BE TESTED, not inherited

`RESEARCH-ARC.md` §7 binds: a coordinator writing a spec is the party with the least time
on the question and the most authority over its framing. Each of the three below names
the surface it was read off, and **each is the direction's to confirm, sharpen or kill**.
Two of them are the reason this dispatch is priced as a slice rather than a wave.

**(1) (PAIR-5) AS STATED IS STRONGER THAN WHAT (E-pair) NEEDS — read off the implication
chain, not off numerics, and this is the most useful of the three if it holds.** The only
use of (PAIR-5) is: *given a residual `G` whose degree-`2` vertices are independent,
produce a seed and contradict (PAIR-3).* So it suffices to prove **(PAIR-5) restricted to
graphs that are residuals AND satisfy ¬(E-pair)** — and that restriction hands the proof
three hypotheses *Step PR5*'s class statement throws away:

- the **no-good-contraction clause** at every proper rigid subgraph (`hnoGood'`), which is
  the engine (PAIR-3)'s own proof runs on, plus feasibility and **no co-1 rigid set**;
- **every branch has `≤ 1` interior vertex** (that *is* ¬(E-pair)), so `G` is a *partial
  subdivision* of the hub multigraph and is determined by `Λ` plus a choice of which edges
  are subdivided;
- **`f(V(G)) = 6 + e₀ + 2σ ≥ 7` with `e₀ ≥ 1`** ((PAIR-1) + (PAIR-4)) — an over-braced
  graph, so rigid sets are *plentiful*, which is the tension *Step PR5* names.

**Prove the restricted statement and (E-pair) follows just as well.** If the direction
proves the unrestricted (PAIR-5) instead, say so — it is a stronger and reusable result —
but do not spend the dispatch on the extra generality if the restriction closes.

**(2) THE MONOTONE `|∂_hub|` INVARIANT IS UNCONDITIONAL — read off (PAIR-3)'s own proof
text and its second remark.** The non-increase of `|∂_hub ·|` along a `j = 1` or `j = 2`
ear absorption follows from **(PAIR-2)(i) + (EL-1) alone**: every absorbed hub arrives
with a hub neighbour already inside, and (EL-1) caps a hub at two hub neighbours. It needs
neither `|∂_hub S| ≤ 2` nor any branch-length hypothesis — the workbook says exactly this
(*"This needs no branch-length hypothesis, so (PAIR-3) is available to the whole arc"*).
**And the `j = 1` clause is a strict decrease when the absorbed vertex was itself a
boundary hub** (`∂_hub(S ∪ {x}) ⊆ ∂_hub S ∖ {x}`), so growth can carry `|∂_hub|` *down*
across the `3 → 2` threshold. That is what makes "grow until it is a seed" a coherent
attack rather than a category error. **Test it**: if the invariant turns out to need a
hypothesis the workbook dropped, that is a correction to (PAIR-3)'s remark and it must be
made at the originating prose (F12), not only in the write-up.

**(3) *Step PR5*'s `≤ 2k − 1` IS RIGHT BUT ITS CONVENTION IS UNSTATED — and with the Ear
Lemma threshold that convention decides the attack's shape.** *Step PR5* says *"an ear
through `k` consecutive hubs has `≤ 2k − 1` interior vertices"*. Re-derived: `k` hubs plus
at most `k − 1` subdivision vertices on the connecting branches — which is `2k − 1`
**only if the ear attaches directly at `z₁` and `z_k`** (each has a neighbour in `H`). If
one attachment runs through a subdivided branch the count is `2k`; if both, `2k + 1`.
Against the Ear Lemma's `j ≤ 5` (§(SAFE-RES) *Step 1*, and it is an **iff**) that gives:

> **one ear absorbs at most THREE consecutive hubs — and only two if either attachment is
> subdivided.**

So the named attack **cannot be a single ear along a long `Λ`-run**. It has to be
**iterated** short ears, and the quantity carried across the iteration is reading (2)'s
monotone `|∂_hub|`, not the run length. This is BGENUINE's lesson applied to the prep
itself (`RESEARCH-ARC.md` §7, sixth kind): a criterion quoted without its hypotheses hands
the dispatch the wrong yardstick. **Where the coordinator expects to be wrong:** the
`2k − 1` figure may be intended with a different attachment convention than the one
re-derived here, in which case the correction belongs at *Step PR5*.

### What is free — cite it, do NOT re-derive it

- **The whole WPAIR apparatus**: **(PAIR-1)** the deficit identity `f = 6 + e₀ + 2σ`;
  **(PAIR-2)** the contraction criterion at a general rigid set — in particular **(i)**
  (a rigid set's outside neighbours attach only at **hubs**, and a degree-`2` vertex of
  `U` has both neighbours in `U`) and **(iii)** (`hcard(G/U)` **iff** `|∂_hub U| ≤ 2`);
  **(PAIR-3)** the seed lemma; **(PAIR-4)** the closed `e₀ = 0` stratum; **(PAIR-6)** (V)
  as a theorem given (E-pair).
- **`Λ`'s shape, already pinned**: max degree `≤ 2` by (EL-1), so components are paths and
  cycles; **cycle components have length `≥ 7`** (length `3` by (T); lengths `4`–`6` are
  rigid by `isKDof_zero_of_cycle` with `∂_hub = ∅`, hence seeds, hence killed by
  (PAIR-3)); and `|∂_hub U|` counts **dangling `Λ`-ends** of `U ∩ W` ((PAIR-2)(i)).
- **(T) is a THEOREM** ((TF-5)): every residual is triangle-free.
- **(EL-1)**: in a feasible `G` every hub has **`≤ 2` hub neighbours**. **(EL-3)/(EL-4)**:
  a brick is a hub `C₄`/`C₅`, and no residual carries one.
- **The Ear Lemma** (§(SAFE-RES) *Step 1*): `H` rigid, `P` a path with both ends in `V(H)`
  and `j` interior vertices off `V(H)` — then `H ∪ P` is rigid **iff `j ≤ 5`**. `j = 1` is
  "a vertex with two edges into a rigid `H`".
- **`isKDof_zero_of_cycle`** (`Deficiency.lean:743`) / **`cycle_isProperRigidSubgraph`**
  (`Operations.lean:1082`): every cycle of length `≤ 6` is rigid. **(R1)**
  (`two_le_degree_of_isKDof_zero`, `Deficiency.lean:1306`): a rigid set has min degree `2`
  inside.
- **`T32`** (`weloc.py --witness`), a certified residual with `f = 4` — but note it does
  **not** satisfy ¬(E-pair), so it is a sanity instance here, not a target.

### Job 1 (PRIMARY, FORCED) — settle (PAIR-5)

Prove it (reading (1)'s restriction is enough), refute it, or reduce it. The named attack
is *Step PR5*(a): show some rigid set's hub part is a `Λ`-**sub-path**, since a sub-path
has at most two dangling ends and is therefore a seed. Reading (3) says that has to be
built by iterated short ears. **Two structural facts the coordinator did not check and
that look load-bearing:** where the *starting* rigid set comes from (the class hypothesis
gives a proper rigid subgraph, and (PAIR-4)'s proof shows `|V(H)| ≥ 3`), and whether the
iteration can be forced to *stay* inside one `Λ`-component. If the iteration stalls, the
stall configuration is itself the reduction (HIT shape 3).

**The refutation branch is worth its own sentence.** A counterexample must be a graph in
the class every one of whose rigid sets straddles `≥ 3` dangling `Λ`-ends. **State whether
your counterexample is a genuine residual**: if it is, it carries `f ≥ 7` and therefore
**refutes (E)** too — a much larger result than refuting the reduction route, and one that
re-routes W4. If it is only in the class (not a residual), the route dies but **(E-pair)
stays open**; say which, explicitly, because the two have completely different
consequences.

### Job 2 (FORCED) — the landed-inventory question, fourth time and now standing

WPAIR returned a **standing verdict**: *the arc inventories landed CONCLUSIONS and
mis-reads landed HYPOTHESES*, with the cheap fix — *before declaring an obligation
unprovable from the landed set, `grep` the owning file for every declaration whose NAME
contains the obligation's conclusion, and read each one's hypotheses in the arc's own
arithmetic, not its docstring*. **Run it against this direction's new consumer**, which is
different from the previous three: not feasibility criteria, but **producers of rigid
subgraphs and of ear/cycle extensions** — `Operations.lean`, `Deficiency.lean`, and
whatever `ReducibleVertex.lean` proves about `rigidContract`. One paragraph. If the fix
has now been applied prospectively rather than retroactively, say so — that is the
evidence that the standing verdict has been absorbed.

### Job 3 (FORCED, CHEAP) — the W4 cost list, and the E-rider reading

State **exactly** what W4's cost list is after this landing, distinguishing non-user-call
items from the (K-res) **USER call**. Then read E1/E2/E3 against their **actual**
definitions (`notes/Pencil-fanout-archive.md`) and **report, never fire**. One clause is
pre-corrected for you and quoting it wrong is the trap WPAIR fell into (`61e046a6`):

> **"The target" in E1–E3 is the ARC's target — `PencilPair K 3 G` — never a direction's
> local obligation.** Emptying **W4's** dispatchable list does **not** fire E3: the
> (BE-14) thread stays dispatchable, and `hcontract` is one of **three** carried items, so
> proving (PAIR-5) does not meet the Lean hold's release condition. Note also that the
> corpus carries **two** E3 formulations (GEXIST's two-conjunct text and a later
> deliberate one-conjunct deviation) — say which you read.

If the target is refuted, the **E2** clause turns on whether a successor is specified —
say so explicitly.

### What counts as a HIT — state which you got

1. **(PAIR-5) PROVED** (restricted per reading (1), or in full) — **W4's non-user-call
   cost list is EMPTY**, and (E-pair)/(V)/`hcontract`'s informal side all close behind it.
2. **A counterexample in the class** — with the residual/non-residual call made
   explicitly, because only the residual case refutes **(E)**.
3. **Reduced** to a named checkable condition strictly smaller than (PAIR-5).
4. **The standing inventory verdict**, run against the rigid-set-producer surface (job 2).
5. **The W4 cost list + the E-rider reading** (job 3).

Any of readings (1)–(3) **corrected** is a reportable result in its own right; say so
rather than silently working around it.

### Bars

- **Do not re-open:** **(T)** ((TF-5)); **(EL-4)** (no residual carries a brick);
  **(E-loc)**, REFUTED by `T32` ((EL-5)) — do **not** attempt to rescue it; **(PAIR-1)**,
  **(PAIR-2)**, **(PAIR-3)**, **(PAIR-4)**, **(PAIR-6)**, all proved and all re-verified
  by the coordinator at `61e046a6` and this prep; **(E)** itself, which is open, tight
  (`f = 4` at `T32`) and **not this direction's target** — the whole point of the (E-pair)
  route is to avoid it, and the only way (E) enters here is as *collateral* in the
  refutation branch; the route-3 / packaging-(b) adjudication (2026-08-02); `hnoGood'`'s
  vacuity refutation; **(SAFE-RES)**, refuted at `S29`; and the whole **(BE-14) thread**.
- **The Lean hold (2026-08-05) binds**: no `.lean`, in any file, for any reason. Pin
  statements; do not build them.
- **Not this direction, ranked separately:** **(K-res)**, a **USER call** — it is a bar,
  not a stretch goal, for the ninth consecutive spec; everything on the (BE-14) side.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity of the escape.

### Riders

**F11 — a driver per headline sentence, and the exhaustiveness class.** *"Every graph in
the class has a seed"* is a **universal** claim and *"every rigid set of `X` straddles
`≥ 3` ends"* is an **exhaustiveness** claim; both need an argument or an actual
enumeration, never a per-instance assert. **Cap disclosure MANDATORY with the DENOMINATOR
named** — and there is a specific, known cap to fix or disclose: `wpair.py --hunt`'s
313/313 ran under **`≤ 16` branches** (`rigid_vertex_sets`' `2^{branches}` enumeration)
and its **pairing-model generator builds no `Λ`-cycle of length `≥ 7`** — *precisely the
configuration (EL-4) leaves open*. A new driver that does not reach `Λ`-cycles has not
tested the open case; say so if it cannot.

**Harness.** `notes/scripts/README.md` binds and is **read first** — §1 for the primitives
that already exist (do not reimplement `rigid_vertex_sets`, the rigidity oracles, or the
`hcard` test), §2 for where a new module goes, §4 for the discipline. `w4/wpair.py` is the
direct ancestor and its five modes are the template; a new driver is `w4/wgrow.py`.
**Every script the project runs is committed** (2026-08-05 user requirement), probes
included, and the **figure-invariance gate is triggered by what the commit touches** —
adding a driver cannot move an existing figure, so record the one-line
`git diff --name-only -- '*.py' '*.m2'` / `git status --porcelain notes/scripts/` evidence
rather than re-baselining §3.

**F12 — a corrected summary needs a hunk at the originating prose.** Readings (2) and (3)
above are corrections-in-waiting at *Step PR3*'s remark and *Step PR5*'s attack paragraph;
if you confirm or refute either, edit **there**, not only in the write-up.

**F17 — four status surfaces**, all of which this prep has already set to *in flight* and
which the landing must move: the fan-out header; `notes/Phase39.md`'s `**Status:**` header
**and** its *Blockers* W4 bullet **and** *Hand-off*; and **`ROADMAP.md`'s Status row**.

**RESEARCH-ARC.md §7** — the three readings above are **hypotheses with their evidence
stratum named**. Kill any of them without ceremony; a refuted coordinator reading is a
finding, not a failure, and the tally of kinds is at §7.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction WGROW".) Labels
**(GROW-1)–(GROW-6)**, ***Steps GW1–GW6***, owning file `notes/Pencil-W4-informal.md`
§widened kernels (routes 1/3), driver `w4/wgrow.py`. All **0-hit in both cases**.
**Return any unconsumed remainder** — WELOC returned (EL-6) and that is the good habit.
**`SEED-`/`WSEED` was checked and REJECTED**: `(SEED` hits `random.Random(SEED)` in five
drivers and **`wseed` is a live local variable in `w4/kslide.py`**, which would have made
the driver un-greppable — (L5)'s substring rule firing on the lowercase half, one
direction after it fired on the uppercase half (`EP-` inside `STEP-1`). **Qualify `(E)`,
`(E-pair)` and especially `(S1)`–`(S5)` with their owners** (L3) — that token has three.
`Λ`-run / dangling `Λ`-end / `Λ`-component already have prose names from WPAIR: **re-use
them, do not mint labels for them.**

### Budget — measured at this prep

**`notes/Phase39.md` is at 568/580 lines, 491/525 status-header words** after this prep,
which bought room the way the note's own rule prescribes — by asking *what here is
reference rather than status* — compressing the (BE-14) status block and folding the three
W4 landings into one paragraph. That is **12 lines and 34 words** of headroom, the most a
landing has had in four; spend it, but **merge or rotate rather than append**, and a
landing's *Decisions made* entry stays **one line**. The prep also repaired a stale
surface: the `**Status:**` header still said *"E3 is ... ONE LANDING AWAY"*, which
`61e046a6` had refuted in *Hand-off* and the write-up without fixing the header — an F17
miss in a **coordinator** commit, which is exactly the second half of `RESEARCH-ARC.md` §7
(coordinator artifacts need the same verification tier as a subagent's). No gap-map row is
touched by this direction and none is opened, so `notes/check-gapmap-cells.py` will not
fire — **state that, do not skip it**.

### LANDING WRITE-UP — WGROW, 2026-09-02: **(PAIR-5) is REFUTED as stated and PROVED where it is used — so (E-pair) is a THEOREM and W4's non-user-call list is EMPTY**

**HIT shapes 1, 2, 3, 4 and 5 — all five, and shapes 1 and 2 are about *different
statements*, which is the whole result.** The spec ranked *"(PAIR-5) PROVED"*
first and *"a counterexample in the class"* second and treated them as
alternatives. They are not: **(PAIR-5) as *Step PR5* states it is FALSE**, and the
restriction the spec's reading (1) identified as *all that is consumed* is a
**THEOREM**. So reading (1) is confirmed in the strongest available sense — the
restriction is not merely sufficient, it is **necessary**.

**The refutation is five vertices: `K₂,₃` ((GROW-5)).** Two hubs joined by three
subdivided branches. It is in the class (simple, 2EC, triangle-free, `hcard`,
degree-`2` set independent) and it **carries a proper rigid subgraph** — its `C₄`,
rigid by `isKDof_zero_of_cycle`, on `4 ⊊ 5` vertices, which is exactly
`IsProperRigidSubgraph` (`Deficiency.lean:483`: `2 ≤ |V(H)|` and `V(H) ⊊ V(G)`).
But a seed needs `3 ≤ |U| ≤ |V| − 2 = 3`, and every 3-subset carries `≤ 2` edges
(`def = 2`). **The residual/non-residual call, made explicitly as the spec
demands:** `K₂,₃` is **NOT a residual** — the co-1 rigid set that saves it is
precisely what a residual forbids — so this refutation says **nothing about (E)**,
which stays open and tight at `f = 4`. And it is the **only** counterexample: a
seedless class member forces `f(V(G)) ≤ 7`, hence a cubic hub multigraph with
`e₀ ≤ 1`, hence (via `U(W ∖ {z})` at any hub with no `Λ`-edge) exactly two hubs.

**The theorem is a two-line count once the carrier is right ((GROW-4), the SEED
DICHOTOMY):** *every class member has a seed **or** a co-1 rigid set* — no
proper-rigid-subgraph hypothesis needed. A residual has no co-1 rigid set, so it
has a seed, which **(PAIR-3)** forbids: **no residual has an independent degree-`2`
set, i.e. (E-pair) is a THEOREM** ((GROW-6)), and with (PAIR-6) so is **(V)**.

**The change of carrier is the reusable part ((GROW-1)/(GROW-2)).** A class member
is the partial subdivision of its **hub multigraph** `M`; weight an `M`-edge `5`
when it is a `Λ`-edge and `4` when it is subdivided; then for a partition `Q` of
the hubs into `k` parts,

> `exc(Q) = 5a + 4b − 6(k−1) = 6 + a + 2·Σ_i (c(X_i) − 3)`,

and **`G[U(A)]` is rigid iff `exc ≥ 0` on every partition of `A`**, with the
finest partition giving back (PAIR-1). Rigid sets are hub-closed and `∂_hub` is a
`Λ`-cut, so **the entire question lives on `M`**: no feasibility geometry, no
deficiency oracle, no `|V|` cap. (GROW-4)'s proof is then: take a minimum-excess
partition with `k ≥ 2`; **each of its parts is rigid** ((GROW-3), the refinement
step); *no seed* forces `c ≥ 3` at every part (`≥ 3` dangling `Λ`-ends at the
non-singletons, min degree `3` at the singletons); so `exc ≥ 6` everywhere; so
deleting any single subdivided edge leaves `exc ≥ 2 > 0`, i.e. `V(G)` minus that
branch's interior vertex is rigid — a co-1 rigid set.

**The named attack was not completed, it was SUPERSEDED — and reading (3) is why
it could not have been completed as stated.** *Step PR5*(a) proposed growing a
rigid set **along** a `Λ`-run. (GROW-4) grows nothing; it reads `|∂_hub| ≥ 3` off
**every part at once**. Reading (3) is **confirmed verbatim** (`2k−1 / 2k / 2k+1`
by attachment convention; `j ≤ 5` caps one ear at three consecutive hubs, two if
either attachment is subdivided), and reading (2) is **confirmed and bounded**: the
`|∂_hub|` invariant is unconditional for (PAIR-3)'s **two** moves (726 `j = 1`
absorptions, all non-increasing) but is **not** a property of ear absorption in
general — absorbing a hub through **two subdivided branches** is an ear with
`j = 3` and can **strictly grow** the count (241 witnesses). That is the precise
reason "grow until it is a seed" does not close, and it is a **correction to the
prep's own framing**, made at *Step PR3*'s remark (F12), not only here.

**Job 2 paid a fifth time, and the find is the largest yet: a whole FACE of the
central definition.** `Graph.deficiency` is *defined* as a maximum over partitions
(`Deficiency.lean:273`/`:262`), and on top of it sits a landed **Jackson–Jordán
tight-partition layer** (Phase 32's Jacobs chapter, same file): `IsTightPartition`
(`:1929`), `exists_isTightPartition` (`:1940`), `partitionDef_merge` (`:1978`),
`IsTightPartition.subfamily_le` (`:2038`, JJ 3.2(a)) and
`IsTightPartition.parts` (`:2091`, JJ 3.2(b)). **`notes/Pencil-W4-informal.md`
cited none of it — `partitionDef` occurs 0 times in the whole W4 arc**, which had
argued about deficiency only through the edge-count face. (GROW-2)–(GROW-4) are
that face applied to this arc's own class. **The standing verdict is therefore
sharpened, not merely re-confirmed:** the sibling arc **had** read the object
(`notes/Pencil-informal.md`: 16 `partitionDef` citations, direction BINDUC), so the
gap is **per-arc**, and the new one-line rule is *grep the SIBLING WORKBOOK for the
Lean file you are about to cite; if the other arc reads more of it than you do,
the difference is your inventory gap.* Asked whether the fix has been applied
prospectively: **half of it, honestly** — the `grep`-the-owning-file rule was run
before planning and is what surfaced the tight-partition layer; the
sibling-workbook half was invented while running it.

**Job 3 — the W4 cost list, and the E-rider.** Non-user-call items: **NONE**.
(T) theorem ((TF-5)); (E-loc) refuted and unnecessary ((EL-5)/(EL-6)); (E-pair)
theorem ((GROW-6)); (V) theorem ((PAIR-6)); (PAIR-5) settled both ways. (E) itself
stays open and tight but is on no W4 path. The only open W4 item is **(K-res)**,
a **USER call**. **E-rider, read and NOT fired:** E1–E3 are the (BE-14)/(GR-15)
arc's test, over that arc's ledger and target. I read **both** E3 texts — GEXIST's
two-conjunct form (`notes/Pencil-fanout-archive.md:1700`) and the later deliberate
one-conjunct deviation (`ibid.:2098`) — and under either **E3 does not fire**: the
target is `PencilPair K 3 G`, unproven, and the (BE-14) thread stays dispatchable.
**E2 does not fire** (its second conjunct is false). One thing worth recording:
**E2's literal text says *"the direction's target"* while E3's says *"the
target"***, so the prep's pre-correction is a correction to E2's letter rather
than a restatement of it — under E2's letter its first conjunct would arguably be
met here, and only the second conjunct stops it. **E1** needs a g-flank; none.

**Riders, each answered.** **F11** — the two universal/exhaustiveness sentences are
carried by **proofs**, not by the sweep: *"every class member has a seed or a co-1
rigid set"* is (GROW-4), and *"`K₂,₃` has no seed"* is an **enumeration of all ten
3-subsets** with their deficiencies printed. The sweep is a check, and its cap is
disclosed **with the denominator named**: 1 016 class members, `|V| ≤ 27`, `≤ 10`
hubs (the `2^{|W|}` seed enumeration), `f ≤ 37` — and **118 of them carry a
`Λ`-cycle of length `≥ 7`**, the configuration `wpair.py --hunt`'s pairing-model
generator could not build and the one (EL-4) leaves open. That specific known cap
is therefore **fixed, not merely disclosed**, by the hub-model change of carrier.
The 255-residual pool's denominator is still **0, not 255**. **F12** — hunks at the
originating prose: *Step PR3*'s invariant remark (reading (2)), *Step PR5*'s
statement block, its *"what would settle it"* bullet and its coordinator
annotation (readings (1)/(3)), *Step PR6*'s consumer-state paragraph, §(SAFE-RES)'s
header, its *"what would change this"*, the file's *Purpose* paragraph, and the
*Confidence verdict* entry. **F17** — four surfaces moved off *in flight*: this
file's header, `notes/Phase39.md`'s `**Status:**` header **and** its *Blockers* W4
bullet **and** *Hand-off*, and `ROADMAP.md`'s Status row. **Harness** —
`notes/scripts/README.md` read first; no primitive reimplemented (both landed
rigidity oracles used, and they agree on all 39 989 cross-checked subsets); the new
driver is `w4/wgrow.py`, four modes, 204 s, byte-identical across two runs at
`PYTHONHASHSEED=0`; §1 primitive index and §3 invocation table extended. **No
gap-map row is touched by this direction and none is opened**, so
`notes/check-gapmap-cells.py` does not fire — stated, not skipped.

**Reservation, and the unconsumed remainder.** All six reserved labels were used:
**(GROW-1)** the localized deficit identity, **(GROW-2)** the hub-multigraph
criterion + hub closure, **(GROW-3)** the rigid parts of a minimum-excess
partition, **(GROW-4)** the seed dichotomy, **(GROW-5)** `K₂,₃`, **(GROW-6)**
(E-pair) as a theorem; *Steps GW1–GW6* likewise. **Nothing is returned.** Two
by-products a successor should know about, neither minted as a label: (GROW-3) is a
**strengthening of the landed `IsTightPartition.parts`** (JJ 3.2(b) gives `≥ 3`
vertices and `≥ 2` in-part edges; (GROW-3) gives rigidity of the part) and is the
obvious next leaf if this arc is ever built in Lean; and (GROW-2)'s criterion is
stated for the (PAIR-5) class but its proof only uses *degree-`2` vertices are
independent*, so it transports to any partial subdivision.

**What this costs the phase.** The W4 thread's **non-user-call dispatchable list is
now empty**, which is exactly the self-termination the spec's diversification
paragraph promised on a HIT. The concentration ends here on its own terms; the next
pick is a (BE-14)-side one or a user call on (K-res)/the Lean hold.

## BBASE — sixty-second ordinal (single dispatch, prepped 2026-09-02) — back to the (BE-14) thread

**Selection provenance: the coordinator's own alternation rule, fired exactly where the
WGROW spec said it would be.** W4's non-user-call list is **empty** ((GROW-6)), so the
four-direction W4 concentration self-terminated; the user, offered the Lean hold and the
(K-res) wave alongside continuing, chose **continuing**, leaving **both standing calls
untouched**. That returns the loop to the ranked list, whose **candidate 1** is this: the
**flag base off the no-adjacent-hubs class** ((BE-65)(i)/(BE-68)(ii) item 1) — one of the
**two** things standing between half (B) and a class statement, and by the thread's own
assessment **the smaller of them**.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this session).

### The target, stated exactly

> **(BE-68)(ii) item 1.** *When the skeleton has real hub–hub edges, the flag base is a
> pencil-realization problem for `B_real`* — the graph whose edges are the **length-1**
> branches — *and that is the phase's own problem one level down.*

Concretely ((BE-65)(i)): a legal flag assignment is a point `p_z` and a plane `π_z ∋ p_z`
per hub, with `p_{z'} ∈ π_z` and `p_z ∈ π_{z'}` for every `B_real`-edge `zz'`. The base is
a **product of irreducible rational bundles iff `E(B_real) = ∅`**. **Settle what it is off
that class**: nonempty? irreducible? rational, with dense ℚ-points? If yes, half (B)'s
residue drops from **two** items to **one** ((BE-67)(iii) alone).

### THE COORDINATOR'S THREE READINGS — labelled TO BE TESTED, not inherited

`RESEARCH-ARC.md` §7 binds; each names the surface it was read off. Readings (1) and (2)
are the reason this is priced as one slice rather than a wave, and **reading (1) is a
join of two sentences that are already both in the workbook, one *Step* apart** — so if it
holds, the arc has been carrying a much smaller residue than (BE-68)(ii) says.

**(1) `B_real` HAS MAX DEGREE `≤ 2`, SO ITS COMPONENTS ARE PATHS AND CYCLES.** (BE-65)(ii)'s
own paragraph *"What `hcard` is, seen from here"* states it: `hcard` *"is the condition
that every hub have at most two hub neighbours"*. `B_real`'s edges are exactly hub–hub
edges ((BE-65)(i)). So under `hcard`, `B_real` is a disjoint union of **paths** (including
isolated vertices and single edges) and **cycles** — not an arbitrary graph on `|W|`
vertices. *"The phase's own problem one level down"* is then the phase's own problem on
the **thinnest** graphs it has, which is a different proposition from the one
(BE-68)(ii) records. **Read off the workbook, not measured.**

**(2) THE BASE FACTORS OVER `B_real`'s COMPONENTS, AND (CH-1) ALREADY SETTLES THE CYCLES OF
LENGTH `≥ 4`.** (BE-65)(i)'s proof says the *only* conditions are `p_z ∈ π_z` plus mutual
incidence **per `B_real`-edge** — per-edge conditions, so the base is a **product over
connected components** of `B_real`. On a cycle component of length `≥ 4`, all three of
**(CH-1)**'s hypotheses hold: `hcard` (degree 2 means `≤ 2` hub neighbours), **min degree
2** (it is a cycle), **girth `≥ 4`** (the cycle's own length). So §(K-chart)'s theorem
applies **verbatim** and those components are free — nonempty, irreducible, ℚ-rational,
dense ℚ-points. **What is left is then two named cases, not one open problem:**

- **PATH components** (`m ≥ 2` vertices) — **min degree 2 fails at the two ends**, and that
  is (CH-1)'s hypothesis, not an artifact. This is the real residue.
- **TRIANGLE components** — **girth 3 fails**, and this one is *known not to be merely
  technical*: **(CH-5)** found that girth `≥ 3` does **not** give nonemptiness, *"a
  Λ-triangle with a non-hub on two of its hubs empties the tower at every seed"*, and
  **(BE-72)** records *"isolated emptiness is real (a **triangle on two hubs**)"* and
  **absorbed by the existential**. Say whether the same absorption argument covers the
  base here, or whether a `B_real`-triangle is a genuine obstruction.

**(3) THE PATH CASE LOOKS LIKE (CH-1)'s OWN TOWER WITH A WEAKER HYPOTHESIS, NOT A HARDER
PROBLEM — and this is the reading most likely to be wrong.** §(K-chart) *Step CH3*'s tower
is *hub points free, hub normals in `ker A_h(q)`, non-hub points in the intersection of
their hub neighbours' planes*. Along a path `z₁ … z_m` the greedy order gives `p₁` free
(3 params), `π₁ ∋ p₁` (2), then per step `p_{i+1} ∈ π_i` (2) and `π_{i+1} ∋ p_i, p_{i+1}`
(1, the pencil of planes through the line `p_i p_{i+1}`) — a tower of affine-linear
fibrations with irreducible rational fibres, hence irreducible and rational with dense
ℚ-points. **Where the coordinator expects to be wrong:** that fibre dimension is **not
constant** where consecutive points coincide (`p_i = p_{i+1}` makes the plane fibre
2-dimensional, not 1), and constancy of fibre dimension is precisely what (CH-1)'s tower
argument and **(CH-6)** are careful about. It is entirely possible that min degree 2 is
(CH-1)'s hypothesis *because* of that jump, in which case a path is harder at its ends
rather than freer. **Re-derive the count; do not inherit it.**

### Job 1 (PRIMARY, FORCED) — settle the flag base off the no-adjacent-hubs class

Prove it free, exhibit an obstruction, or reduce it to a named case. Readings (1)–(3) are a
proposed decomposition, not a route you owe anything to. **What "free" has to mean** is set
by the consumer: (BE-65)(iii) buys *one exact-ℚ draw settles the generic value* from
irreducibility, and (BE-64)/(BE-66)'s product theorem needs the base to be a variety the
per-branch chains fibre over — so say which of *nonempty / irreducible / rational / dense
ℚ-points* you get, separately, and which the consumer actually needs.

**If an obstruction appears, classify it before pricing it.** A `B_real` whose base is
**empty** at every flag is a different animal from one whose base is **reducible**: the
first is the (BE-72)/(CH-5) triangle phenomenon and may be absorbed by the existential; the
second breaks (BE-65)(iii)'s one-draw mechanism and would put a genuine new item on half
(B). Say which.

### Job 2 (FORCED) — the standing inventory verdict, PER-ARC, with an immediate target

WGROW sharpened the verdict to **per-arc**: *grep the sibling workbook for the Lean file
you are about to cite* — the W4 arc had cited **no** part of `Graph.deficiency`'s landed
**partition** face while this workbook cites it 16 times. **The immediate instance here
runs the other way, and reading (1) rests on it:** is **`hcard` available at the pieces of
this thread**, or is it only the **sampler's** cap? (BE-65)(ii) says *"the arc's standing
sampler cap is not an artifact; it is (CH-1)'s hypothesis"* — a statement about the
sampler, not about the pieces. The **sibling W4 arc has a landed answer**:
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`), which W4
reads as **(EL-1)** — *every hub of a graph carrying a nondegenerate pencil realization has
`≤ 2` hub neighbours* — a **necessary condition**, not a modelling choice. Settle whether
it transports to the pieces `H` here. **If it does not, reading (1) fails and job 1 is a
larger question than this spec prices; say so plainly rather than working around it.**

### Job 3 (FORCED, CHEAP) — the residue, and the E-rider

State what half (B)'s residue is after this landing — **one** item or **two** — and what
(BE-14) is left with. Then read E1/E2/E3 against their **actual** definitions
(`notes/Pencil-fanout-archive.md`) and **report, never fire**. One clause is pre-corrected
and quoting it wrong is the trap WPAIR fell into (`61e046a6`):

> **"The target" in E1–E3 is the ARC's target — `PencilPair K 3 G`** — never a direction's
> local obligation. The corpus carries **two** E3 formulations (`:1700`'s two-conjunct text
> and `:2098`'s deliberate one-conjunct deviation); say which you read. WGROW recorded a
> further wrinkle worth checking: **E2's literal text says *"the direction's target"* while
> E3's says *"the target"***, so the correction is to E2's letter rather than a restatement
> of it.

### What counts as a HIT — state which you got

1. **The flag base is FREE off the no-adjacent-hubs class** — half (B)'s residue drops to
   the single item (BE-67)(iii), and (BE-68)(ii) is rewritten.
2. **Free on a named sub-class, with the rest named** (readings (1)/(2)'s decomposition, or
   a better one) — a reduction, and the honest shape if the triangle case resists.
3. **An obstruction**, classified empty-vs-reducible per job 1.
4. **The `hcard`-availability verdict** (job 2) — and it is load-bearing, not bookkeeping.
5. **The residue statement + the E-rider reading** (job 3).

Any of readings (1)–(3) **corrected** is a reportable result in its own right.

### Bars

- **Do not re-open:** the flag **coincidence** — genuine and harmless, a **checked
  hypothesis**, not an item ((BE-84)/(BE-86)); the **shortfall** (`0` at 392/392); `(1,1)`
  peels ((BE-79), answered); the **SPREAD step** ((BE-74), closed); the **forced-empty `G`
  hunt** ((BE-72), impossible on (CH-1)'s class); the **exhaustiveness obligation**
  ((BE-70), retired — and completeness of the mechanism list is **not** claimed, do not
  claim it); **(BE-32)(+)**; **(BE-41)(ii)** (refuted and retired); **BWIN's window
  theorem**; **S-mark's pin**; the ear-decomposition induction ((BE-43)).
- **Not this direction, ranked separately:** **(BE-67)(iii)**, the class quantifier, beyond
  job 3's one sentence; **cross-pair welding** ((BE-28)(i)); **(S1)/(S2)** — and qualify
  that token, it has three owners; the **one-end-series** case; BTWOCUT's bundle
  construction.
- **The whole W4 side is CLOSED as an informal argument** ((GROW-6)) — do not re-derive it,
  and do not treat `K₂,₃` appearing on both threads as a result (see *Riders*).
- **The Lean hold (2026-08-05) binds**: no `.lean`, in any file, for any reason.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity, **(K-res)** (a USER call).

### Riders

**F11 — a driver per headline sentence.** *"Irreducible"*, *"rational"*, *"free"* and
*"the only obstruction"* are all **exhaustiveness-class** claims: they need an argument, or
an enumeration that actually enumerates. A sampler that draws legal flags and finds no
failure shows **"none found under cap C"**. **Cap disclosure MANDATORY with the DENOMINATOR
named** — WELOC's *"0, not 255"* and WGROW's *"1 016 class members, 118 carrying a `Λ`-cycle
of length `≥ 7`"* are the standard.

**F21 + `RESEARCH-ARC.md` §6 — the gap-map row, and this one binds at the landing.** The
`(K-bare)` row is at **1 544 / 1 600 words**, 56 spare. That is the *pointless-recompute*
position §6 names: do **not** append a since-direction-BBASE clause. **Recompute to a
target** that leaves headroom for the landings already queued on that namespace, and
**verify label preservation by a scripted set-diff, never by eye** — the coordinator's own
hand-recompute once dropped a live label and only a script caught it.
`notes/check-gapmap-cells.py` gates the cap; it does not gate the labels.

**Harness.** `notes/scripts/README.md` binds and is **read first** — §1 for the primitives
(`bdecor.py`'s chart instruments, `bpeel.py`, `bsharp.sample_piece_config_adj`,
`widened.place_pencil_general`; do not reimplement them), §2 for layering, §4 for the
discipline. Every script is committed; the figure-invariance gate fires only if a **tracked
driver is modified**, so if you only add `w4/bbase.py`, record the one-line
`git diff --name-only -- '*.py' '*.m2'` / `git status --porcelain notes/scripts/` evidence
instead of re-baselining §3.

**F12** — readings (1) and (2), if confirmed, are corrections *in waiting* at **(BE-65)(i)**
(which calls the off-class base *"the phase's own problem"* without the max-degree-`≤ 2`
qualifier) and at **(BE-68)(ii) item 1** (same). Edit **there**, not only in the write-up.

**F17 — four status surfaces**, all set to *in flight* by this prep and to be moved by the
landing: the fan-out header; `notes/Phase39.md`'s `**Status:**` header **and** *Hand-off*
(its *Blockers* W4 bullet is **not** this direction's); and **`ROADMAP.md`'s Status row**.

**A convergence to notice and NOT to manufacture.** WGROW's unique (PAIR-5) counterexample
is `K₂,₃`, and this thread's named triangle-free admitting shape at (BE-86) is **also
`K₂,₃`** — two independent directions, two different threads, one day apart, same five-vertex
graph. That is the F18 cross-return shape and is worth **one sentence** if you see why, and
**nothing at all** if you do not. Do not build a connection to report one.

**`RESEARCH-ARC.md` §7** — readings (1)–(3) are hypotheses with their evidence stratum
named. Kill any without ceremony; the tally of outcome kinds is at §7 and now runs to seven
instances and six kinds.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BBASE".) Labels
**(BE-89)–(BE-93)**, ***Steps BE88–BE92***, owning file `notes/Pencil-informal.md`
§(K-bare-ext) — **extends, no new section**, per the thread's standing convention — driver
`w4/bbase.py`. The reservation opens exactly at the tail BGENUINE's registry row declared.
**Return any unconsumed remainder.** **`BFLAG` was checked and NOT chosen**: it is no longer
0-hit (BSHARP's prep and its fan-out section both record having rejected it), and BSHARP's
recorded ground still stands — *it names the apparatus, the point-plane flag, rather than
the question*. `BBASE` names the object the question is about and **not a predicted
answer**, per BGENUINE's precedent. Prefer **prose names** for new configuration-level
objects, as BSPREAD, BONEONE and BGENUINE all did.

### Budget — measured at this prep

**`notes/Phase39.md` is at 568/580 lines, 503/525 status-header words** — 12 lines and 22
words of headroom, bought at the WGROW landing by rotating the four W4 landings into one
paragraph plus a workbook pointer. The prep spends only the in-flight lines. **The
`(K-bare)` gap-map row at 1 544/1 600 is the tighter constraint** and is the landing's, not
the prep's — see *Riders*. No gap-map row is touched by this **prep**, so
`notes/check-gapmap-cells.py` will not fire on it; the **landing** touches exactly one and
must run it.

---

### LANDING WRITE-UP — BBASE, 2026-09-02: **the flag base is FREE, and it was never (CH-1)'s object — half (B)'s residue drops from TWO items to ONE**

**HIT shape 1, plus shapes 4 and 5, and shape 3 partially.** The base is free off the
no-adjacent-hubs class; job 2's `hcard` verdict is load-bearing and comes out **two ways**;
job 3 is delivered. Shape 3 partially: an obstruction **exists** and is classified
**reducible, not empty** — the exact distinction job 1 asked for — but it is unreachable on
the class. **All three coordinator readings are corrected**, which the spec records as a
reportable result in its own right.

**The object was misidentified, and that is the whole result ((BE-89)).** (BE-65)(i) calls
the off-class base *"the phase's own problem one level down"*; (BE-68)(ii) carries that
forward as half (B)'s residue item 1. It is the wrong ambient. The base is the **flag
variety** of `B_real` — a point *and a plane* at **every** vertex — whereas §(K-chart)'s
`𝒜(Γ)`, the object (CH-1) is about, carries a normal only at a vertex of **degree `≥ 3`**.
Under `hcard` those two sets are nearly disjoint: a path or cycle component of `B_real` has
**no** §(K-chart) hub at all, so `𝒜(B_real)` has **no normals** and is a different variety.
Read instead as §(K-chart) *Step CH3*'s tower **with the hub set taken to be all of `W`**,
the base is its **stages 1 and 2 only** — and stages 3 and 4 are exactly where (CH-1) spends
*min degree 2* and *girth `≥ 4`* ((CH-5)). So the base's hypotheses are strictly **weaker**
than (CH-1)'s, and the (BE-72)/(CH-5) twin-plane obstruction **cannot even be stated** here:
it is about a non-hub's two panels failing to meet, and there is no non-hub and no meet.
Corollary, unconditional: **`Base(B_real) ≠ ∅` for every `B_real`** — put every point at one
`p` and every plane at one `π ∋ p`.

**The forest theorem is the positive content, and it needs nothing ((BE-90)).** For any
`Π ∈ Fl` the fibre `F_Π = {(p,π) ∈ Fl : p ∈ π₀, p₀ ∈ π}` is irreducible of **constant**
dimension `3` — a `P¹`-bundle over `π₀ ∖ {p₀}` together with its `p = p₀` boundary, which
lies in the closure. So on a **forest** `B_real` the base is a tower of such fibres over
`Fl`, Zariski-locally trivial by `PGL₄`-homogeneity: **nonempty, irreducible, ℚ-rational
with dense ℚ-points**, of dimension `5|W| − 2|E| = 5 + 3(m−1)` per tree — *with no
genericity, no degree bound, no girth and no min-degree hypothesis*. A **unicyclic**
component follows on the constant-rank locus ((BE-91)(iii)): its trees attach to the cycle
by the same tower. Together: **every component of cyclomatic number `≤ 1`**.

**Reading (3) is corrected, and it was the right one to distrust — for the wrong reason.**
The greedy tower the spec proposed (`p_{i+1} ∈ π_i`, then `π_{i+1}` through `p_i p_{i+1}`)
*does* jump where `p_i = p_{i+1}`. The jump is an artifact of **splitting the flag into
two sub-stages**; as one stage, `Π_{i+1} ∈ F_{Π_i}`, the fibre is equidimensional. So min
degree 2 is **not** (CH-1)'s hypothesis because of that jump, and a path is not harder at
its ends — it is **freer than a cycle**. Driver-exhibited: `25` constructed `p₁ = p₂` base
flags, every one legal and a **smooth** point of the same `5|W| − 2|E|` component.

**Reading (2) is refuted outright** — (CH-1) does not apply to `B_real` at all, so it
settles no cycles, of any length. **Reading (1) is refuted as stated** and replaced by
something sharper ((BE-93)(i)): `W` is the **marked-pair-augmented** hub set, so
`d_z(B_real) = d_z(Λ(H)) + |N_H(z) ∩ ({u,v} ∖ hubs(H))|` and `hcard` caps only the first
term. `Δ(B_real) = 3` at **737** class-tier pieces. What survives is that
`B_real ∖ {u,v} = Λ(H)` has max degree `≤ 2`.

**Job 2, both halves.** `hcard` **DOES** transport to the pieces, and by an argument rather
than a measurement: `binduc.split_at_pair` returns genuine subgraphs (`E₁ ∪ E₂ = E`, no
virtual edge, body read this pass), so `Λ(H) ⊆ Λ(G)[V(H)]` and the sibling W4 arc's
**(EL-1)** — a landed, compiler-checked necessary condition, **read at one remove from
`notes/Pencil-W4-informal.md` because the 2026-08-05 Lean hold binds** — caps it. Measured:
**0 failures at 78 564 class-tier pieces**. And it does **not** cap `B_real`, which is why
reading (1) fails. So (BE-65)(ii)'s *"the arc's standing sampler cap is not an artifact"* is
right about `Λ` and silent about `W`.

**The obstruction, classified as job 1 demanded ((BE-92)).** Not emptiness — **reducibility**,
and only at short cycles. On a `B_real`-triangle all three planes **coincide identically**
on the constant-rank locus (`200/200`), while the **collinear stratum** — all points on one
line, all planes in that line's pencil — is legal with three *pairwise distinct* planes and
has flag dimension `10 > 9`. At a 4-cycle the two are `12 = 12`; from `m ≥ 5` the stratum is
strictly smaller and the measured tangent rank says it creates no component. Two things keep
it away: both extra components lie **off** the constant-rank locus, which is verbatim the
hinge-coincidence half of the proviso `G` that (BE-64)(ii) is already stated modulo; and on
the class a `B_real`-cycle **is** a cycle of `G`, so girth `≥ 6` forbids `m = 3, 4` outright.
**The shape is real one step away**: two of the seven `R_BATTERY` pieces of (BE-64)/(BE-66)
have `B_real` a 4-cycle at `girth(H) = 4`, and `bpeel.constructed_tier` reaches **118**
triangle components in `10 678` off-class pieces. The landed sampler draws inside the good
component at `16/16`, so **no landed figure moves**.

**Job 3 — the residue, and the E-rider.** Half (B) is left with **ONE** item, the class
quantifier (BE-67)(iii); (BE-14)'s open step is unchanged (S-mark). The named residue of
*this* direction is a `B_real` component of **cyclomatic number `≥ 2`**: `0` of `78 564`
class-tier pieces, `22` of `10 678` off-class ones, and at the smallest such shape the
expected dimension survives, so what is missing is an argument, not a witness. **E1/E2/E3
read against their actual definitions, none fires**, with the 2026-09-02 correction in
force — *"the target" is the ARC's, `PencilPair K 3 G`*. The reading used is **`:1700`'s
two-conjunct E3**, with `:2098`'s one-conjunct deviation noted and not used; WGROW's wrinkle
holds on inspection (**E2's letter says *"the direction's target"*** at `:1697` while E3's
says *"the target"* at `:1700`, so the correction is to E2's letter).

**Verification.** `python3 notes/scripts/w4/bbase.py validate` (33 s), five modes; full
tiers `census` (120 s) and `dim` / `forest` / `tri` / `cross` (`< 2 s` each). Class tier:
K4 **exhaustive** (`[1,6]⁶` at sum 18, `gridcol.class_shape`-certified) plus prism and K33
sampled `400` of `140 142` — `1 606` members, `78 564` peel pieces, `B_real` a **forest at
78 564/78 564**, girth `≥ 7` at `1 606/1 606`. Caps disclosed: all three tiers have `≤ 6`
hubs, so with girth `≥ 7` **no tier here can exhibit a `B_real` cycle** — the forest figure
is a cap boundary, not evidence about the class beyond it.

**Reservation consumed in full**; nothing returned. **F12 paid at source**: (BE-65)(i) and
(BE-68)(ii) item 1 are annotated where they stand. **F21**: the `(K-bare)` gap-map row
**recomputed** 1 544 → 1 385 words (cap 1 600, 215 spare) while absorbing five new labels,
label preservation by **scripted set-diff — 93 codes in, 98 out, zero dropped**; three
inline code spans dropped, each verified body-present. **The `K₂,₃` convergence was NOT
built**: nothing in this direction reaches `K₂,₃`.

**`RESEARCH-ARC.md` §7 — a SEVENTH kind, at the eighth instance: *INAPPLICABLE*.**
Readings (1) and (3) came back *refuted* and *corrected*, both familiar shapes. Reading (2)
is the new one: it cited a landed theorem that is **true**, about **cycles that are real**,
and **does not apply** — its ambient carries structure only at degree-`≥ 3` vertices while
the flag base carries it at *every* vertex. An inapplicable citation passes every check that
stays inside the cited section; it is caught only by opening that theorem's own **ambient
definition**. Recorded at `RESEARCH-ARC.md` §7, which now runs to **eight instances and
seven kinds**.

## BUNIF — sixty-third ordinal (single dispatch, prepped 2026-09-02) — half (B)'s LAST residue

**Selection provenance: there is only one item left on this side.** BBASE discharged the
flag base, so (BE-68)(ii)'s two-item residue is down to **one**: the **class quantifier of
half (B)**, (BE-67)(iii), item 0 on the ranked list and the only entry on it that half (B)
still needs. W4's non-user-call list is empty; the **(K-res) wave** and the **2026-08-05
Lean hold** were both offered to the user on 2026-09-02 and both **declined in favour of
continuing research**, so neither is in play.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this session).

### The target, stated exactly — and BPEEL already reduced it to one number

Do **not** re-derive the reduction; (BE-69)(iii) states it:

> `reach(H; x, y) := max_{A₁ ∩ A₂} dim(ρ̄₁ + ρ̄₂)`, attained on a **dense open** of
> `A₁ ∩ A₂`, i.e. the **generic** value. Hence
>
> **(BE-67)(iii) at `H` ⟺ `A₁ ∩ A₂ ≠ ∅` and `reach(H; x, y) = min(δ₁+δ₂, 6)`.**

`A₁ ∩ A₂ ≠ ∅` is **already free** — `A_i ≠ ∅` is (BE-14) for the side, the 2-cut
induction's own hypothesis rather than a new obligation, and irreducibility upgrades the
two to their intersection, which is the simultaneity clause (BE-25)(i) re-proved from the
same source. So the whole class statement is **one sentence**:

> **For every internal R-node piece `H` and every peel `(x, y)`,
> `reach(H; x, y) = min(δ₁ + δ₂, 6)`.**

Prove it, reduce it to a named checkable condition, or exhibit a **shortfall** — which by
(BE-71) is the only shape a third mechanism could take, and would be a large result in its
own right.

### THE CORRECTION THIS PREP MADE BEFORE DISPATCHING — read it, the target cited a REFUTED lemma

(BE-67)(iii) as landed says the general-position half's *"only located enemy is the flag
coincidence of (BE-66)(iii), **unforceable at an R-node peel** by (BE-66)(iv)"*.
**(BE-66)(iv) is refuted outright** ((BE-81), BONEONE): `π_u = π_v` **is** forced at an
internal R-node peel with both sides flexible, at **392 of 928**. The *conclusion* — the
enemy does not bite — survives, but by an entirely different route ((BE-84)–(BE-86),
BGENUINE): the certificate is a **hinge pair**, the forcing is **genuine pointwise**, and
the **shortfall is 0 at 392/392**. So the coincidence is a **checked hypothesis**, not an
unforceable one, and the enemy is *located and measured-harmless* rather than *excluded*.
Three landings made the correction at (BE-66)(iv) itself and **not** at the statement that
cites it; **annotated at source in this prep** (F12). **Do not inherit the parenthetical.**
Note also what is *not* affected: (BE-67)(iii)'s `Chart(H)`-irreducibility citation stands,
because (BE-89)'s correction to (BE-65) is about `𝒜(B_real)` — a different object.

### THE COORDINATOR'S TWO READINGS — labelled TO BE TESTED, not inherited

`RESEARCH-ARC.md` §7 binds, and its tally now runs to **eight instances and seven kinds**
after BBASE refuted all three of the last prep's readings — including the new
**INAPPLICABLE** kind, a prediction citing a landed theorem about a *different object*.
Both readings below are stated with the surface they were read off; kill either without
ceremony.

**(1) THE CLASS STATEMENT IS NOW ENTIRELY THE GENERAL-POSITION HALF — on current
evidence.** (BE-67)(iii) names two ways to fail. The **welded half** ((BE-22)(iii)(a)) is
*free at theta children* by (BE-66)(ii), and (BE-86) then found `ρ_i = δ_i + a_i` with
(BE-22)(iii)(a) **free** at **392/392** — so on everything measured it is not where the
statement can break. That leaves the **general-position half**, which is exactly what
`reach` measures. **To be tested:** whether the welded half is genuinely free
class-uniformly or only on the measured strata; if it is not, the class statement has two
halves and this reading is wrong about which one is open. Read off (BE-66)(ii) + (BE-86),
both measurements — **so this reading's evidence stratum is a sample, not an argument.**

**(2) (BE-70) MAKES `reach` A FUNCTION OF THE FLAG PAIR ALONE, AND BBASE HAS JUST MADE THE
FLAG PAIR'S OWN HOME FREE.** (BE-70): no topological branch crosses a 2-cut, so at fixed
flags `ρ̄₁` and `ρ̄₂` are functions of **disjoint coordinate blocks** sharing **one datum,
the flag pair `(ϕ_x, ϕ_y)`**, and the achievable pairs are the **full product modulo `G`**.
So `reach(H; x, y)` is a maximum over the flag pair of `dim(ρ̄₁(ϕ) + ρ̄₂(ϕ))` with each
side ranging independently over its own block — and (BE-89)–(BE-91) have just shown the
base those flags live in is **nonempty always**, irreducible and ℚ-rational with dense
ℚ-points, **hypothesis-free on a forest**. That is the shape of a class argument.
**Where the coordinator expects to be wrong:** `G` is precisely the cross-branch proviso
(BE-64)'s product theorem is stated **modulo**, and (BE-72) settles its emptiness only on
**(CH-1)'s class** — so an argument routed through the product may **inherit `G` as a
hypothesis** rather than discharge it, and would then prove a class statement about a class
the proviso defines rather than about internal R-node pieces. Say explicitly which class
your statement quantifies over.

### Job 1 (PRIMARY, FORCED) — settle `reach` uniformity

Readings (1) and (2) are a suggestion, not a route you owe anything to. **What is free and
must not be re-derived:** (BE-69)'s dense-or-empty dichotomy and its one-draw mechanism;
(BE-70)'s independence and product; (BE-72)'s `G` verdict on (CH-1)'s class; (BE-84)–(BE-86)'s
genuine-but-harmless coincidence with shortfall 0; (BE-89)–(BE-93)'s free flag base;
(BE-73)(ii)'s `δ_{uv}(H) = max(0, δ₁+δ₂−6)` and (BE-22)(vi)'s *one rigid side kills the
general-position half*.

**If you exhibit a shortfall, that is HIT shape 3 and it is large** — by (BE-71) a third
mechanism can only appear as a reach shortfall, and completeness of the mechanism list was
explicitly **never claimed**. Classify it: is it a *phenomenon* (a structural fact holding
identically on `Chart(H)`, which (BE-69)(3) says is what `Good = ∅` means) or an artifact of
the piece population? The former re-routes half (B); the latter is a cap finding.

### Job 2 (FORCED) — the standing inventory verdict, per-arc

The verdict is now two directions old and has paid five times: *the arc inventories landed
**conclusions** and mis-reads landed **hypotheses***, sharpened by WGROW to **per-arc**
(*grep the sibling workbook for the Lean file you are about to cite*) and paid again by
BBASE, which found `hcard` **does** transport to the pieces but does **not** cap `B_real`.
Run it against this section's own citations: which facts does §(K-bare-ext) cite **by the
role they played when first needed** rather than by their landed signature? One paragraph.

### Job 3 (FORCED, CHEAP) — what (BE-14) is left with, and the E-rider

**This one is not routine, because a HIT here is large.** If `reach` uniformity lands, half
(B) is **discharged** and (BE-14)'s only open half is the ear side, at the window **modulo
§(K-bare-ext)'s two window conditions**, plus cross-pair welding. State that precisely.
Then read E1/E2/E3 against their **actual** definitions (`notes/Pencil-fanout-archive.md`)
and **report, never fire**, with the 2026-09-02 correction in force:

> **"The target" in E1–E3 is the ARC's target — `PencilPair K 3 G`** — never a direction's
> local obligation. Two E3 texts exist (`:1700`'s two-conjunct, `:2098`'s one-conjunct
> deviation); say which you read. BBASE used `:1700`'s and confirmed WGROW's wrinkle that
> **E2's letter says *"the direction's target"*** while E3's says *"the target"*.

### What counts as a HIT — state which you got

1. **`reach` uniformity PROVED class-uniformly** — half (B) is discharged.
2. **Reduced** to a named checkable condition strictly smaller than (BE-67)(iii).
3. **A shortfall exhibited** — the third mechanism, classified phenomenon-vs-artifact.
4. **The per-arc inventory verdict** (job 2).
5. **What (BE-14) is left with + the E-rider reading** (job 3).

Either reading **corrected** is a reportable result in its own right — BBASE's landing is
the model, where all three corrections were the direction's most useful output.

### Bars

- **Do not re-open:** the flag **coincidence** — genuine, pointwise, shortfall `0` at
  392/392, a **checked hypothesis** ((BE-84)–(BE-86)); the **exhaustiveness obligation**
  ((BE-70), retired — and completeness of the mechanism list is **not** claimed, do not
  claim it); the **flag base** ((BE-89)–(BE-93), discharged — its two low-ranked successors,
  including cyclomatic `≥ 2`, are **not** this direction); `(1,1)` peels ((BE-79));
  the **SPREAD step** ((BE-74)); the **forced-empty `G` hunt** ((BE-72)); **(BE-32)(+)**;
  **(BE-41)(ii)**; **BWIN's window theorem**; **S-mark's pin**; the ear-decomposition
  induction ((BE-43)).
- **Not this direction, ranked separately:** **§(K-bare-ext)'s two window conditions**
  (qualify that token — it has three owners); **cross-pair welding** ((BE-28)(i)); the
  **one-end-series** case; BTWOCUT's bundle construction; the whole **W4** side, whose
  informal argument is closed.
- **The Lean hold (2026-08-05) binds**: no `.lean`, in any file, for any reason.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity of the escape, **(K-res)** (a USER
  call).

### Riders

**F11 — and it is the central rider here, because the target IS a uniformity claim.** Every
figure this section owns is a measurement on a constructed piece population: **28/28** peels
over 7 pieces ((BE-67)(i)), **24/24** (BRNODE), **16/16** first-draw-equals-maximum
((BE-69)(iii)), **392/392** shortfall-0 ((BE-86)), **42/42** MIX ((BE-70)). *"For every
internal R-node piece"* is an exhaustiveness claim over a class none of those populations
exhausts. **Name the piece populations and their caps**, and say what a new sweep adds over
them; a sweep reports *"none found under cap C"*. **Cap disclosure MANDATORY with the
DENOMINATOR named** — BBASE's *"three tiers that cannot exhibit a counterexample"* is the
standard to match, and it is the standard because it disclosed a cap that made its own
78 564/78 564 uninformative about the open case.

**F21 + `RESEARCH-ARC.md` §6.** The `(K-bare)` row was recomputed to **1 385 / 1 600** at the
BBASE landing (215 spare), so this landing has genuine room — but **recompute-to-a-target
still applies**, and label preservation is verified by **scripted set-diff, never by eye**
(BBASE's *93 codes in, 98 out, zero dropped* is the model, including its three
verified-benign inline-span drops). `notes/check-gapmap-cells.py` gates the cap, not the
labels.

**Harness.** `notes/scripts/README.md` first — §1 for the primitives (`bpeel.py`'s
`open`/reach instruments, `bdecor.py`'s chart layer, `bgenuine.py`'s certificate census,
`bbase.py`'s flag tower; do not reimplement any of them), §2 for layering, §4 for the
discipline. If you only **add** `w4/bunif.py`, the figure-invariance gate discharges by the
one-line `git diff --name-only -- '*.py' '*.m2'` / `git status --porcelain notes/scripts/`
check rather than a §3 re-baseline.

**F12** — the (BE-67)(iii) annotation this prep made is the model: a correction lands at the
**consumer that cites** the refuted claim, not only at the refuted claim itself. If your
work refutes or sharpens anything, sweep the citing statements too.

**F17 — four status surfaces**, all set to *in flight* by this prep: the fan-out header;
`notes/Phase39.md`'s `**Status:**` header **and** *Hand-off*; and **`ROADMAP.md`'s Status
row**.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BUNIF".) Labels
**(BE-94)–(BE-98)**, ***Steps BE93–BE97***, owning file `notes/Pencil-informal.md`
§(K-bare-ext) — **extends, no new section** — driver `w4/bunif.py`. The reservation opens at
the tail BBASE consumed to. **Return any unconsumed remainder.** **`BREACH` stays
rejected** — BGENUINE's prep already struck it on the (L5) substring rule (`breach` hits 5
files, and `reach` is itself this arc's live technical term, which is exactly the overlap
(L5) exists to catch) — and **`BCLASS` is rejected the same way** (`bclass` hits **21**,
`BCLASS` 7). `BUNIF` names the question (uniformity), **not a predicted answer**. Prefer
**prose names** for new configuration-level objects.

### Budget — measured at this prep

**`notes/Phase39.md` is at 576/580 lines, 502/525 status-header words** — the BBASE
follow-up bought the lines back by demoting BPEEL's *Decisions* entry, collapsing the
discharged ranked-list item 1, and merging the two W4 *Blockers* bullets. That is **4 lines**
of headroom, which is **not enough for a landing**: the landing MUST merge or rotate, and
the note's own rule names the candidates. The `(K-bare)` gap-map row at 1 385/1 600 is
comfortable by comparison.

### BUNIF — LANDING WRITE-UP (2026-09-02)

> **LANDED 2026-09-02 — HIT shape 2 (the reduction), plus jobs 2 and 3.** Verdict in
> `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE93–BE97*, labels **(BE-94)–(BE-98)**;
> driver `notes/scripts/w4/bunif.py` (five modes: `equiv`, `law`, `bind`, `coin`, `abst`).

**Job 1 (PRIMARY) — settled as a REDUCTION, not a proof and not a refutation.**

- **(BE-94) — the flag pair's stabilizer, and it acts on each side alone.** In the generic
  flag regime (`π_x ≠ π_y`, no cross-incidence) `S(ϕ) = Stab_{PGL₄}(p_x, π_x, p_y, π_y)`
  is `{diag(λ, A, μ) : A ∈ GL₂}/K^×`, **dimension 5** — which *recovers (BE-22)(v)(β)'s
  own count with the group named*, and, unlike a dimension count, **contains the maximal
  torus**. By (BE-70)(ii) each side's achievable family is `S(ϕ)`-invariant and the two
  sides move **independently**. The screw space splits `S(ϕ)`-canonically as
  `Π_x ⊕ ⟨M⟩ ⊕ ⟨L⟩ ⊕ Π_y` of dims `(2,1,1,2)`, and because the four blocks carry pairwise
  distinct torus characters the **`S(ϕ)`-stable subspaces are exactly the 16 sums**. That
  is what makes `c_i(U) := dim(ρ̄_i ∩ U)` an invariant of the *family*, not of a member.
- **(BE-95) — the cap, and (BE-71)'s mechanisms are instances.** The modular law bounds
  `dim(ρ̄₁+ρ̄₂)` by `min_U [ρ₁+ρ₂ − max(0, c₁(U)+c₂(U) − dim U)]`. `core_i` is
  `S(ϕ)`-stable, so **two-sided (P) is the `U = core₁∩core₂` term** and **two-sided (Z) is
  the `U = Π_x⊕Π_y` term**; (BE-71)(iii)'s Klein-ruling candidate is inside (Z).
- **(BE-96) — the law, and it is the direction's result.** Degenerating each side along a
  1-PS of `S(ϕ)` (lower semicontinuity of `dim(V+W)` makes the limit a valid lower bound;
  the `GL₂` factor commutes with the central torus and separates two lines inside a
  2-dimensional block) gives a **matching lower bound** over the **8** realizable block
  orderings. Where the two meet, `reach` is a **theorem** in the two per-side profiles:
  **121/122** measured peel rows and **393/400** abstract pairs, with the cap **ATTAINED
  by a group move at 400/400**. Hence the reduction: **(BE-67)(iii) at a peel ⟺ 14
  inequalities in per-side data**, `⟹` a theorem (the modular law: a violation *is* a
  shortfall), `⟸` the law.
- **(BE-97) — where it can break, and the one place it is tight.** The arithmetic triage
  leaves **14 of 16** blocks live (and refuses the tempting *"`Π_x` can never bite"*,
  which needs (BE-38)(iii)'s **measured** third clause). Measured over 92 rows the
  violation margin is **`0` at 92/92** — never positive, so **no shortfall**, and never
  negative either: **saturated at every measured peel**. `Π_x` is the **only** block at
  which BOTH sides exceed the generic profile (12/92), where they sit at `c₁ = c₂ = 1`,
  which is (BE-45)'s **(M1)/(M2)** dichotomy firing at **both ends of one peel**. Named
  residue: **(NO-DOUBLE-PENCIL)** — *no internal R-node peel has one side with
  `dim(ρ̄_i ∩ Π_x) = 2` and the other with `dim(ρ̄_j ∩ Π_x) ≥ 1`* — whose two clauses are
  already priced, by (BE-44)(ii) and (BE-45) respectively.
- **NOT a shortfall (HIT shape 3 does not fire).** Nothing here exhibits one; what the
  direction adds to (BE-71) is an **index set** for third mechanisms, not a witness.

**The two coordinator readings, both TESTED.** `RESEARCH-ARC.md` §7's tally gains a ninth
instance: **reading (1) is REFUTED AS STATED** — *"the class statement is now entirely the
general-position half"* is wrong as a **decomposition**, because (BE-96)(iv) shows the
welded half is not a separate half at all but the `U = Λ²K⁴` term of one inequality
family; its cited evidence (30/30, 392/392) is untouched, and what fails is the
two-halves framing it inherited from (BE-67)(iii). **Reading (2) is CONFIRMED IN SHAPE and
CORRECTED IN ITS EXPECTED FAILURE POINT** — (BE-70) does make `reach` a function of the
flag pair and that *is* the shape of a class argument, but the operative object is the
flag pair's **stabilizer**, not the base BBASE freed; and `G` is **not** inherited as a
hypothesis (it is carried exactly as (BE-64)(ii)/(BE-70)(ii) carry it), so the statement
quantifies over **internal R-node pieces**, not over the proviso's class.

**Job 2 — the per-arc inventory verdict FIRES, on this section's own citation.**
§(K-bare-ext) cites **(BE-38)(iii)'s third clause** (*"never `2` below `ρ₁ = 6`"*) by the
role it played when first needed — a summary of a table — and (BE-45)(iii) records it as
**standing**; its landed signature is a **measurement over 37 pieces**. Reading it as a
law produced this direction's own first draft of (BE-97)(i), and the arithmetic
enumeration **refused** it. Stress-tested rather than only flagged: over 112 rows, **4**
sides reach `c_i(Π) = 2` and **0** have `ρ_i < 6`, so the clause survives under this cap
with a second population behind it — still a measurement. The section's other borrowings
**are** cited by signature ((BE-69)(iii)'s `A_i ≠ ∅` as the induction's own hypothesis,
(BE-70)(ii) *with* its `G`, (BE-65)(ii) with (CH-1)'s three hypotheses named).

**Job 3 — what (BE-14) is left with, stated precisely, and the E-rider.** A HIT here would
have **discharged half (B)**; this one **reduces** it instead, so half (B) still stands —
as the single per-side condition (NO-DOUBLE-PENCIL). **If** it lands, (BE-14)'s open half
is exactly: **(1)** the ear case's (β) side, at the window, **modulo §(K-bare-ext) *Step
BE56* / (BE-57)(iv)'s own two conditions** — **(S1)** *some `δ₁`-attaining middle has
`p_{w₁} ≠ p_{w₂}`* and **(S2)** *no middle forces a boundary-flag relation other than
equality of the planes* — both vacuous at every drawn piece and **neither a theorem**,
with a per-shape residue outside the window; and **(2)** cross-pair welding ((BE-28)(i)).
*(The token "window conditions" has three owners — these; §(SAFE-RES′)'s (S1)–(S5), which
disambiguates itself inline; the §(K-slide) (W1)–(W4) family — so it is qualified.)*
**E1/E2/E3 read against `notes/Pencil-fanout-archive.md`, REPORTED AND NOT FIRED**, with
the 2026-09-02 correction in force (*"the target" is the ARC's, `PencilPair K 3 G`*): the
reading is **`:1700`'s two-conjunct E3**, with `:2098`'s one-conjunct deviation noted and
not used, and E2's letter (*"the direction's target"*, `:1697`) confirmed to differ from
E3's (*"the target"*, `:1700`). **E1** — no colourings, no g-flank. **E2** — the arc's
target is neither refuted nor unprovable-as-posed, and this landing **names** a
dispatchable attack. **E3** — the arc's target is not proven, and (NO-DOUBLE-PENCIL) is
dispatchable rather than gated; it does not fire under `:2098`'s text either.

**F11 — the central rider, honoured with denominators.** Every figure is a measurement on
a **constructed** population and *"for every internal R-node piece"* exhausts none:
**population A** = BDECOR's 7 R-node pieces + BPEEL's nested one, 3 draws, **32** rows —
*the same pieces behind (BE-67)(i)'s 28/28 and (BE-69)(iii)'s 16/16, so not independent
evidence*; **population B** = `bpeel.constructed_tier(maxlen=3, nsamp=60)` filtered by
BPEEL's own **disclosed stand-in** `rnode_shaped`, **90** rows, a construction (K4
exhaustive at lengths `1..3` + 60 seeds), not a census; **92** rows for `bind`; **400**
random subspace pairs for `abst` (not achievable ones, 60 group draws each); **60**
constructed coincident ear pairs for `coin`. What a new sweep adds over 24/24, 28/28 and
16/16 is **population B** — the first R-node-peel population in this sub-arc that is *not*
the R-battery — plus the index set, which lets a future sweep report *where* rather than
only *whether*. The one non-sweep claim is (BE-96)(iv)'s `⟹`, which is the modular law.

**F12** paid at source: forward pointers added at **(BE-67)(iii)**, **(BE-68)(ii) item 2**
and **(BE-71)(ii)** (whose *"not proved and not claimed"* is now answered in the generic
regime). **F21**: the `(K-bare)` gap-map row **recomputed to a target** — 1 385 → **1 472
/ 1 600** words (128 spare), with label preservation verified by a **scripted set-diff**:
**101 labels in, 112 out, ZERO dropped**. **Harness**: `bunif.py` is an **addition only**,
so the figure-invariance gate discharges by `git diff --name-only -- '*.py' '*.m2'` /
`git status --porcelain notes/scripts/`; no tracked driver was edited.

**Reservation CONSUMED IN FULL, nothing returned.** Labels **(BE-94)–(BE-98)**, *Steps
BE93–BE97*, owning file §(K-bare-ext) (extended, no new section), driver `w4/bunif.py` at
the reserved path. One new configuration-level object is named, in prose per the
reservation's preference: the **block profile** `c_i(U)`, and the condition
**(NO-DOUBLE-PENCIL)**.

**The successor this direction names, ranked.** **(1)** (NO-DOUBLE-PENCIL) — attack it by
seeking the two clauses **together**: a side all of whose `x–y` paths span 6
((BE-44)(ii)) glued to a **series end** ((BE-45)(i)). Cheap individually, never sought
jointly. **(2)** the `U = ⟨M⟩` block — both sides' `ρ̄_i` containing the virtual edge's own
line — unwitnessed, and `xy ∉ E(H)` removes the obvious source. **(3)** the coincident
regime, where only the cap survives; the forced family there is BGENUINE's 392.

## BDOUBLE — sixty-fourth ordinal (single dispatch, prepped 2026-09-02) — the one place the law is tight

**Selection provenance: BUNIF's own named successor, and it is the only tight place the
measurement found.** BUNIF turned (BE-67)(iii) into **14 per-side inequalities**
`c₁(U) + c₂(U) ≤ dim U + max(0, δ₁+δ₂−6)` against the 16 `S(ϕ)`-stable subspaces, proved
both bounds of the sandwich, and measured the violation margin at **`0` at 92/92** — never
positive, never negative. The **only** block where both sides exceed the generic profile is
`Π_x` (12/92, tight at 8), leaving **(NO-DOUBLE-PENCIL)**. W4's non-user-call list is empty;
the **(K-res) wave** and the **2026-08-05 Lean hold** were both offered to the user on
2026-09-02 and both **declined in favour of continuing research**.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this session).

### The target, stated exactly

> **(NO-DOUBLE-PENCIL) ((BE-97)(iii)).** At no internal R-node peel does one side have
> `dim(ρ̄_i ∩ Π_x) = 2` while the other has `dim(ρ̄_j ∩ Π_x) ≥ 1` — and the same at `Π_y`.

Its two clauses are **already priced by landed results**: the first by **(BE-44)(ii)**
(`c_i(Π_x) = 2` forces **every** `x–y` path of side `i` to span 6, hence
`dist_i(x, y) ≥ 6`), the second by **(BE-45)** (a **series end** at `x`, or **path
saturation** `δ_i = d_min`). *"Neither clause has been shown incompatible with the other,
and that — not a search over configurations — is what half (B) now needs."*

### WHAT A HIT HERE DOES AND DOES NOT DO — read this before scoping

**It does not discharge half (B), and the summary surfaces have been corrected to say so.**
(BE-97)(iv) is explicit and it is this direction's honest frame: *"`Π_x` only" is a
statement about 92 rows of two constructed populations, **not** a theorem. The other 13 live
blocks are unwitnessed rather than excluded.* So proving (NO-DOUBLE-PENCIL) closes the
**measured** tight place. Half (B)'s class statement additionally needs the other blocks —
(BE-97)(iv) even names the shape that would put a second one in play at once
(`c_i(⟨M⟩) = 1` on **both** sides: both relative screw spaces containing the virtual edge's
own line `p_x ∨ p_y`). **Job 3 must state the residual in those terms**, and must not report
half (B) as discharged on a (NO-DOUBLE-PENCIL) HIT.

### THE COORDINATOR'S TWO READINGS — labelled TO BE TESTED, both derived from the landed law

`RESEARCH-ARC.md` §7 binds; its tally is **eight instances and seven kinds**, and the last
two preps had **five of six** readings refuted, corrected or ruled inapplicable. Treat both
below as arithmetic to re-derive, not as a route.

**(1) THE OBLIGATION IS THE INEQUALITY, AND IT IS STRICTLY WEAKER THAN (NO-DOUBLE-PENCIL).**
What half (B) needs at `Π_x` is *no violation*: `c₁ + c₂ ≤ 2 + max(0, δ₁+δ₂−6)`. Since
`c_i ≤ dim Π_x = 2`, `c₁ + c₂ ≥ 3` forces one side to `2` and the other to `≥ 1` — so
**(NO-DOUBLE-PENCIL) ⟺ `c₁ + c₂ ≤ 2`**, which is the inequality **only when
`δ₁ + δ₂ ≤ 6`**. Above that threshold the inequality has slack `(NO-DOUBLE-PENCIL)` does
not use. **Consequence to test:** the named condition may be **stronger than necessary**, and
a counterexample to it need not be a shortfall — so an exhibited double pencil is *not*
automatically a refutation of half (B). Say which you have.

**(2) AND THE FIRST CLAUSE MAY BUY THE SLACK ITSELF — the reading the coordinator would
most like tested, with its weak link named.** By (BE-44)(ii), `c₁(Π_x) = 2` forces
`dist₁(x, y) ≥ 6`. **If** that gives `δ₁ = 6` — the step this reading rests on, and the one
the coordinator cannot verify (the `δ = min(L, 6)` identity is stated at a **path** side,
(BE-79)/(BE-80), not in general) — then `max(0, δ₁+δ₂−6) = δ₂`, and a violation at `Π_x`
needs `2 + c₂ > 2 + δ₂`, i.e.

> **`c₂ > δ₂`, hence `a₂ ≥ 1`, since `c₂ ≤ ρ₂ = δ₂ + a₂`.**

That is: **under `δ₁ = 6`, a `Π_x` violation requires side 2 to be NON-ATTAINING.** If the
class statement is asked at peels where both sides attain — which is what `A_i ≠ ∅` supplies
and what (BE-22)(iii)'s `a = 0` case is about — the `Π_x` block would then be **free**, and
(NO-DOUBLE-PENCIL) would be provable rather than merely unrefuted. **Where the coordinator
expects to be wrong:** the `dist ≥ 6 ⟹ δ = 6` step; `δ_i` is the side's own deficiency-like
quantity and the identity may not survive off a path side. **Check that step first** — if it
fails, reading (2) fails with it and the direction is back to the joint search.

### Job 1 (PRIMARY, FORCED) — settle (NO-DOUBLE-PENCIL), or the inequality it stands in for

Prove it, exhibit a double pencil, or reduce it. **The attack BUNIF named** is to seek the
two clauses **together** — a side whose every `x–y` path spans 6 ((BE-44)(ii)) glued to a
series end or path-saturated side ((BE-45)) — which is cheap on each clause separately and
**has never been sought jointly**. Readings (1)/(2) suggest the joint search may be
unnecessary; **test them before spending the search**, and if either holds, say what it
leaves.

**On an exhibited double pencil, classify before pricing** (reading (1)): is it a
**violation of the inequality** — a genuine shortfall, which would be the third mechanism
(BE-71) says is the only remaining shape and a large result — or merely a double pencil at
`δ₁+δ₂ ≥ 7`, where the inequality has slack and half (B) survives? The two have completely
different consequences.

### Job 2 (FORCED) — the standing per-arc inventory verdict

It has now paid at six directions running and BUNIF's own instance is the model to beat: it
found that its first draft of (BE-97)(i) rested on **(BE-38)(iii)'s *measured* third
clause** rather than a theorem, and the arithmetic enumeration refused the draft. Run the
check on this direction's own load-bearing citations — **(BE-44)(ii)** and **(BE-45)**
especially, since the whole target is stated in terms of them: are they theorems, or
measured clauses over a named population? Read the statements, not the summaries. One
paragraph.

### Job 3 (FORCED, CHEAP) — the honest residual, and the E-rider

State what half (B) is left with, **in (BE-97)(iv)'s terms** — a HIT here closes the
measured tight place and leaves the other 13 blocks unwitnessed-not-excluded, with the
`⟨M⟩`-on-both-sides shape named as the one that would put a second block in play. Then read
E1/E2/E3 against their **actual** definitions and **report, never fire**, with the
2026-09-02 correction in force:

> **"The target" in E1–E3 is the ARC's target — `PencilPair K 3 G`** — never a direction's
> local obligation. Two E3 texts exist (`:1700`'s two-conjunct, `:2098`'s one-conjunct
> deviation); say which you read. BBASE and BUNIF both used `:1700`'s.

### What counts as a HIT — state which you got

1. **(NO-DOUBLE-PENCIL) PROVED**, or the weaker `Π_x` inequality proved (reading (1)) —
   say which, they are not the same.
2. **A double pencil exhibited**, classified violation-vs-slack per job 1.
3. **Reduced** to a named condition strictly smaller than (NO-DOUBLE-PENCIL).
4. **The per-arc inventory verdict** on (BE-44)(ii)/(BE-45) (job 2).
5. **The honest residual + the E-rider** (job 3).

Either reading **corrected** is a reportable result; BBASE's three-for-three and BUNIF's
two-for-two are the precedent, and reading (2)'s named weak link is where to look first.

### Bars

- **Do not re-open:** the **law itself** ((BE-94)–(BE-96)) — the stabilizer, the block
  splitting, the cap, the degeneration bound, and the `121/122` / `393/400` meeting
  disclosure, all landed; the **flag coincidence** (checked hypothesis, `0` shortfall at
  392/392); the **flag base** ((BE-89)–(BE-93), discharged; its cyclomatic-`≥ 2` successor
  is **not** this direction); the **exhaustiveness obligation** ((BE-70)); `(1,1)` peels
  ((BE-79)); the **SPREAD step** ((BE-74)); the **forced-empty `G` hunt** ((BE-72));
  **(BE-32)(+)**; **(BE-41)(ii)**; **BWIN's window theorem**; **S-mark's pin**.
- **Do not re-derive** BUNIF's `(BE-96)(ii)` exception (`K4(2,3,3,3,3,3)` at peel `(A,B)`,
  where the degeneration bound is not sharp and the row is settled by measurement) — it is
  disclosed and it is not this direction's job to close it.
- **Not this direction, ranked separately:** §(K-bare-ext)'s two window conditions (qualify
  that token — three owners); **cross-pair welding** ((BE-28)(i)); the **one-end-series**
  case; BTWOCUT's bundle construction; the **W4** side, closed.
- **The Lean hold (2026-08-05) binds**: no `.lean`, in any file, for any reason.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity of the escape, **(K-res)** (a USER
  call).

### Riders

**F11 — and the target is again a universal claim.** *"At no internal R-node peel"* needs an
argument or an enumeration that enumerates; the `12/92` and `8` tight rows are measurements
on two constructed populations. **Name the populations and their caps**, and — this is the
specific trap here — **do not let `Π_x` only** travel without (BE-97)(iv)'s scope, which is
the correction this prep made to three summary surfaces after the landing stated the caveat
only in the workbook. **Cap disclosure MANDATORY with the DENOMINATOR named.**

**F12** — if you correct (BE-44)(ii)'s or (BE-45)'s reading, edit **at those statements**,
not only in the write-up; and if reading (2)'s `δ = 6` step turns out false, annotate
wherever the `δ = min(L, 6)` identity is quoted outside a path side.

**F21 + `RESEARCH-ARC.md` §6.** The `(K-bare)` row is at **1 472 / 1 600** after BUNIF's
recompute — **128 spare, the tightest it has been in three landings**, so a recompute to a
target is required rather than optional, with label preservation by **scripted set-diff**
(BUNIF's *101 in / 112 out / zero dropped* is the standard).

**Harness.** `notes/scripts/README.md` first — §1 for the primitives (`bunif.py`'s block
decomposition, profile and margin instruments; `bpeel.py`'s reach layer; `bgenuine.py`'s
census; do not reimplement any). A new driver is `w4/bdouble.py`; if you only **add** it the
figure gate discharges by the one-line check.

**F17 — four status surfaces**, all set to *in flight* by this prep.

**`RESEARCH-ARC.md` §7** — readings (1) and (2) are hypotheses with their evidence stratum
named, and (2)'s weak link is named inside it. Kill either without ceremony.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BDOUBLE".) Labels
**(BE-99)–(BE-103)**, ***Steps BE98–BE102***, owning file `notes/Pencil-informal.md`
§(K-bare-ext) — **extends, no new section** — driver `w4/bdouble.py`. Opens exactly at the
tail **BUNIF declared**. **Return any unconsumed remainder.** **Do not mint a label for
`Π_x`, `c_i(U)`, `margin`, `blockcap`/`blockdeg` or the double pencil itself** — all are
existing prose/symbol names from BUNIF's landing. `BTIGHT` and `BPENCIL` were checked
(both 0-hit) and **not chosen**: `BTIGHT` names a *measured* property rather than the
question, and `BPENCIL` collides conceptually with the phase's own subject. **`BDOUBLE`
names the condition, not a predicted answer.**

### Budget — measured at this prep

**`notes/Phase39.md` is at 578/580 lines, 485/525 status-header words.** The BUNIF landing
left it **saturated at 580/580**, and the follow-up bought the room back by relocating the
**W4 per-landing detail** as `notes/Pencil-structure.md` **block 9** — the same disposition
block 8 got, and available because W4's informal argument is closed. The prep has spent most
of that again on the in-flight lines plus (BE-97)(iv)'s scope caveat at two surfaces. **The
landing MUST relocate or merge, not append**, and the note's own rule names the candidates.

### LANDING WRITE-UP — BDOUBLE, 2026-09-02: **(NO-DOUBLE-PENCIL) is REFUTED by (BE-45)(ii)'s own vacuous corner, and the tight block is REDUNDANT — `Π_x` and `Π_y` drop out of the fourteen**

> **LANDED 2026-09-02 — HIT shapes 2 AND 3, plus jobs 2 and 3.** Verdict in
> `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE98–BE102*, labels
> **(BE-99)–(BE-103)**; driver `notes/scripts/w4/bdouble.py` (four modes: `arith`,
> `witness`, `hunt`, `price`).

**Job 1 (PRIMARY) — the condition is FALSE, and the double pencil is SLACK.**

- **(BE-99) — one landed lemma produces BOTH clauses.** (BE-45)(ii) (M2, path
  saturation) at its own **explicitly-flagged vacuous corner** `d_min = 6` gives
  `ρ̄_i = ⟨P⟩` of dimension 6, i.e. **`ρ̄_i = Λ²K⁴`**, so `c_i(U) = dim U` at *every*
  stable `U` — in particular `c_i(Π_x) = c_i(Π_y) = 2`, the block cap. (BE-45)(i)/(ii)
  at the other side gives `c_j(Π_x) ≥ 1`. That is exactly the `(2, ≥1)` pair
  (NO-DOUBLE-PENCIL) forbids, and **both hypotheses hold at a row already inside
  BUNIF's own 92**: `K4 + th(6,6,6)/ab + ear4/ua` at peel `(a,b)` — side 2 the
  `θ(6,6,6)` (`d_min = 6`, `δ₂ = ρ₂ = 6`, `ρ̄₂ = Λ²K⁴` asserted **as a space**), side 1
  the `{a–v–b, a–e1₄…u–b}` side (`d_min = δ₁ = ρ₁ = 2`, `c₁ = 1`). **2 of 92 rows, at
  BOTH 2-blocks**, 6 of 6 independent seeds. BUNIF's *"never sought jointly"* attack is
  answered — the two clauses are not merely compatible, one lemma gives both.
- **Why BUNIF's census did not see it, and no landed measurement changes.** (BE-97)(iii)
  counts blocks where **both sides exceed the generic profile**. A side at `ρ_i = 6` has
  `c_i(Π_x) = 2` *generically*, so it never registers as exceeding, and the pair `(1,2)`
  is invisible to that statistic. The census is correct as written; the **named
  condition** is what was wrong — a candidate-side reading correction of the (BE-45)(iii)
  / (BE-36) shape.
- **(BE-100) — CLASSIFIED, per job 1's own instruction: SLACK, not a violation.** At a
  vacuous-corner peel `δ_i = 6`, so `slack = δ_j` and
  `c_i + c_j ≤ 2 + ρ_j = 2 + δ_j + a_j` — the obligation holds whenever side `j`
  attains. At the witness `δ₁+δ₂ = 8`, slack `2`, **margin `−1`** at both blocks, and
  `dim(ρ̄₁+ρ̄₂) = 6 = min(δ₁+δ₂,6)+a₁+a₂`: **the peel ATTAINS. Half (B) is untouched by
  the refutation.** This is *not* (BE-71)'s third mechanism.
- **(BE-101) — THE REDUNDANCY THEOREM, and it is the direction's result.** Name the
  per-side clause **(PENCIL-SATURATES)**: *`c_i(Π) = 2 ⟹ ρ_i = 6`* — **(BE-38)(iii)'s
  third clause** contrapositively. **Theorem:** given it, a violation at `U = Π_x` **is**
  a violation at `U = Λ²K⁴`. *(A `Π_x` failure forces some `c_i(Π_x) = 2` and the other
  `c_j(Π_x) > slack`; then `ρ_i = 6` and `ρ_j ≥ c_j > slack`, so `ρ₁+ρ₂ > 6 + slack`.)*
  Verified exhaustively — **300/300 caught, 0 escaping**, with an **F13 negative control**
  at **313** escapes when the clause is dropped. **Corollary:** at `a₁ = a₂ = 0` the
  `Λ²K⁴` inequality reads `a₁+a₂ ≤ max(0, 6−δ₁−δ₂)`, automatic — so `Π_x` and `Π_y` are
  **FREE** and the live block list drops **14 → 12**. The measured tight place is closed.

**The two coordinator readings, both TESTED.** `RESEARCH-ARC.md` §7's tally gains a tenth
instance. **Reading (1) is CONFIRMED** and immediately load-bearing: (NO-DOUBLE-PENCIL) ⟺
`c₁+c₂ ≤ 2`, the obligation only at `δ₁+δ₂ ≤ 6` (**28 of 49** `(δ₁,δ₂)` pairs asserted
both ways), so the condition is **strictly stronger** than half (B) needs — **320 of 1 975**
conceivable double pencils are not violations — and the exhibited pencil sits in exactly
that gap. **Reading (2) is REFUTED at the weak link the prep named** and its **conclusion
recovered by a different route**: `dist_i ≥ 6 ⟹ δ_i = 6` is false because (BE-30) bounds
`ρ` by `dist` from **above** — a large `dist` removes a constraint, it never supplies one —
asserted as `ρ_i ≤ min(dist_i, 6)` at **184/184** sides and refuted outright at **2**
(`K4(1,3,3,3,3,2)` and `K4(1,3,3,3,3,3)` at peel `(C,D)`: `dist = 6`, `ρ = δ = 1`); the
landed corpus already carried the shape at (BE-44)(iii). What reading (2) wanted comes
instead from **(PENCIL-SATURATES)**, which gives `ρ_i = 6` with no mention of `dist`, and
then (BE-101) supersedes the reading by killing the block outright.

**Job 2 — the per-arc inventory verdict FIRES on BOTH of the target's citations.** Read at
the statements, not the summaries. **(BE-44)(ii)** is proved in the `dim⟨P⟩ = 6` direction
only; its **converse** (`≤ 5 ⟹ the intersection is the first line`) is the open condition
**(BE-46)** discharges **per shape from one witness**, and (BE-46)(iv) says plainly that
the class-level statement is **not** discharged — yet the price (BE-97)(i) quotes,
*`c_i(Π_x) = 2` forces every path to span 6*, is exactly that converse's contrapositive.
**(BE-45)** has (i) and (ii) proved **forward**, while the **converse** (BE-45)(iv) is
*proved at 8 of 11 and measured at 3* — and the target's second clause reads (BE-45) as
**characterizing** `c_j(Π_x) ≥ 1`, i.e. the converse. **Both citations are used in their
non-theorem direction**, the second consecutive direction on which a *"priced by"* phrase
outran its own statement (BUNIF's was (BE-38)(iii)). The **refutation is unaffected** — it
uses only the proved halves — but the **residual's standing changes**: (PENCIL-SATURATES)
is *not* implied by (BE-44)(ii), since `dist_i ≥ 6` yields no lower bound on `ρ_i`, so the
clause rests on (BE-38)(iii)'s measurement alone.

**Job 3 — the honest residual, in (BE-97)(iv)'s terms, and half (B) is NOT discharged.**
What closes is the **measured** tight place. What remains: **(1)** **(PENCIL-SATURATES)**
itself — per-side, one quantifier, no pairing; measured at **37** pieces ((BE-38)(iii))
plus **4 sides of 92** here (0 with `ρ_i < 6`), a small denominator; **(2)** the **other 12
live blocks**, **unwitnessed rather than excluded**, with (BE-97)(iv)'s own named shape —
`c_i(⟨M⟩) = 1` on **both** sides — still the right hunt; **(3)** the **non-attaining case**,
where `U = Λ²K⁴` is a real constraint `a₁+a₂ ≤ max(0, 6−δ₁−δ₂)` and, by (BE-101)(iii), a
**live** block; **(4)** unchanged, the ear case's (β) side at the window modulo *Step BE56*
/ (BE-57)(iv)'s **(S1)**/**(S2)**, and **cross-pair welding** ((BE-28)(i)).
**E1/E2/E3 read against `notes/Pencil-fanout-archive.md`, REPORTED AND NOT FIRED**, with
the 2026-09-02 correction in force (*"the target" is the ARC's, `PencilPair K 3 G`*): the
reading is **`:1700`'s two-conjunct E3**, `:2098`'s one-conjunct deviation noted and not
used. **E1** — no colourings, no `D`, no g-flank. **E2** — *does not fire*, and the
distinction matters here: what is refuted is **(NO-DOUBLE-PENCIL)**, a direction's local
obligation, **not** the arc's target; and this landing names a dispatchable attack.
**E3** — the arc's target is not proven and (PENCIL-SATURATES) is dispatchable, not gated.

**F11 — the rider, and the target was again a universal claim.** *"At no internal R-node
peel"* is a `∀` no sweep exhausts — but this direction did not need to exhaust it, because
the answer is **negative** and one witness settles a `∀`. The sweeps are **BUNIF's own two
constructed populations, with no new one added**: **A** = BDECOR's 7 R-node pieces +
BPEEL's nested one; **B** = `bpeel.constructed_tier(maxlen=3, nsamp=60)` behind BPEEL's
disclosed stand-in `rnode_shaped`; **92** rows for `hunt`, **184** sides for `price`. Every
*"none found"* — including (PENCIL-SATURATES)'s **0 of 4** — reads *none found under those
caps*, and the `4` is the same small denominator (BE-98)(ii) disclosed, on an **overlapping**
population, so it is **not** independent confirmation. The non-sweep claims are (BE-99)(i)/(ii)
((BE-45)'s identities), (BE-100) and (BE-101) (exhaustive enumerations plus one proof), and
(BE-102)(i)'s `ρ ≤ min(dist,6)` (from (BE-30)).

**F12 paid at source — four hunks**, at the statements and not only in the write-up:
**(BE-97)(iii)** (the condition is REFUTED, with its measurements explicitly untouched),
**(BE-97)(i)** (its enumeration's `a = 0` denominator, and that its "structural price" is
weaker than it reads), **(BE-45)(ii)** (its vacuous corner is what refutes (BE-97)(iii)),
and **(BE-80)(iv)** (the `δ = min(L,6)` identity annotated **PATH-SIDE ONLY**, the prep's
explicit instruction).

**F21 — the `(K-bare)` row recomputed to a target; the cap bump was WITHDRAWN.**
1 472 → **1 546** words while absorbing a full direction and five labels — ~110 words of
pre-existing prose compressed away against ~186 added — with label preservation by a
**scripted set-diff: 129 codes in, 144 out, ZERO dropped**. The recompute stands. The
direction also added a `SPECIAL_CAPS` entry at 1 630 / 150, on the ground that 54 words of
headroom is §6's *pointless recompute* case; the **coordinator withdrew it** the same day,
because the row is **compliant at 1 546 under the generic 1 600** and every other entry in
that table was added for a row that had *exceeded* its cap and carried a density argument.
No overflow, no bump — the full reason is in the gate's own docstring. **Harness**: `bdouble.py` is an
**addition only**, so the figure-invariance gate discharges by the one-line check; no
tracked driver was edited. Twenty-first `kbare/` consumer, chain **nineteen** deep, and the
**first external consumer of any `bunif` device** (recorded below the rule-2 threshold).

**Reservation CONSUMED IN FULL, nothing returned.** Labels **(BE-99)–(BE-103)**, *Steps
BE98–BE102*, owning file §(K-bare-ext) (extended, no new section), driver `w4/bdouble.py`
at the reserved path. **Nothing minted** for `Π_x`, `c_i(U)`, `margin`, `blockcap`/
`blockdeg` or the double pencil itself, per the reservation's constraint. One new
configuration-level object is named in prose: **(PENCIL-SATURATES)**. Next tail declared:
**(BE-104) / *Step BE103***.

**The successor this direction names, ranked.** **(1)** **(PENCIL-SATURATES)** — attack it
where (BE-44)(ii)'s **per-shape** half is doing the work: a side whose every `x–y` path
spans `≤ 5` yet whose `ρ̄_i` still contains `Π_x`. Cheapest falsification of this landing,
and (BE-46)(iv) already says the class-level statement is undischarged. **(2)** the
`U = ⟨M⟩` block, (BE-97)(iv)'s own named shape, still unwitnessed. **(3)** the
**non-attaining** case, where `U = Λ²K⁴` becomes a live block ((BE-101)(iii)) — and by the
redundancy theorem it is where a `Π_x` failure would surface first anyway.

## BSATUR — sixty-fifth ordinal (single dispatch, prepped 2026-09-02, **LANDED 2026-09-02**) — the clause the redundancy theorem rests on

**Selection provenance: BDOUBLE's own ranked successor, and job 2's find is what makes it
urgent.** BDOUBLE refuted (NO-DOUBLE-PENCIL) harmlessly and replaced it with something
better — the **redundancy theorem** ((BE-101)): *under* **(PENCIL-SATURATES)** a `Π_x`
violation **is** a `U = Λ²K⁴` violation, so at `a₁ = a₂ = 0` both 2-blocks are free and the
live block list drops **14 → 12**. But its own job 2 established that **(PENCIL-SATURATES)
is not implied by (BE-44)(ii)** and *"rests on (BE-38)(iii)'s measurement alone"*. So the
best result the (BE-14) thread now owns is **conditional on a measured clause**, and this
direction is about that clause.

**Diversification, stated rather than hidden — this is the fourth consecutive (BE-14)-side
direction** (BBASE, BUNIF, BDOUBLE, BSATUR), the same shape the W4 run had. It is taken
because (BE-14) is carried item **#1** by distance to the phase target and half (B) is
close; the mitigation is built into the spec as **job 2**, which is the falsification lane
(the `⟨M⟩` hunt) rather than a promise to alternate later. The **(K-res) wave** and the
**2026-08-05 Lean hold** were offered to the user on 2026-09-02 and both **declined in
favour of continuing research**.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this session).

### The target, stated exactly

> **(PENCIL-SATURATES).** For a side of an internal R-node peel,
> `dim(ρ̄_i ∩ Π) = 2 ⟹ ρ_i = 6` — at `Π = Π_x` and at `Π = Π_y`.

Equivalently: `Π ⊆ ρ̄_i` forces the side's relative screw space to be **all** of `Λ²K⁴`.
It is **(BE-38)(iii)'s third clause**, *"never `2` below `ρ₁ = 6`"*, asserted in that
block's driver over **24 pieces × 14 draws** (and re-measured by BDOUBLE at 37 pieces +
4 sides of 92 — *a small denominator*, its own words). Prove it, refute it, or reduce it.

### THE THING TO CHECK FIRST — its own sentence's MIDDLE clause is already FALSE

**(BE-38)(iii) states three clauses in one sentence, and the middle one was refuted.**
*"The intersection is `1` for path-like sides, `0` wherever two `u–v` paths leave `u` by
different edges, and never `2` below `ρ₁ = 6`."* The **middle** clause — `0` at distinct
first edges — is **FALSE**, corrected 2026-08-28 by **(BE-45)(iii)** (direction BSHARP):
six rows have three distinct first edges and intersection `1`, by path saturation, so
*"distinct first edges are **necessary, not sufficient**"*. The block's own correction note
then asserts *"the first and third clauses stand"* — **which is itself a summary sentence,
of exactly the kind the middle clause turned out to be** (the note even says so: *"this was
a summary sentence outrunning its own table, the same shape as (BE-36)"*).

So the first question is not *"is (PENCIL-SATURATES) true?"* but **"does the third clause
survive the scrutiny the middle one failed?"** The middle clause failed by an
over-read — a *sufficient* condition reported as a *characterization*. Ask whether the
third clause is an over-read of the same kind: the table shows `2` occurring at the `ρ₁ = 6`
rows, which establishes `ρ₁ = 6 ⟹` (nothing), and the clause asserts the **converse
direction**. That is the same converse/contrapositive slip job 2 caught in (BE-44)(ii) one
landing ago.

**What is genuinely in its favour, and should be weighed rather than dismissed:** the
driver **asserts** the clause rather than reporting it — *"a `Π_u ⊆ ρ̄₁` at a non-vacuous
piece would be the (P) trap genuinely realized and would stop the run"* — so the 24 × 14
run is a real assertion, not a silent pass, and BDOUBLE's own 37 pieces + 4 sides add to
it. The clause is *measured*, not merely *believed*; what it lacks is an argument and a
population that exhausts anything.

### THE COORDINATOR'S ONE READING — labelled TO BE TESTED

`RESEARCH-ARC.md` §7 binds; the tally is **nine instances and seven kinds**, and across the
last three preps **six of eight** readings were refuted, corrected or ruled inapplicable —
including one (BDOUBLE's reading (2)) that died at exactly the weak link its own prep named.
Only one reading is offered here, because the coordinator has only one that is checkable.

**(PENCIL-SATURATES) MAY BE (BE-33)'s (P) TRAP, READ AS A VACUITY STATEMENT.**
(BE-38)(iii)'s own gloss names the configuration it forbids: `Π_u ⊆ ρ̄₁` at a non-vacuous
piece **is the (P) trap genuinely realized**. (BE-33) proves the ear's bad locus is
**exactly three mechanisms** (P)/(Z)/(R), and **(BE-34)** says *every trap is a
configuration artifact*. **If** (BE-34)'s quantifier reaches the general-piece side and not
only the ear, then (PENCIL-SATURATES) may already be a corollary — *(P) is realizable only
where it is vacuous* — rather than a new obligation. **Where the coordinator expects to be
wrong:** (BE-33)/(BE-34) are stated **for an EAR** (*"for an **EAR**, `ρ̄₂` spans a Klein
chain with ends `Π_u, Π_v`"*), and the whole point of the general-piece side is that it is
not an ear; BDOUBLE has just been burned by a `δ = min(L,6)` identity that held only at a
**path** side. **Check the ambient before the statement** — that is `RESEARCH-ARC.md` §7's
seventh kind, INAPPLICABLE, which BBASE minted three directions ago and which this reading
is a candidate for.

### Job 1 (PRIMARY, FORCED) — settle (PENCIL-SATURATES)

Prove it, refute it, or reduce it. **What a refutation would cost, so you can price it
before hunting:** a side with `Π ⊆ ρ̄_i` and `ρ_i < 6` would **not** refute half (B) — it
would remove the redundancy theorem's hypothesis, putting `Π_x`/`Π_y` back among the live
blocks (12 → 14) and reinstating BUNIF's tight place. Say that explicitly if you find one.
**A proof, conversely, makes (BE-101)'s corollary unconditional at `a₁ = a₂ = 0`** and is
the cheapest remaining upgrade the thread owns.

**Do not re-hunt what BDOUBLE settled**: (NO-DOUBLE-PENCIL) is refuted, its witness is
`K4 + th(6,6,6)/ab + ear4/ua` at peel `(a,b)`, and the refutation is **slack, not a
shortfall** (margin `−1` at `δ₁+δ₂ = 8`). That witness has `ρ_i = 6` on the saturating
side, so it is **consistent with** (PENCIL-SATURATES) and is not a counterexample to it.

### Job 2 (FORCED — and this is the falsification lane) — the `⟨M⟩` hunt

(BE-97)(iv) names the one shape that would put a **second** block in play at once:
`c_i(⟨M⟩) = 1` on **both** sides — both relative screw spaces containing the virtual edge's
own line `p_x ∨ p_y`. BDOUBLE left it as *"the named hunt"* and the other **12** live blocks
as **unwitnessed rather than excluded**. **Run it.** A hit is a genuine falsification result
and re-opens a block the thread currently ignores; a clean miss with a named cap is worth
having as the first measurement of the 12-block residue. This is the direction's
diversification, and it is a job rather than an aside.

### Job 3 (FORCED, CHEAP) — the residual, and the E-rider

State what half (B) is left with **in (BE-97)(iv)'s terms** — a HIT on job 1 makes the
redundancy theorem unconditional and leaves the 12 blocks, the non-attaining case, the ear
side's (β) window conditions and cross-pair welding. Then read E1/E2/E3 against their
**actual** definitions and **report, never fire**:

> **"The target" in E1–E3 is the ARC's target — `PencilPair K 3 G`** — never a direction's
> local obligation (`61e046a6`). BDOUBLE made the distinction explicitly when it refuted
> one; do the same. Two E3 texts exist (`:1700` two-conjunct, `:2098` one-conjunct); say
> which you read — the last three landings all used `:1700`'s.

### What counts as a HIT — state which you got

1. **(PENCIL-SATURATES) PROVED** — (BE-101)'s corollary becomes unconditional at
   `a₁ = a₂ = 0` and the 14 → 12 drop is a theorem.
2. **REFUTED** — priced as above: the redundancy theorem loses its hypothesis, `Π_x`/`Π_y`
   return to the live list, half (B) is **not** refuted.
3. **Reduced** to a named condition strictly smaller, or shown to follow from a landed
   result whose **ambient actually contains** the general-piece side.
4. **The `⟨M⟩` hunt's verdict** (job 2), with its cap and denominator.
5. **The residual + the E-rider** (job 3).

The coordinator's reading corrected is a reportable result; it is offered as a candidate
for the INAPPLICABLE kind and would be the second instance of that kind if so.

### Bars

- **Do not re-open:** **(NO-DOUBLE-PENCIL)** (refuted, and the refutation is *slack*);
  BUNIF's **law** ((BE-94)–(BE-96)) and its `121/122` disclosure; the **flag coincidence**
  (checked hypothesis, `0` shortfall at 392/392); the **flag base** ((BE-89)–(BE-93));
  the **exhaustiveness obligation** ((BE-70)); `(1,1)` peels ((BE-79)); the **SPREAD step**
  ((BE-74)); the **forced-empty `G` hunt** ((BE-72)); **(BE-32)(+)**; **(BE-41)(ii)**;
  **BWIN's window theorem**; **S-mark's pin**.
- **Do not re-derive** (BE-45)(iii)'s correction of (BE-38)(iii)'s middle clause — it is
  landed, and it is cited here as *evidence about the block*, not as an open question.
- **Not this direction, ranked separately:** §(K-bare-ext)'s two window conditions (qualify
  that token — three owners); **cross-pair welding** ((BE-28)(i)); the **one-end-series**
  case; BTWOCUT's bundle construction; the flag base's cyclomatic-`≥ 2` successor; the
  **W4** side, closed.
- **The Lean hold (2026-08-05) binds**: no `.lean`, in any file, for any reason.
- **Out of scope:** `hK`, **(GR-15)**, class uniformity of the escape, **(K-res)** (a USER
  call).

### Riders

**F11.** *"Never `2` below `ρ = 6`"* is a **universal** claim over sides of internal R-node
peels; 24 × 14 draws, 37 pieces and 4 sides of 92 are measurements over constructed
populations. **Name every population and its cap**, and distinguish *asserted-in-driver*
(which (BE-38)(iii)'s run is, and which is stronger than reported) from *proved*. The
`⟨M⟩` hunt is an existence search — report *"none found under cap C"*, never *"does not
exist"*.

**F21 + `RESEARCH-ARC.md` §6 — and read the gate's docstring before touching the row.**
The `(K-bare)` row is at **1 546 / 1 600 words**, 54 spare. BDOUBLE recomputed to that and
then added a `SPECIAL_CAPS` entry at 1 630; **the coordinator withdrew it**, because the row
was **compliant** and every other entry in that table exists for a row that had *exceeded*
its cap, each with a density argument. The gate's docstring now states the rule: **no
overflow, no bump.** So this landing must **recompute to a target with real headroom** —
the row has absorbed a full direction at each of the last three landings and the honest
question is which of `(BE-1)`–`(BE-90)`'s prose is now redundant — with label preservation
by **scripted set-diff**, never by eye.

**F12** — if the third clause falls, annotate **(BE-38)(iii)** at source alongside its
already-corrected middle clause, and sweep every consumer: **(BE-97)(i)**, **(BE-101)** and
the redundancy corollary all quote it.

**F17 — four status surfaces**, all set to *in flight* by this prep.

**Harness.** `notes/scripts/README.md` first — §1 for the primitives (`bdouble.py`'s
`arith`/`witness`/`hunt`/`price`, `bunif.py`'s block and profile instruments, `bpeel.py`'s
reach layer; do not reimplement). A new driver is `w4/bsatur.py`; an addition-only diff
discharges the figure gate by the one-line check. **`bdouble.py`'s set-diff probe was not
retained** — if you need one, ship it.

**`RESEARCH-ARC.md` §7** — the single reading above is a hypothesis with its ambient risk
named. Kill it without ceremony.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction BSATUR".) Labels
**(BE-104)–(BE-108)**, ***Steps BE103–BE107***, owning file `notes/Pencil-informal.md`
§(K-bare-ext) — **extends, no new section** — driver `w4/bsatur.py`. Opens exactly at the
tail **BDOUBLE declared** (its two tokens' hits are that declaration, in the registry and
the fan-out, opened and confirmed). **Return any unconsumed remainder.** **Mint nothing**
for `Π_x`, `c_i(U)`, `ρ_i`, the (P)/(Z)/(R) traps or the double pencil — all existing
prose/symbol names; this section has gone **five** directions without minting a
configuration-level token. `BSAT` and `BPTRAP` were checked (both 0-hit) and not chosen:
`BSAT` reads as *satisfiability*, and `BPTRAP` names the coordinator's **reading** rather
than the target — precisely what §7 warns against baking into a code.

### Budget — measured at this prep

**`notes/Phase39.md` is at 578/580 lines, 496/525 status-header words.** BDOUBLE merged
rather than appended (BUNIF's *Hand-off* block folded in; three (BE-14) *Decisions* entries
demoted at once) and still landed at 577; the prep's in-flight lines take it to the wire
again. **The landing MUST relocate or merge** — blocks 8 and 9 of `notes/Pencil-structure.md`
are the precedent, and the (BE-14) thread's own oldest-demotes rule is the other lever.

### LANDING — BSATUR, 2026-09-02, `recon-opus`

**Verdict: HIT shapes 2 AND 3 (and 4 and 5). (PENCIL-SATURATES) IS FALSE, and the
repair is FREE.** Landed as §(K-bare-ext) *Steps BE103–BE107*, labels
**(BE-104)–(BE-108)**, driver `notes/scripts/w4/bsatur.py` (five modes), plus
`notes/scripts/gapdiff.py` (the F21 set-diff BDOUBLE did not retain).

**Job 1 — (PENCIL-SATURATES) is REFUTED, at exactly `ρ_i = 5`.** The prep's first
instruction was not *is it true* but *does the third clause survive the scrutiny the
middle clause of its own sentence failed*, and the answer is **no** — for a reason of
the same family and at a different quantifier.

- **(BE-105)(i), proved, no genericity.** At a terminal with `deg_i(x) = 1` the closed
  star of `x` is `{p_x, p_{c₁}} ∪ (side 2's neighbours)`, and side 2 moves freely at a
  fixed flag pair ((BE-70)(ii)) — so **the legal planes at `x` are exactly the pencil of
  planes through the line `p_x ∨ p_{c₁}`**. With `q : K⁴ → Σ_x`, `t ↦ p_x ∧ t`,
  `Π_x ⊆ ρ̄_i ⟺ π_x ⊆ q^{-1}(ρ̄_i ∩ Σ_x)`, and (M1) ((BE-45)(i)) puts `ℓ_e` in
  `ρ̄_i ∩ Σ_x` always. Trichotomy: `dim(ρ̄_i ∩ Σ_x) = 1` → **no** bad plane; `= 2` →
  **exactly one**; `= 3` (i.e. `Σ_x ⊆ ρ̄_i`) → **every** legal plane bad.
- **(BE-105)(ii), the threshold.** `dim(ρ̄_i ∩ Σ_x) = max(1, ρ_i − 3)` — `≥` from the
  modular law plus (M1), `=` **asserted** at every degree-1 terminal of BEARCASE's own
  24-piece battery (`ρ = 3↦1, 4↦1, 5↦2, 6↦3`). **So a bad plane exists iff `ρ_i ≥ 5`**,
  and the clause fails at `ρ_i = 5` and nowhere below.
- **(BE-104)(i), the witness.** `K4(5,3,3,3,3,3)` peeled at the skeleton edge carrying
  the 5-branch: `{x,y}` a 2-cut, **R-node-shaped**, side 1 the 5-edge branch. At 4 of 6
  seeds, asserted: the constructed plane **is** `plane_at`'s closed-star plane of `x` in
  the **whole** graph; `assert_generic_star` **and** `verify_pencil_witness` both pass;
  the flag pair is in the **generic regime**; and **`Π_x ⊆ ρ̄₁` as spaces with `ρ₁ = 5`**.
  `δ = (5,3)`, `a = (0,0)`, `c₁(Π_y) = 1`, `c₂(Π_x) = 0`.
- **F13 negative control**, and it is the whole explanation of the landed measurement: at
  the **same** side-1 configuration the sampler's own random plane gives `c₁(Π_x) = 1`.

**The prep's expected defect was NOT the one found, and the difference matters.** The prep
predicted a **converse/contrapositive slip** — *"the table shows `2` occurring at the
`ρ₁ = 6` rows, which establishes `ρ₁ = 6 ⟹` (nothing), and the clause asserts the converse"*
— the same shape job 2 caught in (BE-44)(ii) one landing ago. That is **not** what is
wrong. (BE-38)(iii)'s own wording is *"`2` occurring at **exactly** the `ρ₁ = 6` rows"*, and
*exactly* is a biconditional over the population measured, so **on its own table the third
clause is a faithful readout** — and the driver's assert makes it a real claim about every
draw the run made, which is the prep's *"what is in its favour"* and it holds up. The defect
is one level up: the run varied the **configuration** and never the **flag**. A converse
slip is a misreading inside a table; this is a **quantifier the sampler never ranged over**.
Recording it because the two failure modes look alike from the outside and only one of them
is fixed by re-reading the table ((BE-105)(iii)).

**The prep's pricing is CONFIRMED, and stated explicitly as it asked.** A side with
`Π ⊆ ρ̄_i` and `ρ_i < 6` does **not** refute half (B): it removes the redundancy
theorem's hypothesis. Measured, over a **new** constructed population (subdivided `K₄` at
every 3rd profile of `{1..4}⁵` with the peeled branch at 5, plus 16 seeded profiles each
of the prism and `K_{3,3}`, 2 draws each): **451** drawn rows, **260** bad-flag rows,
`margin ≤ 0` at `Π_x`, `Π_y`, `⟨M⟩` and `Λ²K⁴` **asserted** at every one, and
`reach = min(δ₁+δ₂,6) + a₁ + a₂` — **the peel attains at every row. 0 shortfalls.**
Margin histogram at `Π_x`: `{−3: 28, −2: 4, −1: 152, 0: 76}`.

**What it does cost, quantified.** At **76** rows `Π_x` is exactly tight with `ρ₁ = 5`,
so (BE-101)(i)'s step *"`c₁(Π_x) = 2`, hence `c₁(Λ²K⁴) = 6`"* is unavailable. Enumerated
over `bdouble.py arith`'s own tuple space: the landed clause gives 3 844 tuples / 300
`Π_x` violations / **0 escaping** (reproducing (BE-101)(i) exactly); the measured floor
`c_i(Π) = 2 ⟹ ρ_i ≥ 5` gives 4 624 / 648 / **24 escaping**; no clause gives 6 400 / 1 655
/ **313** (reproducing its negative control exactly). So the 12 → 14 the prep priced is
real **as a pointwise statement**, and the escapees are arithmetic — none is realized.

**The repair, and why it is free — (BE-107).** **(PENCIL-SATURATES-GEN)**: the same
clause read **at a generic flag**. The bad flags are a **single member** of a
1-parameter pencil (proper closed, by (BE-105)(i)/(ii) whenever `Σ_x ⊄ ρ̄_i`, which the
threshold gives at every `ρ_i ≤ 5`), and at `deg_i(x) ≥ 2` there is **no flag freedom at
all** — `Π_x` is then the span of two of the side's **own** hinge lines, asserted as
spaces at 19 of the 24 pieces, and `c = 2 ⟹ ρ = 6` is asserted and holds there. The
repair costs nothing because **(BE-14) is EXISTENTIAL, not generic** ((BE-16)): the arc
exhibits **one** attaining configuration, the good locus is Zariski-open on the
irreducible `Chart(H)` hence dense ((BE-69)), and `reach` is lower-semicontinuous, so the
generic flag is where the maximum reach already lives. **Under it (BE-101)(i)/(ii) hold
verbatim and the 14 → 12 drop stands.** Recorded, so a future direction does not assume
it: the repair is **not** free for any step needing the block inequalities at *every*
flag ((BE-107)(ii)); and the one shape that would kill the repair too — `Σ_x ⊆ ρ̄_i` at
`ρ_i ≤ 5` — is **named and measured absent, not excluded** ((BE-107)(iii)).

**Job 2 — the `⟨M⟩` hunt, and it fires EMPTY.** Over **72** peel rows of BUNIF's two
populations, with `max(0, ρ_i − 5) ≤ c_i(⟨M⟩) ≤ 1` asserted at every side: census
`(0,0)`: **70**, `(0,1)`: **2**, `(1,1)`: **0**; **0** sides exceeding the generic
profile at `⟨M⟩`. **F11**: *none found under that cap*, never *does not exist*. It is the
first measurement of the 12-block residue (BE-103)(i) item 2 left unwitnessed. Structural
note, offered as a reason and not a proof: the two cheap constructions that force `M`
into a side (a neighbour of `x`, or of `y`, on the line `M`) each put `p_y ∈ π_x` (resp.
`p_x ∈ π_y`) and so **leave the generic flag regime**.

**The coordinator's reading — INAPPLICABLE, and refuted.** Two misses, the first being
the ambient the prep itself flagged. **Ambient**: (BE-33)/(BE-34) are stated for
*(side 1) ∪ **ear**(m)*, and (P) is a lower bound on the **ear's** loss `dim(A ∩ ρ̄₂)`;
(BE-34)(iii) rebuilds trapped rows as exactly that composition. **Content**: even inside
that ambient (BE-34)(iii) says every trap **dissolves once side 1 moves** — a statement
about the composition's attainment, never that `Π_u ⊆ ρ̄₁` forces `ρ̄₁ = Λ²K⁴`; there is
no vacuity statement to inherit. **And the witness refutes it outright**: `Π_x ⊆ ρ̄₁` at
`ρ₁ = 5` is precisely what `bearcase.py`'s assert calls *"the (P) trap, genuinely
realized"* at a **non-vacuous** piece. Second instance of the INAPPLICABLE kind;
`RESEARCH-ARC.md` §7 tally now **ten instances, seven kinds**.

**Job 3 — the residual, in (BE-97)(iv)'s terms.** Half (B) is **not** discharged. Item 1
is closed as posed and replaced by (PENCIL-SATURATES-GEN) with its own residual; `⟨M⟩` is
measured empty at 72 and the remaining **11** blocks are still unwitnessed-not-excluded;
the non-attaining case is unchanged ((BE-101)(iii)); the ear side's (β) window conditions
and cross-pair welding are unchanged.

**The E-rider, reported and not fired.** *"The target" in E1–E3 is the **ARC's** target,
`PencilPair K 3 G`* (`61e046a6`) — what is refuted here is **(PENCIL-SATURATES)**, a
clause a landed theorem is conditional on, i.e. a direction's local obligation. **This
reading is `:1700`'s two-conjunct E3 text**, `:2098`'s one-conjunct deviation noted and
not used. **E1** does not fire (no g-flank); **E2** fires on neither conjunct (the arc's
target is not refuted, and dispatchable attacks are named); **E3** fires on neither
conjunct under either text.

**F21 — the gap-map row, recomputed to a target with real headroom.** `(K-bare)`:
**1 546 → 1 466** words against the generic cap **1 600**, i.e. **134 spare** where
BDOUBLE's recompute left 54 — and the row came out **shorter than it went in** while
absorbing a full direction and five labels (~225 words of pre-existing prose compressed
away against ~145 added). **No `SPECIAL_CAPS` entry added and none needed**: the gate's
docstring rule is *no overflow, no bump*, and the row does not overflow. Label
preservation by **scripted set-diff** (`notes/scripts/gapdiff.py`, kept, with its label
regex stated in its own docstring): **130 codes in, 137 out, ZERO dropped**.

**F12 paid at source, five hunks**: (BE-38)(iii) (third clause annotated FALSE beside its
already-corrected middle clause), (BE-45)(iii) (its *"the first and third clauses stand"*
sentence corrected), (BE-97)(i), (BE-101)(i) and (BE-101)(ii) (both repointed to
(PENCIL-SATURATES-GEN) with the pointwise reading priced), and (BE-103)(i) item 1.

**Reservation consumed in full**; nothing returned. Labels (BE-104)–(BE-108), *Steps
BE103–BE107*, driver at the reserved path. **One** name minted, and it is a *condition*:
**(PENCIL-SATURATES-GEN)**. Nothing minted for `Π_x`, `c_i(U)`, `ρ_i`, the (P)/(Z)/(R)
traps or the double pencil — six directions now without a configuration-level token.

**Successors this direction names**, in its own ranking: (1) **`Σ_x ⊆ ρ̄_i` at
`ρ_i ≤ 5`** ((BE-107)(iii)) — the one shape that kills the repair as well, driver-findable,
measured absent at 5 terminals only, and the thinnest number this landing carries;
(2) **a `deg_i(x) ≥ 2` shape with `c_i(Π_x) = 2` and `ρ_i < 6`** — would show the
refutation is not confined to series ends; (3) **a bad-flag row with `margin > 0`**
(`δ₂ ≤ 2` with `c₂(Π_x) ≥ slack + 1` is the arithmetic shape) — the arc's first exhibited
shortfall, and worth far more than this landing; (4) the **remaining 11 live blocks**,
still unwitnessed; (5) the ear side's **two window conditions** and **cross-pair welding**
((BE-28)(i)), unchanged and untouched here.

## GPACK — sixty-sixth ordinal (single dispatch, prepped 2026-09-02, **LANDED 2026-09-02**) — **the arc returns to `hK` after 22 dispatches**

**Selection provenance: a user call, and a board that had been pointing at dead items.**
Asked whether an `hK`-side dispatch was worth spending this session, the user said yes. A
read-only scoping recon then found that `notes/Pencil-strategy.md` §8's numbered ranking —
which the board's own preamble names as *what a fresh session reads* — carried **rank 1
SPENT** (OQRANK, 2026-08-25: input (a) at all 174 certified classes, **zero rulings**, so
both branches it calls "decisive both ways" are settled) and **rank 2 REFUTED** ((GR-122),
*Step G142*, GHWIT, **2026-08-26 — the day after it was ranked**), with rank 3 not an `hK`
item at all. Coordinator-verified at source, both. Against a measured **22 consecutive
dispatches (ordinals 44–65) with none on `hK`**, that is likely part of *why*. The board is
re-ranked (`70c06abe`) and this is its **new rank 1**.

Dispatched **un-named, single**, at **`recon-opus`** (fable unavailable this session).

### The target, stated exactly

From **§(K-grid) *Step G21*** (`notes/Pencil-informal-grid.md`), read at source. Let `G` be
a tight class shape (`def(G) = 0`); let `Ĝ` be the hub multigraph with branch `β` at
multiplicity `6 − ℓ_β`, so `|E(Ĝ)| = 6(n − 1)`.

> **(GR-18)(i) is a THEOREM** — coordinator-verified: `def(G) = 0` **alone** forces `Ĝ` to
> partition into exactly **6 spanning trees** of `G°` (Tutte / Nash-Williams plus
> 5/6-sparsity). Nothing else is assumed: no `Λ = ∅`, no `D = 0`, no `(GR-4′)`.

Writing `C_β ⊆ {1..6}` for the trees containing `β`, **(GR-18)(iii)** is what is open:

> **Does *some* 6-tree partition of `Ĝ` admit a 3+3 split `J` with
> `|C_β ∩ J| = 3 − A(β)` for a length-legal `A(β)`** — together with an A-end choice on
> each even branch and a consistent hub colouring?

Automatic at `ℓ_β ∈ {1,5}`; at `ℓ_β ∈ {2,3,4}` it says the complement `D_β` is split by `J`
as evenly as possible. **Two freedoms are handed to the prover**: re-choose the packing
(matroid-union **exchange**), and the even branches' bits.

**HIT → (GR-10) → (GR-15) → `hK` on the tight stratum**, over every infinite
characteristic-0 field, and it frees one half of §(K-out)'s input (a). **MISS → the first
(GR-10) flank in 73 directions**: a shape where no packing admits a legal split *is* a
flank by (GR-18)(iii), refuting (GR-10) as a class statement and localizing the obstruction
to a concrete 6-element set-system condition.

### THE COORDINATOR'S ONE READING — VERIFIED IN THE DRIVER, and it says where the work is

This is not a mathematical guess. I read `notes/scripts/w4/gridcol.py`'s `leg_pack`
(`--pack`, line 1001) and it does **two** things: it asserts the **Nash–Williams counting
condition** — that `Ĝ` *can* pack 6 spanning trees — exhaustively at 907/907 shapes; and it
confirms that **(GR-10) certificates ARE such packings**, i.e. it starts from a colouring
that already passes `filter_pass` and reads off the packing it induces.

> **It never constructs an arbitrary packing and asks whether that one admits a legal
> split.** The quantifier (GR-18)(iii) is *about* — *some* 6-tree partition — is exactly the
> one the existing harness does not range over, and the freedom the target hinges on
> (re-choosing the packing by exchange) **has no code behind it**.

**Why this is the load-bearing warning and not bookkeeping:** it is the same shape as the
defect BSATUR found one landing ago and that `RESEARCH-ARC.md` §4 was extended for on
2026-09-02 — an in-driver `assert` that was **true of every draw the run made** and still
missed the answer, because the sampler varied the configuration and never the flag. Here
`--pack`'s assertion is true and tells you about *feasibility*, not about *which* packing.
**Do not read 907/907 as evidence about (GR-18)(iii)**; it is evidence for (GR-18)(i),
which is already a theorem. **Where I expect to be wrong:** possibly the exchange freedom is
unnecessary because the certificate-induced packing is already canonical in some sense the
workbook knows and I do not — if so, say it, and the direction gets much cheaper.

### Job 1 (PRIMARY, FORCED) — settle (GR-18)(iii), and the deliverable must be an ARGUMENT

**The single most important instruction in this spec, and it comes from the re-rank's own
do-not-do:** the `hK` side's record is **907/907, 40 742 exhaustive, 549 172 blocks,
1 158 344 instances, 323 adversarial constructions — and (GR-15)'s status word has never
moved.** §2.2 already wrote the reason: *"A search does not carry a reason."* So:

> **The deliverable is an argument, with the search demoted to an adversarial control.**

What a realistic direction returns — and the arc has this exact pattern three times over
(GFLIP proved (GR-R1) hypothesis-free; (GR-68) proved a single-path repair price `≤ 2` at
any shape with **no cap**; GCHEAP proved an every-step form below an **exact** boundary) —
is **a theorem on a named stratum with an exact boundary, or an adversarial witness**. It
will **not** return (GR-10) whole; do not pad toward that.

**The attack is named and not blind.** TCOL item (v) already records the adversarial places
— `G°` rich in `(2,2,3)`/`(2,2,2,2)` circuits sharing branches, hub multigraphs with many
parallel branch pairs — and says *"a targeted adversarial construction has not been
attempted"*. For this statement it still has not been.

**(GR-13)'s NP-hardness does not bite and points here.** *Step G18* draws its own
consequence: *"Any proof of (GR-10) must be an **existence-of-good-colouring argument** —
exploit the free bit per branch … to avoid the non-polychromatic circuit hypergraphs, not
to characterize them."* And (GR-13) remark (ii) proves the hardness gadgets are
**habitat-infeasible**, leaving *"whether the grouped packing stays NP-complete with
**connected** classes"* open — while real ruling classes are connected. Read that remark
before concluding hardness blocks anything.

### Job 2 (FORCED, CHEAP — and it changes what a HIT is worth) — the tight-stratum caveat

A (GR-15) HIT discharges `hK` **on the tight stratum**. But **`C11`** — a bare odd cycle —
is *in* `hK`'s habitat and is **not** count-tight; **(AC-6) is *"REFUTED as a class
statement"*** by it, and `(K-clos)`'s close-it says *"nothing here would ever make the
statement habitat-uniform: `C11` is permanent"*. The scoping recon **found no gap-map row
owning that non-tight-but-in-habitat remainder** — having read four of 28 rows, so this is
a question, not a finding.

> **Is the remainder genuinely free — §2.5's `dim R_a ≥ 2` ⟹ escape automatic — or is it an
> unowned gap?**

One paragraph, sourced to whichever row does own it (or a statement that none does).
**Read the map with `python3 notes/gapmap.py`, never `sed`/`grep`: one row is a single
20 000+ character line.** This is cheap and it prices the whole `hK`-on-the-tight-stratum
route, so it is forced rather than optional.

### Job 3 (FORCED, CHEAP) — what `hK` is left with, and the E-rider

State what **(GR-15)** and `hK` are left with after this landing, and read E1/E2/E3 against
their **actual** definitions (`notes/Pencil-fanout-archive.md`) — **report, never fire**:

> **"The target" in E1–E3 is the ARC's target — `PencilPair K 3 G`** — never a direction's
> local obligation (`61e046a6`). **E1 is the clause that could actually fire on this side**:
> it wants a **g-flank** exhibited, and a job-1 MISS producing a (GR-10) flank is the
> closest any direction has come in 73. **Report it precisely and do not fire it** — the
> coordinator re-runs E1/E2/E3. Two E3 texts exist (`:1700` two-conjunct, `:2098`
> one-conjunct); the last four landings used `:1700`'s.

### What counts as a HIT — state which you got

1. **(GR-18)(iii) PROVED**, whole or on a named stratum with an **exact** boundary.
2. **A flank** — a shape where no packing admits a legal split. The first in 73 directions,
   and it re-routes (GR-15) onto the collapse-order route. **Say whether it is a g-flank in
   E1's sense.**
3. **Reduced** to a named condition on the branch hypergraph, strictly smaller.
4. **The tight-stratum caveat's verdict** (job 2) — owned row, or unowned gap.
5. **What `hK` is left with + the E-rider** (job 3).

My reading corrected is a reportable result; six of the last eight coordinator readings
died, and each death produced the landing's most useful sentence.

### Bars

- **DO NOT dispatch or drift into another (a′)/(b′) ledger question.** Fourteen directions
  (GLAW → GMINM, *Steps G74–G148*) have worked it; the `(K-grid)` status cell's own summary
  over that span is *"(GR-15) stays OPEN throughout, unchanged in status, no gap-map status
  move"*; its live successor is bookkeeping by its own words; and it produced the board's
  now-refuted rank 2.
- **DO NOT re-run the certificate-3 uniformity route** — GUNIF settled it at *Step G36*,
  *"DEAD AS SPECIFIED"*, the cap being false in general. (The `(K-grid)` **close-it** cell
  still lists a route (i) that *is* certificate 3 while the same cell files it under
  do-not-re-run; that contradiction is **flagged, not yours to resolve** unless your work
  touches the cell, in which case you own the reconciliation.)
- **Do not re-open:** (GR-10) as already-refuted (it is not), (GR-4′), `Λ ≠ ∅`, `D > 0` —
  the three unswept ledger entries are **not** inputs to this route and must not become
  hypotheses of your statement; if your argument needs one, **that is a finding** and the
  route is not `(GR-4′)`-free after all — say so loudly.
- **Not this direction:** **(K-res)** (a standing **USER call**, offered and declined
  2026-09-02); **route σ obligation 1** and the **W4 build** (Lean-held); **option B** (the
  stress-function infrastructure, un-commissioned 2026-07-30); the whole **(BE-14)** thread
  and half (B).
- **The Lean hold (2026-08-05) binds**: no `.lean`, in any file, for any reason. §9's Zheng
  shelf is an **idea source, never a citation**.

### Riders

**F11, in its 2026-09-02 sharpened form — read `RESEARCH-ARC.md` §4 before writing a
driver.** A driver that *asserts* a claim is only as strong as the distribution it runs
under: **name the sampler's support and say which of the claim's own variables it varies.**
That sharpening was promoted from BSATUR's landing yesterday-in-arc-time, and the coordinator
reading above is its first application. **Cap disclosure MANDATORY with the DENOMINATOR
named**; an exhausted cap is *"not found under cap C"*, never *"does not exist"*.

**Cost caution, from the scoping recon.** `--pack` is already **98 s**; a packing-space
explorer is combinatorially heavier. **Cap the exchange neighbourhood explicitly and
disclose it** — GHWIT's precedent is the standard (*"the 2-chord transposition
neighbourhood only … not a search"*).

**F21 — and this row is the biggest in the corpus.** `(K-grid)` is at **2 390 / 2 715
status words** (the one row with a `SPECIAL_CAPS` entry, bumped three times *because it had
overflowed*). **Recompute to a target**, label preservation by **`python3
notes/scripts/gapdiff.py`** — the scripted set-diff shipped yesterday-in-arc-time, now
mandated by `notes/CLAUDE.md` for any recompute. **No overflow, no bump**: the gate's
docstring records a bump proposed and withdrawn on 2026-09-02 for exactly that reason.

**F17 — four status surfaces**, all set to *in flight* by this prep; note that
`notes/Phase39.md`'s ranked list is the **(BE-14)** thread's, and this prep has added an
`hK` lane above it pointing at the strategy board rather than duplicating it.

**Harness.** `notes/scripts/README.md` first — §1 for the primitives (`gridcol.py`,
`packmm.py`, `gridwit.py`, `grid.py`, `closure.py`; do not reimplement `branch_decomp`,
`nash_williams_ok`, `colourings` or `filter_pass`). A new driver is `w4/gpack.py`;
addition-only discharges the figure gate by the one-line check.

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction GPACK".) Labels
**(GR-129)–(GR-133)**, ***Steps G149–G153***, owning file
`notes/Pencil-informal-grid.md` §(K-grid) — **extends, no new section** — driver
`w4/gpack.py`. Opens at the tail **GMINM returned**: it reserved (GR-125)–(GR-129) and
G145–G149, consumed only through (GR-128)/G148, and **explicitly returned (GR-129) and Step
G149**, declaring *"the live tail is therefore (GR-129)+ / Step G149+"*. Every hit on
`(GR-129)`/`(GR-130)`/`G149`/`G150` was opened and confirmed to be that **return record**,
not a consumed label. **Return any unconsumed remainder.** `GGROUP` was checked (0-hit) and
**not chosen**: *group* now collides with a live technical object in the sibling thread
(BUNIF's stabilizer `S(ϕ) ⊆ PGL₄`), which is exactly the (L5) overlap the rule exists to
catch. `GBIS` was 0-hit but names the coordinator's framing (*equitable bisection*) rather
than the target. **`GPACK` names the object the freedom acts on.**

### Budget — measured at this prep

**`notes/Phase39.md` is at 575/580 lines, 496/525 status-header words** — BSATUR merged
rather than appended (five demoted (BE-14) entries one-lined). The prep's `hK` lane is
**net-new structure** in a note whose *Hand-off* has been single-threaded for 20+
directions, so it was paid for inside the ranked list. **The landing MUST relocate or
merge** — `notes/Pencil-structure.md` blocks 8 and 9 are the precedent.

### LANDING — GPACK, 2026-09-02, `recon-opus`

**Verdict: HIT shape 1 on a named half, HIT shape 3 on the rest, plus jobs 2 and 3. The
SPLIT is a THEOREM — unconditionally — and the exchange freedom it uses is LOAD-BEARING.**
Landed as §(K-grid) *Steps G149–G153*, labels **(GR-129)–(GR-133)**, driver
`notes/scripts/w4/gpack.py` (three modes).

**Job 1, part 1 — the target's normal form ((GR-129)).** Two reductions, both elementary
and both removing an object from the statement. First, *"`|C_β ∩ J| = 3 − A(β)` for a
length-legal `A(β)`"* is exactly *"`J` bisects `C_β` as evenly as possible"* — because
`A(β) ∈ {⌊ℓ_β/2⌋, ⌈ℓ_β/2⌉}` by (GR-16)(i) and `|C_β| = 6 − ℓ_β`. Second, and this is the
one that does the work: a **(packing, split) pair is the same data as a signing** `s` of
the odd-length branches, `s_β = ±1`, subject to

> `|s(F)| ≤ σ(F)` at every branch set `F`, where `σ(F) := Σ_{β∈F} ℓ_β − 6·c(F)`,

the two sides being the multigraphs at multiplicity `(m_β ± s_β)/2`. The packing has
disappeared from the statement; the unknown is one bit per odd branch, and the bound is the
**5/6-sparsity slack** — the same quantity `gridcol.nash_williams_ok` computes for
(GR-18)(i). A free corollary: any legal split is **automatically balanced** ((GR-16)(i)'s
condition falls out of `σ(E) = 0`), so no argument for (GR-18)(iii) has to arrange balance.

**Job 1, part 2 — the theorem ((GR-130)). A legal signing always exists.** Unconditional:
`def(G) = 0` and nothing else — no `Λ = ∅`, no `D = 0`, no `(GR-4′)`, no colouring, no
genericity. The proof is four landed classical facts over `σ ≥ 0`: (1) the half-multigraph
`⌊m_β/2⌋` is independent in `N₃ = M(G°)^{∨3}` (Nash-Williams arboricity); (2) `⌈m_β/2⌉`
*contains* three disjoint spanning trees, because halving the cross-count of a 6-tree
packing leaves `3(p−1)` (Tutte/Nash-Williams packing); so (3) `M := (N₃/H₀)|_O` has rank
`|O|/2` and a legal signing is exactly a partition of `O` into **two bases of `M`**, which
by (4) Edmonds' covering theorem exists iff `|S| ≤ 2·rank_M(S)` for all `S ⊆ O` — and that
inequality, expanded through the matroid-union rank formula, reads
`σ(F) + o(F) + (|S| − 2|S ∩ F|) ≥ 0`, whose left side is `≥ σ(F) ≥ 0` identically. **So the
grouping problem's packing-and-split half is closed**, and *Step G21*'s own naming of the
equitable bisection as *"the shape of the argument a successor should attack"* is retired:
that object is free. `--split` re-derives the conclusion at **907/907** without the proof,
through `saferes.union_rank` as an oracle independent of `σ`, and cross-checks the criterion
itself at **7 291/7 291** (shape, signing) instances with **0** disagreements.

**Job 1, part 3 — the coordinator's reading, half confirmed and half REFUTED ((GR-131)).**
The reading itself — that `--pack` asserts Nash-Williams *feasibility* and reads packings off
colourings that already certify (GR-10), never ranging over the quantifier (iii) is about —
was **verified at source and is correct**, and it is what made the direction dispatchable.
Its *named expectation of being wrong* — that the exchange freedom might be unnecessary
because the certificate-induced packing is canonical — is **refuted, exhaustively**. Over the
first 40 census shapes with `M ≤ 6`, all **266 700** 6-tree partitions of `Ĝ` were
enumerated: **6 840** of them (2.6 %) admit **no** legal 3+3 split. The mechanism is uniform
and exact — **all 6 840** fail because the *split graph* (an edge for each `ℓ_β ∈ {2,4}`
branch, joining the two trees `J` must separate) is **non-bipartite**; **0** are
bipartite-but-unbalanced and **0** fail only through the `ℓ_β = 3` clause. Witness
`K4(1,2,3,4,4,4)`, packing `((0,1,2),(0,1,2),(0,1,2),(1,3,4),(1,3,5),(2,4,5))`, separation
pairs a triangle on `{3,4,5}`. (GR-130)'s proof does not split a handed packing; it
*constructs* one, which is the exchange freedom in its strongest form. **The record the prep
asked for: `--pack`'s 907/907 is evidence for (GR-18)(i), already a theorem, and none for
(iii)** — `RESEARCH-ARC.md` §4's sharpening, second application, one landing after BSATUR
minted it.

**Job 1, part 4 — what is left, named exactly ((GR-132)).** At `Λ = ∅` the remaining clauses
of (GR-18)(iii) are a **list-colouring of the hubs**: labels `g_A(u) ∈ J`, `g_B(u) ∈ J^c`,
lists `J ∖ C_β` of size `A(β)` read off the packing, a `≠` constraint across every branch
whose two ends carry the same colour, and *"no monochromatic hub"*. The proof is (GR-16)(iii)
plus counting — at `Λ = ∅` every A-class is a hub star or an interior singleton, the stars
are the only classes two branches share, and the singletons absorb whatever labels are left.
Machine-asserted **both ways**: **229 320/229 320** accepted (packing, split) pairs rebuild a
colouring that passes `gridcol.filter_pass` *and* carries a `packmm.fast_triple` in both
blocks, and **124/124** certificate-induced pairs are accepted. **Where the difficulty now
sits is measurable**: the list at a length-2 branch has size **1** on each side — the hub
label is *forced* — which is exactly the profile (GR-17)(d) isolates as binding
(`(2,2,3)`/`(2,2,2,2)`) and exactly TCOL item (v)'s named adversarial places. A successor
hunts there, with the whole freedom of (GR-130) available: `|s(F)| ≤ σ(F)` describes **all**
legal splits, not one.

**Job 2 — the tight-stratum caveat: OWNED, not free, and the scoping recon's premise is
half-wrong.** The remainder of `hK`'s habitat beyond the tight stratum is `hnoRigid` with
`index ≠ 0`; `C11` is in it (`index = −5`, `def > 0`). It is **not an unowned gap**: the
`§(K-res)/(RS-5)` row owns the audit and says, in its own words, that the two quantifiers are
**disjoint** (*"tight shapes satisfy `hnoRigid`, (K-res) shapes refute it, so closing (GR-15)
does NOT close this row"* — that claim, not anything re-verified here, is what covers the
`def = 0`, `index > 0` corner; a successor that needs it should check it rather than inherit
it) and that *"`def > 0`
members stay with the **escape route**"* ((RS-6), the deficient fringe refuted for the grid
route with a mechanism at θ(2,3,7)). But it is **not free**, and the `dim R_a ≥ 2` reading
does not survive its source: `Pencil-strategy.md` §2.5 says the count **forces**
`dim R_a = 1` at *tight* shapes — a negative result about counting invariants, not a supply
of `dim R_a ≥ 2` anywhere — and §(K-flank) *F5(d)* exhibits seeds where the count predicts
`1` and the geometry delivers `0`. **Price: a (GR-15) HIT buys `hK` on the tight stratum and
hands the `def > 0` habitat to the escape route**, whose rows ((K-Λ), (K-wit), (K-pitch),
(K-out), (K-dom)) are all live. §(K-clos)'s close-it says the same from the other side:
*"`C11` is permanent."*

**Job 3 — what (GR-15) and `hK` are left with, and the E-rider, reported and not fired.**
(GR-10) and (GR-15) are **unchanged in status**; no gap-map status word moves on either.
What changes is the *shape* of the residual: it is no longer a packing problem, so every
instrument the arc built for it (Nash-Williams, Edmonds, the `2^M` sparsity sweep) is now on
the closed side of the line, and (GR-13)'s NP-completeness of the *grouped* packing is better
located — the hardness cannot live in the packing or the split, so it lives in the grouping
map, which is the object (GR-132) exhibits. **The E-rider**, read against the **ARC's**
target `PencilPair K 3 G` (`61e046a6`), E3 in `:1700`'s two-conjunct text: **E1 does NOT
fire**, and the distinction is worth stating loudly because this landing is the closest an
`hK`-side direction has come to tripping it by accident — **the 6 840 split-less packings are
NOT flanks.** A g-flank is a `D = 0` *shape* whose **every** admissible colouring is binding;
(GR-131)'s objects are *packings*, at shapes that do carry a good packing and a (GR-10)
certificate. Nothing here refutes per-shape (GR-15) anywhere, and no flank was found.
**E2** does not fire (target not refuted; (GR-132) is a dispatchable attack). **E3** does not
fire (the arc's target is not proven).

**F21 — the corpus's biggest row, recomputed to an explicit target.** `(K-grid)`:
**2 390 → 2 500** status words against the `SPECIAL_CAPS` cap **2 715**, hitting the target
`≤ 2 500` set before the edit (~140 added for this direction, ~30 compressed out of the
(GR-94) and (b′) units, both keeping every code). Close-it **959 → 980 / 985**. **No
`SPECIAL_CAPS` entry proposed and none needed** — *no overflow, no bump*. Label preservation
by `python3 notes/scripts/gapdiff.py K-grid`: **135 codes in, 141 out, ZERO dropped, 6
added**. Column 2's stale step range `G0–G129` corrected to `G0–G153` in the same edit.

**The close-it cell's route (iv) is CONSUMED, and the flagged contradiction reconciled** (the
prep made it mine because my work touches the cell). Route (iv) was *"an exchange argument on
(GR-18)'s guaranteed 6-tree packing supplying a length-compatible 3+3 split"* — now
**settled**, and rewritten to say so and to point at (GR-132) for what it leaves. The
contradiction between route (i) and the do-not-re-run list is a **method/statement
confusion**: route (i) is the *statement* (`a = 0 ∧ max g ≤ 0` at some colouring, plus
(GR-4′)); what (GR-28)(iv)/(GR-29)/(GR-30) killed is the uniform-`g`-cap *method* for it.
One clause added to route (i) saying exactly that.

**Reservation consumed in full**; nothing returned. Labels (GR-129)–(GR-133), *Steps
G149–G153*, driver at the reserved path; the tail declared for the next reservation is
**(GR-134) / Step G154**. Nothing minted for the split graph — deliberately left unlettered,
because `P` already carries (GR-8)'s subgraph and this direction's own signing subset.

**Cost, and the prep's cost caution answered.** `--split` **16 s**, `--arb` 40 s, `--resid`
234 s, `--validate` **336–402 s** — inside the 600 s foreground budget, byte-identical across
two `PYTHONHASHSEED=0` runs (394 s, 336 s) and one at 999 (402 s); a range, because the wall
clock moved ~20 % with machine load while not one output byte did. The prep warned that a
packing-space explorer would be combinatorially heavier than `--pack`'s 98 s and told me to
**cap the exchange neighbourhood and disclose it**. **No exchange cap was needed and none is
disclosed**, because (GR-130) does not explore a neighbourhood at all — it *constructs* the
packing — and the leg that covers the same 907 shapes `--pack` covers is `--split` at **16 s
against its 98 s**. The 234 s is `--resid`, which is a different kind of cost: it enumerates
every 6-tree partition of a 12-shape subpool and puts every accepted pair through
`filter_pass` and `fast_triple` twice over. The caps that do exist are **population** caps,
disclosed with denominators: all 907 shapes for `--split`; the first 40 with `M ≤ 6` for
`--arb`; the first 12 with `M ≤ 6` and `Λ = ∅` for `--resid`.

**Successors this direction names**, in its own ranking: (1) **the (GR-132) list-colouring at
the `ℓ = 2`-rich shapes** — the forced-label conflict is the only mechanism left, it is
finite and local, and `(2,2,3)`/`(2,2,2,2)` is where (GR-17)(d) independently says the
circuit law binds; (2) **(GR-132) at `Λ ≠ ∅`** — the merging conjunct (GR-16)(iii)/(iv)
supplies is not written, and every current statement of the residual is a `Λ = ∅` one;
(3) **a flank hunt on the list-colouring**, now a genuinely finite object: a shape at which
*no* legal split admits a consistent hub colouring would refute (GR-10) as a class statement
and be the first (GR-10) flank in 74 directions; (4) the `(K-grid)` close-it's routes (ii)
and (iii) (the collapse-order bound, and which `r`-groupings certify), untouched here.

## BSIGMA — sixty-seventh ordinal (single dispatch, **DRAFT-ONLY**, run 2026-09-02 in parallel with GPACK) — the disproof lane

**Selection provenance: a user call for parallelism, and the arc's first genuinely
concurrent pair since the eighth fan-out.** With GPACK (66) in flight on `hK`, the user
asked whether anything else could be dispatched in parallel to help prove or disprove the
conjecture. The binding constraint was **not** budget: GPACK is a *committing* dispatch, so
by `RESEARCH-ARC.md` §2 anything concurrent must be **read-only with respect to every
shared file**. BSIGMA was therefore dispatched **draft-only** — spec delivered in the
invocation prompt, deliverable written to the session scratchpad, **nothing committed and
no tracked file touched** — and the coordinator landed it serially after GPACK. That is
§2's pattern exercised for the first time outside a prepared fan-out, and it worked with
zero collisions on a tree that took a full landing underneath it.

**Why this target, out of everything available.** It is the **disproof lane**: BSATUR's own
(BE-107)(iii) named `Σ_x ⊆ ρ̄_i` at `ρ_i ≤ 5` as *"the thing to hunt"* — the one shape that
kills **(PENCIL-SATURATES-GEN)**, and therefore the hypothesis BSATUR's entire landing rests
on. It is also genuinely independent of GPACK: different workbook (§(K-bare-ext) vs
§(K-grid)), different label family, different gap-map row, different driver lineage. Three
other candidates were considered and **not** dispatched, recorded so the choice is legible:
the collapse-order bound (board rank 2 — arguably a bigger prize, but 18 separators on two
shapes, geometry re-entering at `r = 4`, no landed input and no driver), the ZNEQ pool
re-key (*"no new mathematics"* by its own description), and OGEOM's successors
(disproof-risk reduction, which **(OC-24)** says can never be the binding obstruction).

Run at **`recon-opus`** (fable unavailable this session).

### The spec, as dispatched

**Target.** Hunt `Σ_x ⊆ ρ̄_i` at `ρ_i ≤ 5` — equivalently a shape forcing
`dim(ρ̄_i ∩ Σ_x) = 3` at `ρ_i = 5`. Exhibit one with its **regime checked**, or report
*"none found under cap C"* with the cap and denominator named.

**Priced in advance, and the direction was told to say it plainly:** a hit costs the
redundancy theorem's hypothesis — `Π_x`/`Π_y` return to the live blocks, 12 → 14, and
BUNIF's tight place is reinstated — but **does not refute half (B)**.

**The rider that bit hardest.** `RESEARCH-ARC.md` §4's 2026-09-02 sharpening — *an in-driver
assertion is only as strong as the sampler's support; name that support and say which of
the claim's own variables it varies* — was made a **forced job**, because the target's own
evidence has exactly the shape that had just failed: (BE-105)(ii)'s threshold is *"asserted
at every `deg = 1` terminal of the 24-piece battery"*.

**Bars.** Do not re-open BSATUR's landing; do not touch the `(K-grid)`/`(GR-…)` lane (GPACK
was there); (K-res) is a **USER call**; the 2026-08-05 Lean hold binds.

### LANDING WRITE-UP — BSIGMA, 2026-09-02: **the residual is REALIZED, and its floor is a THEOREM**

**HIT.** `Σ_x ⊆ ρ̄₁` at `ρ₁ = 5`, on **BSATUR's own pinned peel** `K4(5,3,3,3,3,3)` — what is
new is the **configuration**, not the peel. Place the peeled branch `x, b₀, b₁, b₂, b₃, y`
with `p_x, p_{b₁}, p_{b₂}, p_{b₃}, p_y ∈ π` and `p_{b₀} ∉ π`. Then
`ρ̄₁ = ⟨ℓ₁, ℓ₂⟩ ⊕ Λ²π` has `ρ₁ = 5` exactly and contains `p_x ∧ π` (dimension 2, because
`p_x ∈ π`) together with `ℓ₁ = p_x ∧ p_{b₀}`; their span is
`p_x ∧ (π + ⟨p_{b₀}⟩) = p_x ∧ K⁴ = Σ_x`. So **every** plane through `p_x` is bad — legal or
not — and **(PENCIL-SATURATES-GEN) is FALSE as stated**. Asserted at 6/6 seeds: both gates,
`flag_frame` non-`None`, R-node-shaped, `δ = (5,3)`, `a = (0,0)`, `c₁(Π_x) = 2`, and 24
further random planes through `p_x` all bad. **F13 control**: the same peel drawn by
`bsatur.draw_peel` gives `max(1, ρ−3)` and 0 hits.

**Regime checked, and it is why this witness is the right one.** `deg₁(x) = deg₁(y) = 1`, so
side 1 never forces `π_y` — both terminals are series ends. The `ρ_i = 4` shapes the
direction *did* find fail exactly there (below).

**SLACK, not a shortfall — for the third refutation running.** 78 rows over 39 constructed
profiles, every one a hit row, `margin ≤ 0` at `Π_x`/`Π_y`/`⟨M⟩`/`Λ²K⁴` and
`reach = min(δ₁+δ₂,6) + a₁ + a₂` asserted at each: **0 shortfalls**, margin histogram
`{−3: 66, −2: 12}`, `Π_x` never tight. Half (B) is **not** refuted.

**THE FLOOR IS A THEOREM, and it is the landing's second result.** Projection from `p_x` is
the linear map `ω ↦ ω ∧ p_x`, whose kernel is exactly `Σ_x`, so
`dim(ρ̄ ∩ Σ_x) = ρ − dim(ρ̄ ∧ p_x)`. At a path side `dim⟨L_j⟩ = 0` is killed by
`assert_generic_star`, and `dim⟨L_j⟩ = 1` forces every point into one plane with `p_x`,
capping `ρ ≤ 3`. Hence **`Σ_x ⊆ ρ̄_i ⟹ ρ_i ≥ 5` is PROVED**, improving (BE-107)(iii)'s
modular bound from 3 to 5 — and the same identity **upgrades (BE-105)(ii)'s measured `≤`
half to proved** at a generic path configuration.

**`ρ_i ≤ 4`: none found under cap, and the misses are instructive.** Bucket A
(`deg_i(y) = 1`, the only bucket a generic-regime peel can present): **668 rows / 16
topologies**, zero. Bucket B (`deg_i(y) ≥ 2`): **544 rows / 13 topologies**, and the shape
**is** reached at `ρ = 4` (`pendant + cycle(8)`, 8/8) — but at **8 of 8** those rows have
`p_x` in the plane the side itself forces on `y`, so `flag_frame` rejects them: **off the
generic flag regime**. That is BSATUR's own structural warning firing on a *positive*
result rather than on a construction.

**JOB 2 — the support audit, and it answers more sharply than the rider asked.**
`bearcase.piece_battery()` returns 24 pieces; `deg(u) = 1` at **exactly 5**, and they are
the **five path pieces**, one topological family in which the side *is* the path. Inside
each, `run_mech` keeps **one** configuration — the arg-max of `ρ` over ≤6 draws of
`sample_piece_config`, coordinates uniform on a box, so every kept configuration is
**generic**. The sharp finding: **the flag is not a variable of this claim at all**
(`Σ_x = p_x ∧ K⁴` depends on `p_x` alone), so unlike BSATUR's case the missing quantifier is
the **configuration stratum**. `ρ = 5 ↦ 2, never 3` is a true statement about generic
configurations of a path — now *proved* there — and false one stratum away. Re-running the
battery reproduces `3↦1, 4↦1, 5↦2, 6↦3` verbatim.

**JOB 3 — the residual.** Half (B) is **not** discharged. Item 1 is closed as posed **for
the second direction running** and replaced by **(PENCIL-SATURATES-CHART)** — the clause at
a generic *point of `Chart(H)`* — free by the same (BE-16)+(BE-69)+semicontinuity argument,
now with a **proved**-proper bad locus at path sides. Its own residual is narrower: a piece
where `Σ_x ⊆ ρ̄_i` holds at a *generic* configuration. The live-block count now reads **three
ways**: 14 pointwise in the flag; **14 pointwise in the configuration at a generic flag
(new)**; 12 at a generic chart point.

**Honest cap, self-caught.** The planted stratum draws at only **5 of 16** bucket-A
topologies (all five paths); every hub-carrying side rejects it under this sampler, listed
by name in the driver output. So the shape at a **non-path** side is *unmeasured, not
excluded*. An earlier draft of the direction's own claimed otherwise; its data refuted it
and the draft was corrected before return.

**E-rider: none of E1/E2/E3 fires**, read at source with `:1700`'s two-conjunct E3. E1: no
g-flank. E2: what is refuted is **(PENCIL-SATURATES-GEN), a direction's local obligation,
not the arc's target**, and dispatchable attacks are named. E3: target not proven, and it
fails under `:2098` too, on the first conjunct.

**Driver** `notes/scripts/w4/bsigma.py`, six modes
(`witness | mech | support | floor | price | validate`), exact ℚ, seed `20260902`.

### Coordinator note on the landing — one defect the draft carried

**Appendix B2 dropped a label, and only the set-diff saw it.** The draft's status-column
replacement removed the citation `(BE-107)(iii)`, whose residual this direction had just
*realized*. `notes/check-gapmap-cells.py` (the word cap) passed; **`notes/scripts/gapdiff.py`
failed** — *137 in, 142 out, 1 DROPPED*. Repaired at landing by keeping the citation with
its new status (*"(BE-107)(iii)'s named residual REALIZED, not absent"*). This is the script
GPACK's predecessor shipped one landing earlier, catching a real drop on its second outing,
and it is also the reason the coordinator's **own** first compression attempt was thrown
away: that attempt dropped the same label *and made the row longer*. The row finally went
**1 466 → 1 538 / 1 600** with **zero dropped**, by folding the (BE-104)/(BE-105) mechanism
detail — now workbook material, superseded as headline by the proved floor — rather than by
folding the history.

---

## GLIST — sixty-eighth ordinal (concurrent pair with a `(K-bare)` draft-only sibling, prepped 2026-09-02, **LANDED 2026-09-02**) — the `hK` lane's named successor, one direction after GPACK

**Selection provenance.** `notes/Phase39.md`'s own **NEXT CONCRETE TASK** and **rank 1** of
`notes/Pencil-strategy.md` §8's corrected `hK` ranking — the successor GPACK itself named at
§(K-grid) *Step G152*. The **committing** dispatch of a concurrent pair, the sibling running
draft-only on the (BE-14) thread; dispatched **`recon-opus`**.

### The target, stated exactly

From **§(K-grid) *Step G152* ((GR-132))**, read at source. At a tight class shape with
`Λ = ∅`, fix a legal (packing, split) pair `(C, J)`. Is there always **some** such pair,
end pattern and hub labelling `g_A : hubs → J`, `g_B : hubs → J^c` satisfying (GR-132)'s
(a)/(b)/(c)? Concentrate where (GR-132)'s hand-off sends a successor: (GR-17)(d)'s binding
profiles **(2,2,3)** and **(2,2,2,2)**, and the adversarial places
`notes/Pencil-fanout-archive.md` §TCOL item (v) names.

**What the prep supplied as verified, and it is all load-bearing.** (GR-130) is
unconditional, so the packing-and-split half is closed and the criterion `|s(F)| ≤ σ(F)`
describes **all** legal splits — the hunt ranges over a *described set*. (GR-131) makes the
exchange freedom load-bearing (6 840 of 266 700 packings admit no split, every one by an odd
cycle). (GR-132) is proven at `Λ = ∅` only, machine-asserted at 12 census shapes. (GR-133)
is the price: a (GR-15) HIT buys `hK` on the **tight** stratum only, the `def > 0` habitat
being **owned** by `§(K-res)` (RS-5)/(RS-6) but not free — and **`Pencil-strategy.md` §2.5
must not be quoted as supplying freeness anywhere**, being a *negative* result.

### The coordinator's reading, offered as a HYPOTHESIS (`RESEARCH-ARC.md` §7)

Named honestly in the spec as *the coordinator's own reading of (GR-132)'s statement text,
no measurement*: **the `ℓ = 2`-only sub-case may be an ORIENTATION problem rather than a
colouring problem** — at an even branch exactly one end is A, at `ℓ_β = 2` both lists are
singletons, so the bit is which endpoint takes the forced A-label; (b) is then automatic and
(c) vacuous, leaving a constrained orientation on `G°`'s hubs. Three places the spec
expected to be wrong: (1) the forced label depends on `β`, so agreement at a hub is a real
constraint; (2) **(2,2,3)** carries an odd branch and reintroduces (c)'s `≠`; (3) (a) may
not be satisfiable alongside an all-`ℓ = 2` orientation at a degree-2 hub.

### Forced jobs (reproduced from the spec)

1. **The deliverable is an ARGUMENT, the search demoted to an adversarial control** — say
   plainly whether the `ℓ = 2`-rich case is a **theorem**, **refuted by an exhibited
   conflict**, or **reduced to a named strictly-smaller condition**.
2. **The sampler-support audit is FORCED** (`RESEARCH-ARC.md` §4's 2026-09-02 sharpening),
   because (GR-132)'s evidence has exactly the shape that has just failed twice: name the
   population's support and say which of (GR-132)'s own variables it varies — (i) is any of
   the 12 shapes `ℓ = 2`-rich at all? (ii) do `--resid`'s 124 certificate-induced pairs
   range over the **packing exchange freedom**?
3. **Reconcile the internal contradiction the option board flags and does not resolve** —
   the `(K-grid)` close-it cell lists route (i) as live *and* files the certificate-3
   uniformity route under do-not-re-run.
4. **Cap disclosure is mandatory**, travelling with the figure everywhere it is quoted.
5. **Restate the `Λ ≠ ∅` caveat** so nothing is over-read; it is not this direction's to
   close.
6. **TERMINATION riders E1/E2/E3 read at source**, E1 live in its **literal** reading
   because a g-flank is a §(K-grid) object.

**Bars.** No (a′)/(b′) ledger direction; no `notes/Pencil-informal.md` §(K-bare-ext) or
`(BE-…)` label (the sibling is there); no re-derivation of the packing/split half; **(K-res)
is a user call and the 2026-08-05 Lean hold binds — no `.lean`.**

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction GLIST".) Labels
**(GR-134)–(GR-138)**, ***Steps G154–G158***, owning file `notes/Pencil-informal-grid.md`
§(K-grid) — **extends, no new section** — driver `w4/glist.py`. Opens at exactly the tail
**GPACK declared**. `GLIST`/`glist` verified **0-hit** as raw substrings across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2`; `(GR-135)`–`(GR-138)` and `Step G155`–`G158` 0-hit,
and the two hits on `(GR-134)`/`Step G154` were both opened and confirmed to be **GPACK's
tail declaration**, not consumed labels.

### LANDING — GLIST, 2026-09-02, `recon-opus`

**Verdict: HIT shape 3 — REDUCED to a named strictly-smaller condition — with HIT shape 1 on
two named sub-statements, and the coordinator's reading SPLIT.** Landed as §(K-grid) *Steps
G154–G158*, labels **(GR-134)–(GR-138)**, driver `notes/scripts/w4/glist.py` (four modes).

**Job 1, the argument.** Two theorems and one measured negative.

- **(GR-134), the orientation normal form.** The end pattern is **eliminable**: (GR-132)'s
  (a)/(b)/(c) are equivalent to a CSP in two hub functions `α : hubs → J`, `γ : hubs → J^c`
  alone, whose entire content is *every branch at `u` inside `T_{α(u)}` has its `u`-end B,
  and every branch inside `T_{γ(u)}` has its `u`-end A*. And **clause (a) is FREE** — implied
  by (b), because each of the six parts of (GR-18)(i)'s partition is a **spanning** tree, so
  `deg_{T_{α(u)}}(u) ≥ 1` supplies the B-end and `deg_{T_{γ(u)}}(u) ≥ 1` the A-end. Cross-
  oracled against `gpack.csp_witness` at **472 680/472 680** pairs, 0 disagreements; (a)
  **asserted rather than imposed** at all 229 320 feasible ones.
- **(GR-135), the local criterion.** At a hub whose branches are all length 2 (*pure*), the
  local system is feasible iff the incident cells lie in one cross of the `3 × 3` grid
  `J × J^c`; at **hub degree 3 this is `J`-free** and reads *`u` is a **leaf** of at least
  one of the six trees* — equivalently not `deg_{T_j}(u) = 2` for all six `j`, equivalently
  the three `D_β` are **pairwise disjoint, a perfect matching of `{1..6}`**. Verified against
  brute force **exhaustively over the abstract configuration space** (729 at degree 3, 6 561
  at degree 4) and at 1 887 120 realized instances. This is a **second obstruction
  mechanism, independent of (GR-131)'s odd cycle**: that one kills the *split*, this one
  kills the *colouring* at a pair whose split is legal.
- **(GR-136), the reduction and its limit.** By the excess law (GR-21) there is **no
  all-length-2 shape** (`Σ(ℓ−2) = 2D + 6 ≥ 6`), so the `ℓ = 2`-only case is about **hubs**,
  never a shape; at `D = 0` at least `n − 12` hubs are pure, and the local half is a
  **leaf-covering** demand on the 6-tree partition, not counting-obstructed. **But the local
  conditions are not the residual:** of the 243 360 infeasible legal pairs, 44 640 fail
  (GR-135) at some hub and **198 720 (82 %) are locally feasible at every hub**. So no
  per-hub repair can close (GR-18)(iii) — which is exactly why this is *reduced*, not
  *proved*. Exhaustively at `n_hub = 4` on the `D = 0` stratum (312 class shapes, 28 with a
  pure hub, every partition, every split) **some legal pair is feasible at every shape**, the
  conflict being realized (80 640 of 1 013 760 pairs) and always escapable.

**Job 2, the support audit ((GR-137)) — and it REFUTES the coordinator's own audit
expectation.** The spec asked whether the population ever presents the conflict. **It does:**
`--resid`'s twelve shapes are three thetas plus nine `K4`s, `max_u t(u) = 3`, and **6 of the
12 carry a pure hub** — the `K4(2,2,2,·,·,·)` shapes, whose length-2 branches form a **star**
at one hub while the opposite triangle absorbs the whole excess. What *is* defective is the
denominator: the `229 320/229 320` figure counts only the pairs the CSP **accepts** (the
soundness loop `continue`s on rejection), and the same enumeration produces **472 680** legal
pairs of which **243 360 are rejected** — a 48.5 % acceptance rate, 17 280 of the rejections
carrying (GR-135)'s conflict outright. On sub-question (ii): the **soundness** leg *does*
range over the full exchange freedom (`all_packings` × `legal_splits`, both exhaustive); the
**completeness** leg does not (certificate-induced packings only, `J = (0,1,2)` pinned).
Wider scale: 24 of the 303 census `Λ = ∅` shapes carry a pure hub, and **2 623 of the 4 598**
`n_hub = 6` `D = 0` shapes do.

**The audit fired once more, on this direction's own driver, and it nearly produced a false
flank.** `--rich`'s `n_hub = 6` control is a constructed `K_{3,3}` class shape with one pure
hub. A seeded randomized DFS collected 4 000 6-tree partitions there and found **21 336 legal
pairs, all conflicted, 0 CSP-feasible** — which read as a nonexistence claim would have been a
(GR-10) flank. It is not: the shape's 512 admissible colourings contain **60** that are
filter-passing with a both-block tree-triple, and **all 60** induce a legal pair that is
CSP-feasible with the pure hub a **leaf**. The DFS had collected one depth-first subtree,
varying the low-index branches and holding the high-index ones nearly fixed. Reported in the
driver as *not found under cap* and disproved as a nonexistence claim in the same breath.

**Job 3, the reconciliation.** Both readings survive. Route (i) is the **statement**
(certificate 3's uniform form); what *Step G37* killed is the **method** — *"cap + `Λ ≠ ∅`
flip + `D > 0` lift + (GR-4′)"*, whose `g ≤ 1` cap is false from `n_hub = 8`. Calling a
statement a route is what made the cell read as self-contradictory. The close-it cell now
says **targets**, the dead entry is qualified as the *cap + repair* method, and
`Pencil-strategy.md` §8's flag (b) is marked **RESOLVED** (flag (a), the U2/U3 one, stays
open — a different surface, not this direction's). Recorded at *Step G158*.

**Jobs 4/5/6.** Caps travel with every figure (the `n_hub = 4` legs are exhaustive; the
`n_hub = 6` control is capped and says so; `n_hub ≥ 8` is unswept). The `Λ ≠ ∅` caveat is
restated at *Step G158* and **not closed** — (GR-16)(iii)'s merging is the first thing that
breaks (GR-134)'s class/list bijection. **TERMINATION, read at source in
`notes/Pencil-fanout-archive.md`:** **E1 does NOT fire**, decided in its literal reading —
`§(K-grid)` is E1's habitat, a g-flank is a `D = 0` shape whose *every admissible colouring*
is binding, and the one object that looked like one is refuted in the same step by 60
certificates. **E2 does NOT fire** (target not refuted; three successors named). **E3 does
NOT fire** (the arc's target is not proven; (GR-10)/(GR-15) unchanged).

**On the coordinator's reading: SPLIT** (`RESEARCH-ARC.md` §7's second kind). Its *shape* is
**confirmed and is now a theorem** — the `ℓ = 2` case is an orientation problem, exactly as
described. Two of its three self-declared error bars land: expectation (1) is **right** (the
forced label does depend on `β`, and (GR-135) is precisely when that agreement is
satisfiable); expectation (3) is **wrong in a useful direction** — (a) is not an extra
burden, it is **free**, for the structural reason that the six parts are spanning trees. The
reading's implicit hope, that the residual is a union of per-hub conditions, is **refuted at
82 %** of the infeasible pairs. The audit expectation the spec attached to job 2 — that the
population never presents the conflict — is **refuted outright** by the first measurement the
dispatch made; the tally on coordinator predictions moves to **twelve instances**, no new
kind (this is a *refuted* one and a *split* one).

**F21 — the corpus's biggest row, recomputed to an explicit target.** `(K-grid)`: **2 500 →
2 528** status words against the `SPECIAL_CAPS` cap **2 715**, close-it **980 → 949 / 985**,
both under a target set before the edit (status ≤ 2 530, close-it ≤ 950). The status target
is honest rather than generous **because no landing is queued on this row** — the concurrent
sibling is on `(K-bare)` — and the compression behind it is real: **135 words removed from
nine already-landed entries before one word of new content was added**. **No `SPECIAL_CAPS`
entry proposed and none needed** — *no overflow, no bump*. Label preservation by
`python3 notes/scripts/gapdiff.py K-grid`: **141 codes in, 146 out, ZERO dropped, 5 added**.
Column 2's step range `G0–G153` → `G0–G158` in the same edit. One **stale claim corrected in
passing** (`RESEARCH-ARC.md` §3): the status cell still said (GR-108) is refuted *"from
`n = 16`"* and *"the half-witness clause survives"* — both superseded in the body by
(GR-122)/(GR-123) and now fixed in the row; the body prose was grepped and is already
correct.

**Reservation consumed in full**; nothing returned. Labels (GR-134)–(GR-138), *Steps
G154–G158*, driver at the reserved path; the tail declared for the next reservation is
**(GR-139) / Step G159**. **(L6) landing grep:** no bare `(X<digit>)` token is minted — the
new objects are `α`, `γ`, `P_β`, `Q_β` and the words *pure hub* / *cross* / *leaf-covering*,
all unlettered; *Step G21*'s `A(β)`, `C_β`, `D_β`, `J`, `Ĝ` and *Step G149*'s `σ(F)` are
reused, nothing re-minted.

**Cost.** `--support` 4 s, `--local` 2 s, `--csp` 105 s, `--rich` 320 s, `--validate` **530
s** — inside the 600 s foreground budget. Harness debt: `glist.py` is the **second consumer**
of `gpack.py`'s `all_packings` / `csets` / `legal_splits` / `csp_witness` / `shape_rows`, so
§2 rule 2's move-down trigger fires; recorded **UNPAID** in `notes/scripts/README.md`, with
the reason (moving them would re-baseline `gpack.py`'s recorded figures for a single
consumer).

**Successors this direction names**, in its own ranking: (1) **the global `(α, γ)` CSP at
`D = 0`** — the 82 % says a proof must charge something global, and the two handles are the
**constructive** certificate side and (GR-129)(iii)'s closed-form description of the exchange
freedom; (2) **`n_hub = 6` exhaustively** — `all_packings` is ~10⁴ partitions per shape at
`n_hub = 4` and out of reach at `m = 9`, so the 2 623 pure-hub shapes there are undecided;
(3) **leaf-covering as a packing question on its own terms**, the one place the landed
Phase-12/13/14 matroid-union machinery might reach, as §(K-slide-comb) (C6) remark (c)
reaches (GR-130).

## BPROPER — sixty-ninth ordinal (single dispatch, **DRAFT-ONLY**, run 2026-09-02 in parallel with GLIST) — the class-statement lane

**Selection provenance.** (BE-113)(i) item 1 **designated this target in its own words** —
*"That is the successor's target, and it is a **class** statement, not a hunt"* — after the
clause it protects had been refuted and repaired **three directions running** ((BE-99)
BDOUBLE, (BE-105) BSATUR, (BE-109) BSIGMA), every one of them **SLACK, not a shortfall**
(0 shortfalls at 300 / 260 / 78 rows) and every repair **free**, because (BE-14) is
existential ((BE-16)), the good locus is dense on an irreducible chart ((BE-69)) and `reach`
is lower-semicontinuous. Three free repairs is a signal that the object wants **proving**,
not repairing a fourth time. Run **draft-only** beside a committing dispatch — the second
exercise of `RESEARCH-ARC.md` §2's serial-landing pattern outside a prepared fan-out, and
the second concurrent pair of the arc — at **`recon-opus`**.

### The spec, as dispatched

**Target.** Prove (PENCIL-SATURATES-CHART): that the `Σ_x ⊆ ρ̄_i` locus is a **proper**
subvariety of `Chart(H)` at a **non-path** side. A class statement; any sweep is an
**adversarial control** on an argument, not the deliverable.

**Priced in advance, both ways.** A proof closes item 1 of half (B)'s four residuals. A
refutation costs the redundancy theorem's hypothesis (`Π_x`/`Π_y` back among the live
blocks, 12 → 14) but by (BE-113)(iv)'s own accounting does **not** refute
`PencilPair K 3 G`, `hbareSplit`, (BE-14), the 2-cut step or half (B).

**The coordinator's reading, labelled TO BE TESTED.** *The corank identity is
structure-free; what the path proof consumes is the `dim⟨L_j⟩ ∈ {0,1}` case analysis, so
properness off paths needs no new identity — only a replacement for `assert_generic_star`'s
role at a vertex of degree `≥ 2`.* Evidence stratum named honestly in the spec: *a reading
of (BE-110)'s proof text, no measurement, no driver.*

**Forced jobs.** (1) a class statement, not a hunt; (2) the `RESEARCH-ARC.md` §4
sampler-support audit, naming each population's support and which of the claim's own
variables it varies — the direction's direct inheritance, since BSIGMA's own cap was that
its planted stratum reached only paths; (3) measure the `deg_i(x) ≥ 2` shape ((BE-113)'s
price (d)), unmeasured anywhere; (4) a shortfall control on every exhibited row; (5) cap
disclosure; (6) E1/E2/E3 read at source.

**Bars.** Draft-only, no tracked file touched; do not touch `notes/Pencil-informal-grid.md`
or any `(GR-…)` label; do not re-open BSATUR's or BSIGMA's landings; (K-res) is a **USER
call**; the 2026-08-05 Lean hold binds.

### LANDING WRITE-UP — BPROPER, 2026-09-02: **the properness half is settled at every side, and two hunt verdicts fall with it**

**THE TARGET'S PROPERNESS HALF IS SETTLED, and the argument is side-topology-free.** At a
terminal with `deg_i(x) = 1` and side neighbour `c`, the pendant edge carries a **free
multiplier** — `kbare_common.build_rigidity` emits `perp_basis(C_e)` as `+wv` at `u` and
`−wv` at `w`, i.e. exactly `m(u) − m(w) ∈ ⟨C_e⟩`, so the single hinge `xc` is the only
constraint on `x` — hence `ρ̄_i = ⟨p_x ∧ p_c⟩ + A` with `A = ρ̄(side_i − x; c, y)` a function
of the **core points alone** ((BE-114)). Because `p_x ∧ p_c ∈ Σ_x`, the intersection splits
exactly: `dim(ρ̄_i ∩ Σ_x) = dim(A ∩ Σ_x) + [ℓ ∉ A]` and `ρ_i = dim A + [ℓ ∉ A]`, so the bad
condition is **two conditions on `p_x` against a FIXED subspace**. Both cut out a proper
subvariety of the plane `π_c` the pencil condition confines `p_x` to — `Σ_p ⊆ A` because
three α-planes over a plane already span `Λ²K⁴`, and `dim(A ∩ Σ_p) ≥ 2` by an incidence
count on `{(p, ℓ) : p ∈ ℓ ∈ P(A) ∩ Q}` whose **one** exception `Λ²π_c ⊆ A` is **neutralized
by `p_c ∈ π_c`**, which puts the row in the other branch ((BE-115), (BE-116)). **No
`dim⟨L_j⟩` case analysis, no `assert_generic_star`, no path hypothesis.**

**SCOPE, stated exactly as the caps allow and never widened.** What is settled is the
**properness half**, **proven-informally modulo one MEASURED input** — that `p_x` genuinely
sweeps its fibre inside `Chart(H)` with the core fixed. The passage from *proper* to
*generic* **cites (BE-69) rather than re-deriving it** for this locus, and `a_i = 0` at a
generic configuration is likewise measured. **(PENCIL-SATURATES-CHART) is therefore NOT yet
a theorem and half (B)'s item 1 is NOT closed** ((BE-116)(ii)/(iii), (BE-121)(i)).

**Properness exercised ON the bad locus, not by failing to find it.** At **96** planted bad
rows over **16** topologies, `p_x` was swept over its actual chart freedom with the core —
hence `A` — held fixed: a good `p_x` at **96/96**, and **0** of ~1 500 swept points bad. The
planted `p_x` is asserted to be in its own fibre and to be bad, so what is measured is a
**nonempty** proper subset.

**AND THE PREDECESSOR'S CAP WAS A SAMPLER ARTEFACT, located at one line.** BSIGMA's planted
sampler gave a hub inside the planted plane a *random* flag and then intersected it with the
plane, forcing that hub's neighbours onto a **line** and failing `assert_generic_star`. Give
the hub the planted plane itself and the obstruction disappears: **16 of 16** bucket-A
topologies drawable (BSIGMA: 5 of 16), firing at **11**, **eight of them not paths** —
cycles, thetas and a subdivided `K₄` ((BE-117)). The mechanism off paths is *simpler*: `A`
collapses onto `Λ²π` exactly, giving `(ρ_i, dim, dim A) = (4,3,3)` against the path's
`(5,3,4)`.

**AND THE `ρ_i ≤ 4` HUNT VERDICT IS REFUTED BY WITNESS.** On a constructed peel — a non-path
bucket-A side glued at two **non-adjacent** hubs of a subdivided `K₃₃` or prism, so side 2 is
R-node-shaped — **21 rows** carry `Σ_x ⊆ ρ̄₁` at **`ρ₁ = 4`** with `deg₁(x) = deg₁(y) = 1`,
both gates, and **`flag_frame` non-`None`** ((BE-118)). (BE-110)(ii) is a **path theorem**
and is untouched; what falls is (BE-110)(iv)'s *none found at 668 rows*, which (BE-113)'s own
*What would change this* had named. Its structural reading — that `deg_i(y)` is the regime
gate — is **confirmed** by the witness.

**price (d) MEASURED for the first time, and half settled.** At `deg_i(x) ≥ 2` the same
inclusion survives (delete all but one edge at `x` — that only adds motions), so
`Σ_x ⊆ ρ̄_i` still forces `dim(A ∩ Σ_x) ≥ 2`, which (BE-115) makes proper whenever
`dim A ≤ 4`: **91 rows over 16 topologies, `dim A ≤ 3` at every one**, `Σ_x ⊆ ρ̄_i` with
`ρ_i ≤ 5` **not found under that cap** ((BE-119)).

**THE PRICE IS PAID DOWN, and the distinction matters.** `margin ≤ 0` at `Π_x`, `Π_y` and
`⟨M⟩` at **all 21** rows — so `notes/Phase39.md` item 0(c)'s `Π_x` shortfall is **not**
exhibited and **stays open** — and `⟨M⟩`'s both-sides shape stays empty, taking (BE-108)'s
denominator to **93**. What the non-path rows *do* break is `U = Λ²K⁴`, because **planting
off a path costs `a_i ≥ 1`** (a path is a tree, so `a_i = 0` identically; off paths the flat
core gains motions): 15 of 21 rows carry `a₁+a₂ > max(0, 6−δ₁−δ₂)`, the **first exhibited
inhabitants** of (BE-101)(iii)'s live non-attaining block and of the shape BDOUBLE's own
*What would change this* named ((BE-120)). **F13 control**: the same seven graphs drawn
**freely** give `a = (0,0)`, `dim(ρ̄₁ ∩ Σ_x) = 1` and **attain** — so this is a fact about
the stratum, not the graph, and (BE-14) is existential.

**THE COORDINATOR'S READING: SPLIT** — the arc's second. Its first half (*what the path
proof consumes is the `L_j` analysis*) is **confirmed and load-bearing**; its second half
(*replace `assert_generic_star`'s role at degree `≥ 2`*) is **MOOT**, `RESEARCH-ARC.md` §7's
fourth kind: no replacement was needed and no `L_j` analysis was run. Escape-clause item 1 is
**refuted**, item 2 (*is irreducibility available off paths?*) is **vindicated and promoted
to the residual**, item 3 is **confirmed but relocated** — `deg_i(y)` matters only through
the regime gate. **Tally: twelve instances, seven kinds.**

**E-rider: none of E1/E2/E3 fires**, read at source with `:1700`'s two-conjunct E3. What is
refuted is two **hunt verdicts**, not the arc's target; dispatchable attacks are named.

**Driver** `notes/scripts/w4/bproper.py`, eight modes
(`reduce | alpha | proper | plant | peel | degx | support | validate`), exact ℚ, seed
`20260902`, every headline an `assert`.

### Coordinator note on the landing — two concurrency findings, both new to `RESEARCH-ARC.md` §2

§2 today covers **tracked-file** contention only, and both of this round's findings sit
outside it.

**1. A draft-only dispatch must diff against `HEAD`, never against the working tree.**
BPROPER did this correctly for the gap map (`gapdiff.py K-bare HEAD`, which is why that work
needed no redoing) and **incorrectly** for the phase note: it read `notes/Phase39.md`'s line
and status-word counts off GLIST's **uncommitted** edits and reported them as landed state.
Re-measured after GLIST committed as `cadfc1f3`, the real figures were 565 lines / 487 status
words — close enough that nothing broke, which is precisely why the habit is the risk rather
than this instance.

**2. The session scratchpad is SHARED between concurrent dispatches.** Both directions wrote
working files into the same directory, and generic names collided — GLIST reported two of its
own overwritten, and BPROPER's `closeit.txt` was overwritten by a sibling. **Nothing was
corrupted here only because** BPROPER's row-assembly chain re-derives everything from a
single file that was re-verified byte-identical to `HEAD` immediately before use. The rule
both findings share: **prefix every scratch file with the direction code**, and **re-verify
any scratch input against `HEAD` before consuming it**.

---

## OWALL — seventieth ordinal (**DRAFT-ONLY**, third dispatch of a three-way concurrent round, run 2026-09-02) — (OC-44)(iii), the wall-avoiding colouring existence question

**Selection provenance.** Rank 3 of `notes/Pencil-strategy.md` §8's corrected
`hK` ranking, dispatched as the **third** member of a concurrent round: one
committing dispatch live in `notes/Pencil-informal-grid.md` §(K-grid), a second
draft-only one in `notes/Pencil-informal.md` §(K-bare-ext), and this one. Three
concurrent directions on one working tree is the widest exercise of
`RESEARCH-ARC.md` §2 outside a prepared fan-out; it landed with zero collisions.

**Why this row, and the reason is new.** GPACK's job 2 ((GR-133)) established
that a (GR-15) HIT buys `hK` on the **tight stratum only**; the remainder of
`hK`'s habitat is owned but not free, and `§(K-res)/(RS-5)`/(RS-6) route it to
the **escape route**, whose gap-map rows — (K-Λ), (K-wit), (K-pitch), (K-out),
(K-dom) — are all live. §(K-out) is that route's largest live row, and
(OC-44)(iii) was its newest named residual.

Run at **`recon-opus`**.

### The spec, as dispatched

**Target.** (OC-44)(iii): *"every certified class (every tight class shape)
admits a certificate colouring with no single-class `b`–`c` `X`-path and with
generic-draw `rank(Q|_D) = 3`"*. Prove it, refute it, or reduce it to a named
strictly-smaller condition. **The deliverable must be an ARGUMENT**, with any
search demoted to an adversarial control (§2.2's standing do-not-do for the
lane: *"a search does not carry a reason"*).

**Forced jobs.** (1) State plainly which of theorem / refuted / reduced.
(2) The **sampler-support audit** (`RESEARCH-ARC.md` §4's 2026-09-02
sharpening) with an exact target: (OC-44)(iii)'s 174/174 went *"never past the
fourth certificate colouring"* — name that population's support, say how many
admissible certificate colourings each rank-2 class actually has, and whether
the enumeration order is adversarial or incidental. (3) Decide the **second
confinement's status** (attack (4)) and whether *Step O41*'s `≥ 4`-class
cycle-relation mechanism survives contact. (4) The **duplicate check** (F20)
against the concurrent §(K-grid) exchange lane. (5) **Cap disclosure**.
(6) **E-riders E1/E2/E3**, read at source.

**The coordinator's reading, labelled TO BE TESTED** (`RESEARCH-ARC.md` §7):
*the wall is a connectivity event on a single class and certificate colourings
carry tree-triple exchange freedom, so the natural proof is attack (2) — given a
walled colouring, exchange along the tree-triple to break the single-class
path.* Evidence stratum named honestly in the spec: the coordinator's reading of
*Step O41*'s text, no measurement, no driver, neither the exchange machinery nor
the (OC-42) derivation read. Three "where I expect to be wrong" items, the first
being *the 20 non-walled rank-2 classes are probably the real obstruction, so
attack (2) alone may upgrade nothing*.

**Bars.** Draft-only, no commit, no tracked file touched. Do not touch
`notes/Pencil-informal-grid.md`, §(K-grid) or any `(GR-…)` label; do not touch
§(K-bare-ext) or any `(BE-…)` label. Class-uniform input (a) and (GR-15) out of
scope. Do not re-open §(K-out)'s settled batch, do not re-run the
`{σ > 0}`-everywhere hunt, do not work the (a′)/(b′) ledger; **(K-res) is a
USER call**; the 2026-08-05 Lean hold binds.

### LANDING WRITE-UP — OWALL, 2026-09-02: **the named route is refuted as a matter of LOGIC, (OC-44)(iii) is REDUCED, and (Z) accounts for 19 of the 20 second-confinement points**

**Verdict: REDUCED to a named strictly-smaller condition** — the third of the
spec's three options, and the reduction is to a statement with **no geometry in
it at all**.

**The enabling theorem, and it is the pass's real content.** (OC-50): at a
σ-fixed grid chart point the whole (a₁) criterion — target rank of `G`,
`dim D = 3`, the forced `(1,2)` profile, `Q(g)`, `Gram_B(D_Y)`, `rank(Q|_D)` —
is computed by **two direction networks in `K³`** with conic directions
`A(s) = (1,s,s²)`, under a symbol dictionary in which `B` is the apolarity
pairing and **`Q` is the discriminant**. No Plücker, no `ℚ(i)`, no rigidity
matrix of `G`. The landed `closure.ruling_A_line` is the image of `(1,s,s²)`
under a fixed invertible matrix in the *same* affine parameter and `pitch.Q`
pulls back to `−8Q`, so this is not an analogue — it is the same object in a
`ℚ`-rational basis. **Control:** `--agree` reruns `oqrank.point_at` unmodified,
at OQRANK's own seed and draw order, beside the model, and requires every clause
equal — **72 standing points over 36 colourings at 12 classes**, all equal.

**The second confinement, 19 of 20 ACCOUNTED FOR.** (OC-51)(v), the **`≤ 3`-class vanishing
rule**: a cycle-space element touching at most three distinct classes forces
every per-class sum to vanish (three distinct Veronese points are independent,
(FR-2)(ii)), so *coefficients are forced to zero*, nodes are **welded**, and the
(OC-42) wall becomes visible on the contracted network. At the first certificate
colouring per class the census returns **131 good / 7 wall / 19 (Z) / 17
no-standing-draw**: the wall side matches OQRANK's 7 exactly (the same `K4+par`
shapes at split 5) and **every one of the 19 is the wall after the weld** — so
**(Z) accounts for 19 of OQRANK's 20**, not for all 20. The populations are
**not directly comparable** (this leg stops at the first certificate colouring
and reports 17 no-standing-draw classes, which OQRANK's figure has no bucket
for), so the one unmatched class is recorded as **unaccounted for**, not as a
second mechanism; a matched re-run would settle it and was not run. *Step O41*'s
guess — *"a value-level cancellation through a `≥ 4`-class cycle relation"* — is
**INVERTED**: a `≥ 4`-class cycle is where a nonzero relation *lives*; `≤ 3`-class
cycles are what *kill* coefficients.

**A second new mechanism, proven and (honestly) unrealized here.** (OC-51)(iv),
the **monochromatic cut**: if `b` and `c` fall in different components of `H`
minus one `X`-class's edges, then `g` is confined to that class's ruling line —
a Kirchhoff-flow/apolarity proof, dual to the wall's path argument, neither
implying the other. It fires **38 times alone** in a 20 000-network synthetic
control and **zero times** anywhere in the class-shape population. Reported as a
theorem with no realizations, not as a mechanism.

**THE NAMED ROUTE IS REFUTED, and by logic rather than by measurement.**
(OC-52): (OC-44)(iii)'s wall-avoidance conjunct is **implied by** its
`rank(Q|_D) = 3` conjunct — a rank-3 colouring cannot be walled, by (OC-42)(ii)
itself. So *Step O41*'s attack (2), a tree-triple exchange breaking the
single-class connectivity, proves a **consequence** of the target and can never
prove the target. This is the coordinator's own *"where I expect to be wrong"*
item 1, **vindicated and strengthened**: not "the 20 are probably the real
obstruction" but "the conjunct the route addresses is redundant". Quantified:
**252 of 2 340** confined colourings at the pinned splits are unwalled, and
**380 of 672** over the wider split population — at the non-pinned splits the
(OC-42) wall as stated is the **minority** mechanism.

**THE COORDINATOR'S READING, classified — and the tally was reconciled at
landing.** `RESEARCH-ARC.md` §7's *"eight instances and seven kinds"* was **stale
by six** when this direction was dispatched: the live count entering this round
was **eleven** ((BE-113)(iii), BSIGMA), and three concurrent directions then each
incremented a **shared counter** from whatever baseline they happened to read —
GLIST landed "twelve" and BPROPER landed "twelve", claiming the same slot. The
coordinator reconciled it on the cross-return pass and lands the repair of
`RESEARCH-ARC.md` §7 and the other surfaces as a **separate commit**; the
historical per-direction figures elsewhere in this file are correct as of their
own landings and stay. **OWALL is the FOURTEENTH instance, seven kinds**
(eleven before the round; GLIST twelfth, BPROPER thirteenth). Its kind is
**5 — *refuted with its own named escape clause vindicated*** (the BONEONE
kind), with a sharpening: the spec's escape item 1 (*"the 20 non-walled classes
are probably the real obstruction, so attack (2) may upgrade nothing"*) was right
for a **stronger reason than it stated** — the conjunct the route addresses is
*logically redundant* ((OC-52)), not merely insufficient. Item 2 (*does a
tree-triple exchange preserve admissibility?*) is **MOOT**: the route dies before
that question is reached. Item 3 (*the 174/174 may not be evidence for existence
given the cap*) is **REFUTED**: for an *existence* claim a successful capped
search is full strength at the instances it sampled, and removing the cap
entirely confirms 174/174 with 5 920 good colourings. **This instance is also the
first evidence that §7's own counter is a shared mutable surface a concurrent
round can double-claim** — a hazard of the fan-out shape, not of any direction.

**THE SAMPLER-SUPPORT AUDIT (forced job 2), answered with the cap removed.**
The landed 174/174 ran the *first `≤ 6`* certificate colourings in
`grid.colourings` enumeration order — a bit-vector order over branch phases,
i.e. **incidental, not adversarial**. This pass enumerates **every** admissible
colouring of every shape (`2^{branches}`, 8–1024; `COL_CAP = 2^16` never
approached) and keeps every one carrying (GR-9) certificates: **8 514
certificate colourings**, 4–196 per class. Result: **(OC-44)(iii) holds
174/174 with no colouring cap**, with **never fewer than four good colourings**
at a class and the first certificate colouring already good at **131 of 174** —
so *"never past the fourth"* is **explained, not lucky**. Two support holes
remain and are named: the **174 classes** are a bounded stratum while *"every
tight class shape"* is infinite (§(K-ind) (I4)); and the **split** — (a₁) is
needed at every (shape, split) and `oschu.out_classes` pins one. Run at **every**
eligible split of 20 classes — **98 (shape, split) pairs** — the answer is
**98/98**, and the mechanism split flips (raw wall 292, (Z) 376). For an
*existence* claim a successful capped search is full strength at the instances
sampled, which is why the cap never weakened the 174/174; what it hid was the
**denominator**, and that is what this pass supplies.

**What is left.** **(OW)**: *every tight class shape, at every eligible split,
admits an admissible colouring carrying both-block tree-triples whose block
network leaves `βγ` independent, for every `X`-class, in the class-parametrized
direction-network matroid.* Decidable per colouring by an O(1) rank test, so
(OC-44)(iii) is now **decidable by enumeration at any given shape** — attack
(4)'s operational goal, delivered. A **connectivity** characterization is not
delivered: (W)/(C)/(Z) certify **2 336 of 2 340** confined colourings; the
4-case residue is a matroid-**closure** event (a node set carrying a constant
flex with **no rigid subnetwork** witnessing it), all on `V5e10`.

**F20 DUPLICATE CHECK — one convergence, no duplication.** The argument rests on
Veronese independence and Kirchhoff duality, **not** on any colouring-exchange
lemma, so it does not re-derive the concurrent §(K-grid) lane's object under an
`(OC-…)` label. Two honest convergences are recorded instead. *(a)* **(OW) is in
the same object class as (GR-10)** — a partition-constrained existence statement
over admissible colourings — and **(OW)(a) *is* (GR-10)'s certificate
condition**. Stated plainly, because it connects this lane to the one GLIST
landed the same day: **a (GR-10) min-max would be *consumed* by (OW), not
duplicated by it** — (OW) is (GR-10) plus one extra independence clause about a
single distinguished pair — **but (OC-52) shows a colouring *exchange* alone
cannot settle that extra clause**, so the (GR-10) route buys (OW)(a) and leaves
(OW)(b) exactly where it is. This is a cross-return finding: only a parallel
round surfaces it. *(b)* **(OC-51)(v)'s proof uses the same Vandermonde/Veronese collapse
that (GR-9)'s own proof uses** — three parameters, a `3 × 3` Vandermonde — cited
to (FR-2)(ii), not re-derived as a new fact.

**Caps, with denominators.** 3 seeded draws per colouring (a `confined` verdict
is a theorem exactly when (W)/(C)/(Z) fires — 2 336/2 340); 174 classes of the
bounded `|V°| ≤ 6` stratum against an infinite class; all eligible splits at 20
of 174 classes; 20 000 synthetic networks yielding 81 target-rank-compatible.
Every "not found" is *not found under cap*.

**E-rider: none of E1/E2/E3 fires**, read at source. **E1** no g-flank — and the
E1-shaped near-miss is named: a shape whose every certificate colouring is
confined would be the route's dead end, and the exhaustive census found the
opposite at 174/174 and 98/98. **E2** the target is reduced, not refuted, with
three named dispatchable successors; what is refuted is a *route*. **E3** the
target is not proven and stays ARMED by GBAL.

**Driver** `notes/scripts/w4/owall.py`, seven modes
(`controls | agree | full | splits | first | synth | validate`), exact `ℚ`, seed
`20260902`, pool **POOL-OW**.

## GGLOB — seventy-first ordinal (concurrent pair with a `(BE-14)` draft-only sibling, prepped 2026-09-02, **LANDED 2026-09-02**) — (GR-138)'s successor 1, the GLOBAL `(α, γ)` CSP at `D = 0`

**Selection provenance.** `notes/Phase39.md`'s own **NEXT CONCRETE TASK** — the `hK` lane's
own named successor, one direction after GLIST, now that its local half is exact and its
residual explicitly global. The **committing** dispatch of a concurrent pair, the sibling
running draft-only on the (BE-14) thread; dispatched **`recon-opus`**.

### The target, stated exactly

From **§(K-grid) *Step G158* ((GR-138)) successor 1**, read at source. At a tight class shape
with `D = 0` and `Λ = ∅`, is the `(α, γ)` CSP of (GR-134) satisfiable for **some** legal
(packing, split) pair? Prove it, refute it with an exhibited shape, or reduce it to a named
strictly-smaller condition. The prep supplied as verified: **(GR-130)** unconditional (neither
packing nor split is ever the obstruction); **(GR-134)** clause (a) **free**; **(GR-135)** the
exact local criterion at a cubic pure hub; **(GR-136)(iii)** the measured negative that makes
the direction necessary — **82 %** of the infeasible legal pairs are hub-locally feasible
everywhere, so **no per-hub repair can close (GR-18)(iii)**; and **(GR-133)**'s price, which
must be restated: a (GR-15) HIT buys `hK` on the **tight** stratum only, the `def > 0` habitat
being **owned** by `§(K-res)` (RS-5)/(RS-6) but not free, and **`Pencil-strategy.md` §2.5 must
never be quoted as supplying freeness**, being a *negative* result.

### The coordinator's reading, offered as a HYPOTHESIS (`RESEARCH-ARC.md` §7)

Named honestly in the spec as *the coordinator's reading of GLIST's landed text, no
measurement, no driver* — and with the note that GLIST had classified the previous reading on
this lane as **SPLIT**. The reading: (GR-136)(iii)'s 82 % says the obstruction is a **global
consistency** phenomenon over the hub graph, and (GR-134) has already reduced the state to one
9-valued variable per hub with constraints supported on **branches** — an **edge-constraint
CSP on `G°`**. Two handles were proposed: **(i)** a **discharging / counting** argument over
the six spanning trees (the leaf-slot count is `3n` against `≤ n` needed, so the demand is not
counting-obstructed); **(ii)** (GR-129)(iii)'s exchange freedom used as a **repair operation**
on a failed assignment rather than as a search space. Three places the spec expected to be
wrong: (1) the constraint may stop being binary/edge-supported once branches of length `≥ 3`
appear; (2) a counting argument that cannot fail is usually one that cannot help — **check the
saturation filter before investing in handle (i)**; (3) the 82 % may not share a single
mechanism, in which case the honest deliverable is a **classification**.

### Forced jobs (reproduced from the spec)

1. **The deliverable is an ARGUMENT, with any search demoted to an adversarial control.**
2. **Apply the option board's two filters explicitly** — growing ground set (§4.6) and
   counting saturation (§2.5, (OC-3)/(OC-37)) — saying which filter each candidate survives.
3. **The sampler-support audit is FORCED** (`RESEARCH-ARC.md` §4): name the support of every
   population and which of the claim's variables it varies; treat any "0 feasible" as a cap
   artifact until disproved (GLIST's own near-miss is one direction old).
4. **Cap disclosure**, travelling with every figure.
5. **TERMINATION riders E1/E2/E3 read at source**, E1 live in its literal reading.
6. **Restate the `Λ ≠ ∅` caveat**; it is not this direction's to close.

**Bars.** No (a′)/(b′) ledger direction; no `§(K-bare-ext)` or `(BE-…)` label (the sibling is
there); no re-derivation of (GR-130) or of (GR-135)'s local classification; **(K-res) is a
user call and the 2026-08-05 Lean hold binds — no `.lean`.**

### Reservation

(`notes/Pencil-labels.md` §"Reserved namespace — direction GGLOB".) Labels
**(GR-139)–(GR-144)**, ***Steps G159–G164***, owning file `notes/Pencil-informal-grid.md`
§(K-grid) — **extends, no new section** — driver `w4/gglob.py`. Opens at exactly the tail
**GLIST declared**. `GGLOB`/`gglob` verified **0-hit** as raw substrings across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` **at `HEAD`, never against the working tree** (the
concurrent sibling leaves it dirty — `RESEARCH-ARC.md` §2's first new hazard); `(GR-140)`–
`(GR-144)` and `G160`–`G164` 0-hit, and the two hits each on `(GR-139)`/`G159` were opened and
confirmed to be **GLIST's tail declaration**, not consumed labels.

### LANDING — GGLOB, 2026-09-02, `recon-opus`

**Verdict: HIT shape 3 — REDUCED to a named strictly-smaller condition, and the reduction is
CSP-FREE — with HIT shape 1 on four named sub-statements, two REFUTED handles, and a
CORRECTION to a landed reading of (GR-136)(iii).** Landed as §(K-grid) *Steps G159–G164*,
labels **(GR-139)–(GR-144)**, driver `notes/scripts/w4/gglob.py` (six modes).

**Job 1, the argument.** Four theorems, one refutation by witness, one measured
classification.

- **(GR-139), the two dual normal forms.** The residual is a **binary** CSP on `G°` with the
  uniform 9-element domain `J × J^c` **at every branch length** — a graph CSP, not a
  hypergraph one — whose length-2 relation is exactly `R_β = (P × Q) ∪ (Q × P)` for the row
  `P = row(a_β)` and column `Q = col(b_β)`: *the branch's cell is MIXED from the two hub
  cells*. Orienting each length-2 branch at its A-end gives `a_β = α(head β)`,
  `b_β = γ(tail β)` and the two identities `T_j ∩ H = {β : α(head β) ≠ j}` (`j ∈ J`) and
  `T_k ∩ H = {β : γ(tail β) ≠ k}` (`k ∈ J^c`). Dually, fixing one **bit per even branch**
  makes the A-side and B-side **decouple** into two independent 3-list-colourings. A
  table-driven solver seeing nothing but one `9 × 9` table per branch, and the boolean dual,
  each reproduce `csp_orient`'s verdict at **472 680/472 680** pairs.
- **(GR-140), the SYNTHESIS theorem — the packing quantifier is ELIMINABLE.**
  `D_β = {α(head β), γ(tail β)}` makes the length-2 half of the packing a **function** of the
  CSP solution (asserted by rebuilding it, identical, at **229 320/229 320** feasible pairs),
  so the only surviving freedom is the `(P_β, Q_β)` choice on the **at most six** long
  branches. Hence *"some legal pair is CSP-feasible"* becomes a CSP-free statement about `H`:
  *orient `H` and 3-colour the hubs twice so that every cycle of `H` carries a head of each
  `α`-colour and a tail of each `γ`-colour*, plus the bookkeeping `Σ_{j∈J} t_j = 2L − 3`,
  `2|H| = 3(n−1) − (2L−3)` — which incidentally re-proves `L ≥ 2` from the packing side.
  **And the price is named: on the `D = 0`, `Λ = ∅` stratum that statement IS (GR-10)**, by
  (GR-18)(ii)+(iii) — so successor 1 was never a slice below (GR-10).
- **(GR-141), the two filters — handle (i) is DEAD.** Every counting identity in sight is an
  identity in the **shape alone**, so it takes the same value on a feasible and an infeasible
  pair; and, one level finer, **96 of 227** hub-local tree-degree profile classes contain both
  a feasible and an infeasible pair, covering **335 520** of the 472 680 pairs. So no charge
  assigned to hubs from their local tree degrees can decide the residual. (GR-140)'s object
  **passes** the growing-ground-set test (index set `V(G°) ∪ E(H)`, per-hub domain the fixed
  9-element grid).
- **(GR-142), the matroid handle is DEAD too.** `{X ⊆ hubs : the branches headed in X form a
  forest}` **fails the exchange axiom**, at an exhibited orientation *induced by a
  CSP-feasible legal pair* of a genuine `D = 0`, `n_hub = 6` class shape. Since (GR-139)(iii)
  makes the `J`-side of the packing exactly this family, the demand is a partition problem
  over a **non-matroid**, and Edmonds/matroid union — what (GR-130) used on the *branch* side,
  and what the landed Phase-12/13/14 subsystem is — does **not** reach the hub side. This is
  (GR-10)'s own *"not yet Edmonds"* remark, one level down and now exhibited.
- **(GR-143), the three-tier classification — and it CORRECTS a landed reading.** Tier 1,
  hub-local: 44 640 of 243 360 (18 %). Tier 2, **propagation-visible**: arc consistency
  **decides** the residual on (GR-132)'s whole population — non-empty closure ⟺ feasible at
  **472 680/472 680**, ≤ 5 rounds — so *all* of (GR-136)(iii)'s 82 % lives there, and every
  minimal core the greedy shrink returns spans a **cycle** of `G°` (198 720/198 720, sizes
  3 and 4). Tier 3, **propagation-invisible**: a **pinned `n_hub = 6` witness** that is
  hub-locally feasible, arc-consistent and infeasible. **(GR-132)'s population cannot present
  tier 3 at all** — so the 82 % measures tier 2, and the genuinely global obstruction first
  exists one hub-count up.

**Job 2, the two filters.** Applied explicitly and *measured*, not asserted — see (GR-141).
Handle (i) dies on **counting saturation**; handle (ii) survives both filters and is
**reframed**: the exchange freedom is not a *repair* operation on a failed assignment, it is
the **synthesis** direction — you do not repair the assignment, you build the packing from it.

**Job 3, the support audit — and it fires on the arc's own headline figure.** Every population
is named with its support: `--form`/`--filter`/`--glob` are exhaustive over (GR-132)'s 12
shapes at `n_hub ∈ {2, 4}` (all partitions × all splits); `--synth`'s `n_hub = 4` leg is
exhaustive over that whole `D = 0` stratum (312 shapes) and its `n_hub = 6` leg is a
**deterministic prefix** of 150 pure-hub shapes out of 2 623; `--tier`'s census is a **seeded**
sweep of 120 shapes. The finding: **the population behind (GR-136)(iii) is blind to tier 3**,
because arc consistency decides it there — exactly the (GR-137) defect one level further out,
and the reason (GR-143) exists.

**The E1 guard, fired deliberately.** A tier-3 witness read as a shape-level claim would be a
g-flank. It is not: the **same shape** carries a CSP-feasible legal pair, exhibited by
`synth_first` in 339 nodes and asserted in the driver. Every shape this direction decided —
312/312 at `n_hub = 4`, 150/150 at the `n_hub = 6` slice — carries one.

**Jobs 4/5/6.** Caps travel with every figure, with denominators (the `--matroid` leg reports
a **witness**, whose search cap is irrelevant to what it claims). **E1 does NOT fire**, decided
in its literal reading over a strictly wider stratum than GLIST swept. **E2 does NOT fire**
(target not refuted; four successors named). **E3 does NOT fire** ((GR-10)/(GR-15) unchanged).
The `Λ ≠ ∅` caveat is restated at *Step G164* and **not closed** — (GR-134)'s class/list
bijection is still the first thing that breaks.

**On the coordinator's reading: SPLIT, with its own escape clause 2 vindicated.** The framing
half — *a binary edge-constraint CSP on the hub graph* — is **confirmed and is now a theorem**
((GR-139)(i)), and its self-declared error bar (1) is **refuted**: the constraint stays binary
at every length. Error bar (2) is **exactly right** and is the reason handle (i) was not
worked: counting saturation kills it, measurably ((GR-141)). Handle (ii) is **reframed** from
*repair* to *synthesis* ((GR-140)). Error bar (3) is **answered**: the 82 % does share one
mechanism — propagation — but the reading that it is *the* global obstruction is **corrected**,
since the genuinely global tier is invisible on that population. **The tally is cited, not
incremented** (`RESEARCH-ARC.md` §7, **fourteen instances, seven kinds** as reconciled by the
coordinator after the previous round); this instance is of the **second kind, *split***, with
the fifth kind's signature — the escape clause did the work.

**F21 — the corpus's biggest row, recomputed to an explicit target.** `(K-grid)`: **2 528 →
2 679** status words against the `SPECIAL_CAPS` cap **2 715**, close-it **949 → 964 / 985**,
both under targets set before the edit (status ≤ 2 680, close-it ≤ 970). Honest rather than
generous **because no landing is queued on this row** — the concurrent sibling is on
`(K-bare)`. Two already-landed clauses were compressed before a word of new content was added,
and the close-it cell's unit 6(iv) was **corrected**, not merely extended: it said the open
half is *"global: 82 % of infeasible pairs are hub-locally invisible"*, which (GR-143) shows
is the propagation-visible tier. Label preservation by
`python3 notes/scripts/gapdiff.py K-grid HEAD`: **146 codes in, 154 out, ZERO dropped, 8
added**. Column 2's step range `G0–G158` → `G0–G164` in the same edit. **No `SPECIAL_CAPS`
entry proposed and none needed.**

**Reservation consumed in full**; nothing returned. Labels (GR-139)–(GR-144), *Steps
G159–G164*, driver at the reserved path; the tail declared for the next reservation is
**(GR-145) / Step G165**. **(L6) landing grep:** the only `(X<digit>)`-shaped token in the new
steps is `(F11)`, the dispatch-log finding code the *Verification* block cites by convention —
no label is minted in that shape; the new objects (the **cell**, *head*/*tail*,
*head-independent*, the three **tiers**) are deliberately unlettered.

**Cost.** `--form` 140 s, `--synth` 195 s, `--filter` 76 s, `--matroid` 3 s, `--glob` 123 s,
`--tier` 110 s. `--validate` is ~650 s and does **not** fit a 600 s foreground budget, so the
landing gate ran **two** foreground invocations — `--form --synth` at **339 s** and
`--filter --matroid --glob --tier` at **305 s** — per `notes/scripts/README.md`'s *Two invocations do not fit* row — the third
recorded instance of that reading. Harness debt: `gglob.py` is the **third consumer** of
`gpack.py`'s `all_packings`/`csets`/`legal_splits`/`csp_witness`/`shape_rows` and the
**second** of `glist.py`'s `csp_orient`/`d0_shapes`/`first_feasible`/`split_data`/`tree_deg`,
so §2 rule 2's move-down trigger fires **twice**; recorded **UNPAID** in
`notes/scripts/README.md` with the same reason GLIST gave (moving them re-baselines two
drivers' recorded figures).

**Successors this direction names**, in its own ranking: (1) **(GR-140)(ii) attacked as a
graph statement** — the CSP is gone, `H` is simple and triangle-free, and a 4-cycle needs at
most one source and one sink to have three heads at all; (2) **`n_hub = 6`, now an engineering
job** — `synth_first` decided 150/150 positively with the node cap never binding, leaving
2 473 of 2 623 to compute; (3) **whether *path* consistency decides at `n_hub = 6`**, where
arc consistency provably does not — the cheapest question that would say how global "global"
really is; (4) **leaf-covering on the branches**, untouched by (GR-142) and still the one place
the landed matroid machinery might reach.

---

## BOPEN — seventy-second ordinal (single dispatch, **DRAFT-ONLY**, run 2026-09-02 in parallel with a committing `(K-grid)` dispatch) — the class-statement lane, one direction after BPROPER

**Selection provenance.** (BE-121)(i) item 1 **designated this target in its
own words** — *"what is left of item 1 is no longer a properness question; it
is the passage from proper to generic, i.e. (BE-69)'s openness for this
specific locus, plus (BE-116)(iii)'s two measured inputs … it is a **chart**
question rather than a **configuration** hunt"* — after BPROPER settled the
properness half at every side. `hbareSplit` is ranked **#1 of the three
carried items by distance to the phase target**; the item is seed-free and
induction-free and discharges `hbareSplit` **and** `PencilPair`'s
unconditional conjunct at once. Run **draft-only** beside a committing
dispatch at **`recon-opus`** — the third exercise of `RESEARCH-ARC.md` §2's
serial-landing pattern outside a prepared fan-out.

### The spec, as dispatched

**Target.** Close half (B)'s item 1 by making **(PENCIL-SATURATES-CHART)** a
theorem: discharge the passage from *proper* to *generic* for the
`Σ_x ⊆ ρ̄_i` locus, plus BPROPER's two measured inputs (the `p_x`-sweep;
`a_i = 0` generically).

**Priced in advance, both ways.** A proof closes item 1. A refutation costs
the redundancy theorem's hypothesis (`Π_x`/`Π_y` back among the live blocks,
12 → 14) but by (BE-121)(iv)'s accounting does **not** refute
`PencilPair K 3 G`, `hbareSplit`, (BE-14), the 2-cut step or half (B).

**The coordinator's reading, labelled TO BE TESTED** (`RESEARCH-ARC.md` §7),
with its stratum named honestly as *a reading of BPROPER's landed caps today;
no measurement, no driver*: *the three gaps are not equally hard, and two may
be corollaries of the pendant reduction — if `Chart(H)` fibres over the core
with `π_c`-fibres, the sweep should follow from the chart's own construction
rather than needing (BE-69) at all; `a_i = 0` generically looks like the
genuinely separate one.* Three *where I expect to be wrong* items: (1) the
chart may not fibre that way; (2) (BE-69) may be stated over a locus of a
different **shape**, in which case the residue is **larger**; (3) `a_i = 0`
may not be provable at this stratum.

**Forced jobs.** (1) a class statement, not a hunt — any sweep is an
adversarial control on an argument; (2) **read (BE-69) at source and report
its actual ambient before using it**, a full result either way; (3) the
`RESEARCH-ARC.md` §4 sampler-support audit, naming each population's support
and which of the claim's own variables it varies — this lane having produced
**three consecutive** claims true wherever the sampler went and false one
quantifier away ((BE-105), (BE-109), (BE-117)); (4) BPROPER's shortfall
control at every exhibited row, with a `margin > 0` row at `Π_x` outranking
the stated target; (5) cap disclosure with denominators; (6) E1/E2/E3 read at
source.

**Bars.** Draft-only, no tracked file touched; do not touch
`notes/Pencil-informal-grid.md` or any `(GR-…)` label; do not re-open
BSATUR's, BSIGMA's or BPROPER's landings; (K-res) is a **USER call**; the
2026-08-05 Lean hold binds. **Two rules new that day**: diff against `HEAD`,
never the working tree; prefix every scratch file with `BOPEN_`.

### LANDING WRITE-UP — BOPEN, 2026-09-02: **item 1 CLOSES at every side-degree-`1` terminal, and the citation it hung on is retired**

**(PENCIL-SATURATES-CHART) IS A THEOREM at every terminal of side-degree `1`**
((BE-127)(i)), which is every instance where the clause has ever failed and
the only regime in which the flag carries freedom at all ((BE-105)(iv)). So
half (B)'s item 1 **closes there**, (BE-101)(i)/(ii) hold with the clause a
theorem rather than a hypothesis, and the `14 → 12` block drop stands at a
generic chart point.

**THE FORCED JOB ANSWERS NEGATIVELY, AND THAT IS THE RESULT THAT MOVES THE
MOST.** (BE-69) read at source: its ambient **is** `Chart(H)` — so the
citation is not `RESEARCH-ARC.md` §7's *INAPPLICABLE* shape — but its **locus**
is `Good = A₁ ∩ A₂ ∩ GP`, the **attainment** locus, and its openness proof is
in its own words *"plain rank **lower** bounds"*. The saturation good locus is
an **upper** bound on an intersection dimension, upper-semicontinuous only on
a constant-`ρ_i` stratum, so **(BE-69)(i) does not transport** ((BE-122)) —
and it need not, because *generic* does not need *open*: the bad locus is a
finite union of rank strata, hence **CONSTRUCTIBLE**, and on an irreducible
variety a constructible set with empty interior is nowhere dense, so fibrewise
properness alone yields a **dense open** good locus ((BE-123)). **The only
thing (BE-69) ever contributed to three landings' arguments is
irreducibility** — which is (CH-1)(a) one level down.

**BOTH MEASURED INPUTS BECOME PROVED.** The `p_x`-**sweep**: in §(K-chart)'s
tower (which (BE-65)(ii) says **is** (BE-64)(ii)'s parametrization, stage for
stage) the defining equations are `n_h · (q_u − q_h) = 0`, and with the core
fixed the **only** one coupling `q_x` to fixed data is `q_x ∈ π_c`, present
exactly when `c` is a hub. So `p_x` ranges over the whole plane `π_c`, resp.
over **all of `𝔸³`** — precisely (BE-116)(i)'s two ambients — with side 2
**rebuilt** rather than perturbed ((BE-124)). And **`a_i = 0` generically IS
(BE-69)(i)'s own open locus `A_i`**: `a_i = dim M_i − 6 − f_i` and (BE-22)(ii)
caps `dim M_i ≥ 6 + f_i`, so `{a_i = 0}` is the max-rank locus — open,
nonempty by **(BE-14) for the side**, which (BE-69)(iii) already calls *"the
2-cut induction's own hypothesis, not a new obligation"* — hence dense
((BE-126)).

**AND A GAP NO LANDING HAD NOTICED IS LOCATED, EXHIBITED AND CLOSED.** The
clause is stated at `Π_x = p_x ∧ π_x`; (BE-116) proves properness of the
strictly smaller `Σ_x ⊆ ρ̄_i`. A **constructed** `A` shows the difference is
real: at a **fixed** flag the `Π_x`-bad set can be the complement of one line
of the `p_x`-plane — dense — while `Σ_x ⊆ ρ̄_i` holds at a **single point**
((BE-125)(iii)). What closes it is a second fibration: rotating `π_x` through
the line `p_x ∨ p_c` leaves `ρ̄_i` **constant** and sweeps `Σ_x`, so a bad
chart point sitting in any **open** set is bad at **every** flag — i.e. lies
in (BE-116)'s locus — **pointwise** ((BE-125)(ii)). Asserted at 16/16 planted
rows (every rotation bad) and 20/20 free rows (none bad), with the unique bad
plane **constructed** at the 4 rows that have one, since no sampled rotation
can reach it ((BE-105)(iii) again).

**BPROPER's ESCAPE ITEM 2 IS SETTLED, in two lines.** *"Is `Chart(H)`'s
irreducibility available at a non-path side?"* — yes, and side topology plays
no role: degrees only drop, so a hub of `H` is a hub of `G` and
`d_h(H) ≤ d_h(G) ≤ 2`; girth and min degree inherit likewise ((BE-123)(iii)),
checked 9/9.

**price (d) is SHARPENED, not just measured.** At `deg_i(x) ≥ 2` the CHART
clause reduces to `p_x ∧ t ∈ A` for `t` on the **fixed line**
`p_{c₁} ∨ p_{c₂}` ((BE-105)(iv) + (BE-114)(iv)), proper under a two-part
condition `(∗)` whose halves are **exactly certifiable** — one is *linear* in
`t`, the other needs a single witness on the line — and which is certified at
**91/91** of BPROPER's own library and seeds ((BE-127)(ii)/(iii)). That
replaces (BE-119)(i)'s `dim A ≤ 4` hypothesis and is **what item 1 is now left
with**.

**THE PRICE IS PAID DOWN.** `margin ≤ 0` at `Π_x`, `Π_y` and `⟨M⟩` at **54**
further rows (27 planted, 27 free), `reach = min(δ₁+δ₂,6)+a₁+a₂` at every free
row, **0 shortfalls** — `notes/Phase39.md` item 0(c) is **untouched and still
open**, for the fourth direction running ((BE-128)(i)). **Nothing is refuted**:
(BE-116) is used verbatim, and what is replaced is a **warrant**
((BE-122)(iii)) and a **hypothesis** ((BE-127)(ii) over (BE-119)(i)).

**THE COORDINATOR'S READING: CONFIRMED**, and its escape item 2 is the
informative one. The main claim — *the chart fibres over the core, so the
sweep follows from the construction and (BE-69) is not needed* — is right in
mechanism and in object. Its second half is **refuted with the sign
inverted**: `a_i = 0` is the **cheapest** of the three, not the separate hard
one. Escape items 1 and 3 are **refuted**; **item 2 SPLITS** — its diagnosis
(*a locus of a different shape, so the citation was never going to work*) is
exactly right, and its consequence (*the residue is larger*) is **inverted**,
because openness was never what "generic" needed. **Tally: cited, not
incremented** — `RESEARCH-ARC.md` §7 stands at **fourteen instances, seven
kinds**, and the coordinator reconciles after the round.

**E-rider: none of E1/E2/E3 fires**, read at source. E3's first conjunct is
the one to state carefully: item 1 is proven at side-degree `1`, but *the
target* in E1–E3 is the **arc's** (`61e046a6`), and (BE-14), `hbareSplit` and
`hK` are untouched; dispatchable entries remain.

**Driver** `notes/scripts/w4/bopen.py`, eight modes
(`hyp | weak | amax | fibre | slide | degx | price | support | validate`),
exact ℚ, seed `20260902`, every headline an `assert`, `validate` 281 s.

## BLINE — seventy-third ordinal (single dispatch, prepped 2026-09-02, **LANDED 2026-09-02**) — BOPEN's own residue: prove or refute `(∗)`

**Selection provenance.** BOPEN designated this target in its own words —
*"a proof of `(∗)`, or a side with `deg_i(x) ≥ 2` violating it … that is now
the whole of item 1"* — and `notes/Phase39.md` *Hand-off* item 0(a) carries
it as half (B)'s **last open sub-item**. `hbareSplit` is ranked **#1 of the
three carried items by distance to the phase target**. Two features made it
the pick over the `hK` lane's queued successor: the item is one **fixed line**
against one **fixed subspace** — the smallest object half (B) has ever been
reduced to — and BOPEN had priced *both* halves of `(∗)` as *exactly
certifiable*, so a decisive answer was cheap either way. Single **committing**
dispatch at **`recon-opus`**; no sibling in flight.

### The spec, as dispatched

**Target.** Prove or refute **§(K-bare-ext) (BE-127)(ii)'s `(∗)`**, quoted
**with its hypotheses** from *Step BE126* and not from a summary: *`Σ_t ⊄ A`
for every `t ∈ L_c`, and `{t ∈ L_c : dim(A ∩ Σ_t) ≥ 2}` is FINITE*, at an
internal R-node peel with `x ≁ y` under (CH-1), `deg_i(x) = k ≥ 2`.

**Priced in advance, both ways.** A proof was priced as *"the clause is a
theorem at every terminal, half (B)'s item 1 CLOSES, `14 → 12` stands
unconditionally generically"*. A refutation was priced as *"re-opens the
side-degree-`≥ 2` stratum with a named mechanism"*. **Both prices were
wrong in the same direction, and the landing says so**: `(∗)` is
**sufficient, not necessary**, so its refutation re-opens nothing that was
closed — it kills a *route* and leaves the clause exactly as open as BOPEN
left it. The correct advance price would have been *"a proof closes item 1;
a refutation costs the arc a route and buys it a successor"*.

**The coordinator's reading, labelled TO BE TESTED** (`RESEARCH-ARC.md` §7),
with its stratum named honestly as *a reading of (BE-127)(iii)'s own reported
figures, nothing else*: *(BE-127)(iii)'s certifying population is
`dim A ∈ {1: 16, 2: 34, 3: 41}`, so every row has `dim A ≤ 3`, while
(BE-127)(ii) claims to be stronger than (BE-119)(i), which needed
`dim A ≤ 4`. If both readings are right the population lies entirely inside
the regime the older criterion already covered, so it is evidence only where
`(∗)` was not needed — and the `Hand-off`'s "subsumes the old `dim A ≥ 5`
item" is a subsumption asserted on a population containing none of the
subsumed cases. The support gap is at `dim A ≥ 4`/`≥ 5` and at rows where `x`
has hub side-neighbours.*

**Forced jobs.** (1) attack `(∗)` as mathematics before assuming measurement
is the only move — the step itself says half one is *linear* in `t` and half
two Zariski-closed; (2) reconcile the surface disagreement between the
gap-map `(K-bare)` row (**two** left items) and *Hand-off* item 0(a)
(**subsumes**); (3) the `RESEARCH-ARC.md` §4 sampler-support audit, naming
each population's support and which of the claim's own variables it varies;
(4) cap disclosure with denominators, *not found under cap C* never
*does not exist*; (5) E1/E2/E3 read at source; (6) do **not** re-report
(BE-127)(iii)'s F13-disclosed never-fired assert as a discovery.

**Bars.** Committing; the 2026-08-05 Lean hold binds (no `.lean`); every
driver run in the **foreground** with an explicit `timeout`; `(∗)` stays a
**marker, not a label**; extend §(K-bare-ext), open no new section.

### LANDING WRITE-UP — BLINE, 2026-09-02: **`(∗)` is DECIDED — a theorem below `dim A = 3`, FALSE from `dim A = 5`, and the route dies with it**

**`(∗)` IS AN EXACT, CASE-FREE CRITERION.** Put `z := p_{c₁} ∧ p_{c₂}`, the
Plücker point of `L_c`, and `W := z^⊥`, the **hyperplane** of lines meeting
`L_c` — which contains every `Σ_t` with `t ∈ L_c`, and contains `z`. Then
`W/⟨z⟩` is canonically `L_c ⊗ (K⁴/L_c)`, a space of `2 × 2` matrices whose
rank-one locus is the Segre quadric, and `Σ_t/⟨z⟩` is its
**column-space-`⟨t⟩` ruling**. Reading `(∗)` there collapses it to three
incidences and nothing else ((BE-129)):

> **`(∗)` HOLDS ⟺ `dim(A ∩ C_{L_c}^⊥) ≤ 3`, AND no `Σ_{t₀}` with `t₀ ∈ L_c`
> lies in `A`, AND no `Λ²π'` with `L_c ⊆ π'` lies in `A`.**

Asserted as an **iff** — in both its case-split and compact forms, against
each other and against the brute-force reading of `(∗)` — at 140 random
`(A, L_c)` across `dim A = 0..6` plus 48 constructed degeneracies.

**HENCE `dim A ≥ 5` REFUTES IT, UNCONDITIONALLY.** `W` is a hyperplane, so
`dim(A ∩ W) ≥ dim A − 1 ≥ 4` and the first clause fails at **every**
configuration, for **every** line, with no genericity anywhere ((BE-130)(i)).
Equivalently: **`(∗)` ⟹ `dim A ≤ 4`.** And the failure is not a lost
certificate but a **dead route**: for every `p` off `L_c`, `p ∧ L_c` is a
2-space inside the 5-space `W`, so it meets `A` — the necessary condition
`p_x ∧ t ∈ A` that (BE-127)(ii) derives from `Π_x ⊆ ρ̄_i` holds at **every
point of `P³`** and excludes nothing ((BE-130)(ii)), asserted at 2 400/2 400
sampled `p_x`. **(BE-127)(ii) dies at exactly the place (BE-119)(i) died.**

**AND `dim A ≤ 2` PROVES IT.** Half one needs `dim A ≥ 3`; half two needs
`A ⊆ Σ_t`, and two distinct `t` on a line share only `⟨z⟩`, so at most one
`t` qualifies ((BE-131)(i)). At `dim A = 3` the only failures are
`A = Σ_{t₀}` (`t₀ ∈ L_c`) and `A = Λ²π'` (`L_c ⊆ π'`) — two **totally
singular** 3-spaces, both proper closed, so **no blind draw can hit either**;
at `dim A = 4` the failure locus is `A ⊆ C_{L_c}^⊥` plus one ruling case
((BE-131)(ii)/(iii)). So the direction **proves `(∗)` on the stratum the arc
has actually sampled and refutes it on the stratum it has not.**

**SO (BE-127)(iii)'s 91/91 IS A COROLLARY, NOT EVIDENCE.** The population is
reproduced here **exactly** and independently — 91 rows,
`dim A ∈ {1: 16, 2: 34, 3: 41}`, 0 hub side-neighbours — and every row's
verdict is **asserted to be decided by a theorem of (BE-131)**: 50 rows by
(i), 41 by (ii) ((BE-132)). BOPEN had disclosed (F13) that the reduction's
*assert* never fired; this landing supplies the reason the **certification**
half is blind too, which was not disclosed because it was not known. The
sampler varies the configuration and never the **core length**, the one
variable `(∗)` is a function of — F11's shape once more.

**AND THE REFUTED STRATUM IS INHABITED, GENERICALLY.** 27 new
`deg_i(x) = 2` sides with **longer cores**, drawn by the sampler
(BE-127)(iii) itself used, each glued into a composite on which (CH-1)'s
three hypotheses, both terminals' hub-ness and side 2's R-node shape are
**asserted 27/27**: `dim A` census `{1: 30, 2: 10, 3: 60, 4: 30, 5: 60,
6: 80}`, and **`(∗)` fails at 142 of 270 rows** ((BE-133)(i)/(ii)). The cores
are **trees**, so `rank R` is constant (asserted `= 5|E|` at every row) and
`dim A` is **lower semicontinuous** — one draw at `dim A = d` certifies
`dim A ≥ d` generically — giving `dim A ≥ 5` at a **generic** chart point of
**14 of the 27** topologies ((BE-133)(iii)). The fairness check passes too:
**109 of the 140** `dim A ≥ 5` rows have `ρ_i ≤ 5`, so the clause is not
vacuous where the route dies ((BE-133)(iv)).

**THE MECHANISM, AND THE SUCCESSOR IT NAMES.** The `(dim A, ρ_i)` census —
`(5,3): 20, (5,4): 10, (5,5): 30, (6,4): 20, (6,5): 29, (6,6): 31` — shows
`ρ_i` running 1 to 3 **below** `dim A`. That is the whole story:
`ρ̄_i ⊆ ⟨ℓ₁⟩ + A` is a **relaxation**, obtained by deleting `xc₂, …, xc_k`,
and at `k ≥ 2` those are exactly the edges that make `x`'s cycle rigid. **The
named successor is the exact `k ≥ 2` reduction that keeps them.**

**TWO FURTHER GAPS, AND NEITHER IS `(∗)`.** (a) There is **no `p_x`-sweep
lemma at `deg_i(x) ≥ 2`**: (BE-124)(i) assumes `deg_i(x) = 1` inside its own
derivation, and at `k ≥ 2` the flag `π_x` is *determined* by `p_x`, so moving
`p_x` moves `π_x` and every side-2 neighbour must be re-placed. (b) *Proper
in `P³`* is not *proper in the fibre*: the fibre is `𝔸³` only when no
side-`i` neighbour of `x` is a hub, and `(∗)` explicitly permits finitely
many `t` with `dim(A ∩ Σ_t) = 2`, each contributing a whole **bad plane** —
12 such `(A, L_c)` are **constructed** with `(∗)` holding ((BE-134)(i)/(ii)).
(BE-127)(iii) could not see (b): it reports **0** hub side-neighbours at all
91 rows. This direction exhibits **90 rows** where `c₁` **is** a hub, on
(CH-1)-legal composites ((BE-134)(iii)). So even a proof of `(∗)` would have
left item 1 **two** steps short, not one.

**WHAT IS *NOT* REFUTED, stated as prominently as what is.**
(PENCIL-SATURATES-CHART) at side-degree `≥ 2` is **still OPEN**: `(∗)` is
sufficient, not necessary, so its failure kills the route and not the clause,
and the clause's own bad condition is **0 of 270** rows — *not found under
this cap*. **(BE-127)(i) is untouched**; so are `PencilPair K 3 G`,
`hbareSplit`, (BE-14), half (B), (BE-116), (BE-119)(i) and **every landed
measurement** — (BE-127)(iii)'s figures are reproduced exactly. No shortfall
is exhibited; item 0(b)/(c) is untouched, for the fifth direction running.

**THE SURFACE DISAGREEMENT IS SETTLED, AND BOTH SURFACES CORRECTED.** The
gap-map `(K-bare)` row's **two** left items and *Hand-off* item 0(a)'s
**"subsumes"** are both wrong, in opposite directions: `(∗)` is FALSE exactly
on (BE-119)'s `dim A ≥ 5`, so it cannot subsume it — and the two are not two
items either. **They are ONE obstruction**, reached by two routes that both
die on it. Both surfaces now say so.

**THE COORDINATOR'S READING: SPLIT, with its parts pointing the same way.**
Its **premise** is confirmed at source; its **middle inference** —
*"(BE-119)(i) already gave properness there"* — is **REFUTED**, because
(BE-119)(i)'s locus is `Σ_x` and (BE-127)(ii)'s is the strictly larger `Π_x`,
a difference (BE-125)(iii) exhibits, so at `dim A ≤ 3` (BE-127)(ii) does
prove something new; its **conclusion** is confirmed for a **stronger** reason
than it gave (a theorem, not merely a covered regime); its **"subsumes"** call
is confirmed as a defect and sharpened from *unsupported* to *false*; and its
**located support gap** is confirmed at both coordinates. **Tally: cited, not
incremented** — `RESEARCH-ARC.md` §7 stands at **sixteen instances, seven
kinds**, and the coordinator reconciles after the round. Offered for that
reconciliation, and explicitly not claimed: a candidate **eighth kind,
UNDERSHOT** — a prediction right in direction and *weaker than the truth*, so
that inheriting rather than testing it would have understated the finding.

**E-rider: none of E1/E2/E3 fires**, read at source. E2's second conjunct is
the one to state carefully: what is refuted is a **route**, not the target,
and the residue — the exact `k ≥ 2` reduction ((BE-133)(iv)) and the sweep
lemma ((BE-134)(i)) — is a named, dispatchable attack.

**Driver** `notes/scripts/w4/bline.py`, six modes
(`classify | five | low | pop | reach | fibre`, plus `validate`), exact ℚ,
seed `20260902`, `validate` ≈ 59 s. **Mathematics** `notes/Pencil-informal.md`
§(K-bare-ext) *Steps BE128–BE134*, labels **(BE-129)–(BE-135)**.

## BDEGTWO — seventy-fourth ordinal (concurrent pair with a **(K-res)** sibling, prepped 2026-09-03, **LANDED 2026-09-03**) — BLINE's own residue: **both** of (BE-134)'s gaps

**Selection provenance.** `hbareSplit` via (BE-14) is the carried item the
phase ranks **#1 by distance to `PencilPair K 3 G`**, and half (B)'s item 1
is where six consecutive directions had gone. The coordinator **read
(BE-134) at source before dispatching** and targeted the **sweep** gap
rather than the hand-off's phrasing — the hand-off called the successor
*"the exact `k ≥ 2` reduction keeping `xc₂…xc_k`"*, a mechanical restate,
while (BE-134)(i) says a proof of `(∗)` would leave item 1 **"two steps
short, not one"** and that *"no lemma in the section covers"* the missing
one. Committing half of a concurrent pair at **`recon-opus`**; the sibling
ran **(K-res)**, sharing no section, label family or driver.

### The spec, as dispatched

**Target.** Settle **(BE-134)(i)** — *there is no `p_x`-sweep at
`deg_i(x) ≥ 2`* — and **(BE-134)(ii)** — *properness in `P³` is not
properness in the fibre* — quoted with their hypotheses and to be read **at
source, not through the spec**. **The deliverable was a verdict on whether
item 1 can close at side-degree `≥ 2` at all**, with a well-evidenced
**negative** named in advance as *"a fully acceptable and valuable
outcome"*.

**NO PREDICTION WAS OFFERED ON THE MATHEMATICS**, deliberately and on the
record: *"yesterday I put three predictions into three specs and all three
were wrong; the useful half each time was naming which section I had not
opened."* What the spec offered instead was an **evidence-stratum
declaration** — (BE-134), (BE-127)(i)/(ii) and (BE-124)(i) read at source;
**(BE-123), (BE-125) and `bline.py fibre` NOT opened** — and one framing
claim, that item 1 is *two* steps short, with the instruction to *"rate the
work by that, not by the hand-off's phrasing"*.

**Forced jobs.** (1) construct the `k ≥ 2` completion or show the
obstruction is real and name it; (2) settle whether a hub-confined fibre can
be protected; (3) `RESEARCH-ARC.md` §4 + its BSATUR sharpening — a driver
per headline sentence, **naming the sampler's support**; (4) §5 cap
disclosure; (5) §8 — every forward-looking item carries its kill condition
and the status row that decides it; (6) §7 — label any route hypothesis and
name its evidence stratum; (7) repair `notes/Pencil-strategy.md` §9's
citation of BLINE as *"Steps BE129–BE135"* (a **label** range, not a step
range).

**Bars.** Committing; the 2026-08-05 Lean hold binds (no `.lean`); every
driver in the **foreground** with an explicit `timeout` parameter; the phase
note at **579 of its 580 cap**, so anything added is paid for by relocation
and **never** a cap bump; diff against `HEAD`, never the working tree;
distinctly-named scratch files; `BSWEEP` **rejected as a code** for naming a
predicted method.

### LANDING WRITE-UP — BDEGTWO, 2026-09-03: **both gaps SETTLED — the sweep EXISTS, fibre-properness is CLOSED-FORM, and what fails at `k ≥ 2` is the ARCHITECTURE, not the clause**

**GAP (i) DISSOLVES.** (BE-134)(i)'s reason for doubting the sweep is that
(BE-124)(ii) *"re-solves `n_x` from a pencil of planes through `q_x ∨ q_c`,
which exists precisely because `π_x` is not yet determined"*. Read against
(CH-2)'s tower that is true and **not load-bearing**: the completion needs a
**nonempty** fibre for `n_x`, and at `k ≥ 2` it gets a *determined* one that
is still **rational** in `q_x` — `n_x = (q_{c₁} − q_x) × (q_{c₂} − q_x)`,
nonzero exactly off the fixed line `q_{c₁} ∨ q_{c₂}` — after which
(BE-124)(ii)'s three stages run **verbatim**, because none of them used the
pencil's *dimension* ((BE-136)(iii)). **411/411** targets over 70 free peel
draws on **35** composites, (CH-1) asserted on all 35 before any target is
drawn, the core asserted unchanged, `π_x` asserted to carry the fixed
side-`i` star, and the fibre asserted unchanged under its own sweep. **So
item 1 was one step short, not two.**

**AND THE FIBRE HAS FOUR SHAPES, NOT THREE.** (BE-136)(ii) reads them off
the tower rather than sampling: with `W := aff⟨q_{c_1},…,q_{c_k}⟩`, the
fibre is `⋂_{hub c_j} π_{c_j}` **minus** `W` when `dim W = 1` and
**intersected with** `W` when `dim W = 2`. `hcard` caps the hub count at 2,
so that is `𝔸³` / the plane `π_{c₁}` / the line `π_{c₁} ∩ π_{c₂}` —
(BE-134)(ii)'s three, **confirmed at source** — plus a fourth at `k ≥ 3`
with the `c_j` non-collinear: the fibre is the plane `π_x` **itself**, along
which `π_x` is **CONSTANT**. All four are realized as legal chart points,
36/18/6/10 peels respectively, the last two on sides built for the purpose
(`wide_library`).

**THE REDUCTION IS UNIFORM IN `k`, WHICH MAKES THE NAMED SUCCESSOR MOOT.**
`Π_x = p_x ∧ L_{jk}` for **every** pair of side-neighbours, so all `C(k,2)`
instances of (BE-127)(ii) are the single condition `Π_x ∩ A ≠ 0`
((BE-137)(i), 288 pairs over 192 configurations). *Keeping* `xc₂, …, xc_k`
therefore buys **nothing** while the object on the right is `A` — the
gap-map row's and *Hand-off* item 0(a)'s named successor is **MOOT as
stated**. Two dividends fall out: (BE-130)(i) becomes a **one-line count**
(`dim(p ∧ L_c) + dim A = 2 + 5 > 6`, no Segre analysis), and the condition
the route actually needs is `Bad ≠ P³`, **strictly weaker** than `(∗)` —
at the **β-ruling** `Λ²π′ ⊆ A` with `L_c ⊆ π′`, `(∗)` fails while `Bad` is
the **proper plane** `π′`. That separation is **invisible to any sampler**
(300 random `(A, L_c)` agree at every draw; both rulings are **built**), and
the recount on BLINE's own 270 rows — reproduced **exactly**, `dim A` census
`{1: 30, 2: 10, 3: 60, 4: 30, 5: 60, 6: 80}`, `(∗)` failing at 142 —
recovers **2** rows and **none** of the 140 where `dim A ≥ 5`. **BLINE's
verdict stands, for a shorter reason.**

**GAP (ii) CLOSES AS A CRITERION, at all four shapes** ((BE-138), each
asserted as an **iff** against an exact identically-vanishing-quadric test,
300 draws apiece with every branch separately planted):

> `π_{c₁} ⊆ Bad ⟺ Bad = P³` or **`Π_{c₁} ⊆ A`**;
> `π_x ⊆ Bad ⟺ dim(A ∩ Λ²π_x) ≥ 2`;
> `M ⊆ Bad ⟺ dim(A ∩ (M ∧ L_c)) ≥ 3` or **`M ∧ t₀ ⊆ A`**, `t₀ ∈ L_c`.

One sentence covers all three: *a fibre is entirely bad exactly when `A`
swallows a **2-dimensional totally singular family adapted to it***, or a
dimension count forces it. That is the same shape as (BE-115)(iii)'s
exception `Λ²π ⊆ A`, which the `k = 1` theorem neutralized with the chart
fact `p_c ∈ π_c`; **no analogous chart fact is available here**.

**AND THAT IS THE HEADLINE: WHAT FAILS AT `k ≥ 2` IS THE ARCHITECTURE.**
The exact structure ((BE-139)(i), a **subspace identity** asserted 162/162)
is `ρ̄_i = span{ s(m) + a(m)ℓ₁ : m ∈ r^{-1}(Π_x) }` with
`r(m) = m(c_1) − m(c_2)` and `s(m) = m(y) − m(c_1)`. At `deg_i(x) = 1` there
is no `r`, the pendant edge's multiplier is **free**, and that is the whole
of (BE-114)(i) — *the free multiplier is not a convenience of the proof, it
is the reason a `p_x`-free subspace exists at all*. At `k ≥ 2` the
multiplier is **determined by the core motion**, and the sharp object
`A_sharp = s(r^{-1}(Π_x))` **moves with `p_x`**. `A` is recovered only by
dropping the constraint — i.e. by (BE-114)(iv)'s edge deletion — so it is
the **unique** `p_x`-free candidate on this route, and (BE-137)(ii) makes it
vacuous wherever `dim A ≥ 5`, which (BE-133)(iii) puts at a *generic* chart
point on 14 of 27 topologies. **So (BE-114)(iii)'s "a condition on a point
against a FIXED subspace" — the technique the whole `deg_i(x) = 1` theorem
rests on — is provably unavailable at `k ≥ 2`** ((BE-139)(iv)).

**THE POSITIVE HALF, AND IT IS THE SUCCESSOR.** `A_sharp` is strictly
smaller than `A` at **89 of 162** rows and has `dim ≤ 4` — where (BE-115)
and (BE-138) have content — at **30** rows carrying `dim A ≥ 5`. So the
sharp object has content **exactly where the relaxation has none**. What it
lacks is `p_x`-freeness, so the successor is a properness statement for the
`p_x`-**varying** locus `{p ∈ F : (p ∧ L_c) ∩ A_sharp(p) ≠ 0}` — bounded-
degree determinantal, decidable per configuration, class-uniformity open.
**That is a change of method, not a further reduction.**

**THE PRICE, AND THE FIRST POPULATION THAT COULD HAVE BROKEN IT.** At the
411 swept **chart** points the clause `Π_x ⊆ ρ̄_i` with `ρ_i ≤ 5` holds at
**0** — *not found under this cap*, taking the standing tally at
side-degree `≥ 2` to **0 of 772**. The relaxed condition holds at 165, and
at **28 of 70** peels at **every** point of the fibre, so there it proves
properness nowhere while the clause is violated nowhere: the quantitative
form of the architectural verdict. At all **96** confined-fibre points the
relaxed condition holds at **none**, so **(BE-134)(ii)'s hazard is not
realized on any chart point here** — its witnesses stay abstract, exactly as
that step disclosed, and this is the first population that could have
contradicted it. `margin ≤ 0` **asserted** at `Π_x`, `Π_y`, `⟨M⟩` on 70
peels, histogram `{−3: 24, −2: 46}`, **0 shortfalls**, so item 0(b)/(c) is
untouched.

**The coordinator's framing, classified** (`RESEARCH-ARC.md` §7): **the
spec withheld a prediction on purpose and substituted an evidence-stratum
declaration, and the stratum half did the work.** Its framing is
**CONFIRMED as to which question to ask** — the two gaps are the right two,
and the hand-off's mechanical-restate reading was wrong — and **REFUTED as
to the count**: one step short, not two. Both unopened sections were
load-bearing: (BE-123)(i)'s constructibility is what makes the architecture
`k`-free, and `bline.py fibre`'s implementation is what showed (BE-134)(ii)'s
witnesses to be abstract rather than chart-realized. The tally is **cited,
not incremented** (the 2026-09-02 concurrent-counter finding); a **ninth
candidate kind, DECLINED-AND-REPLACED**, is offered for the coordinator's
reconciliation, with the honest caveat that it may simply be §7 working.

**Two harness findings.** A **silent** `bimage.span` hazard: it
special-cases width 6 and otherwise round-trips `nullspace(nullspace(·))`,
so it returns **`[]` — dimension 0 — on any full-rank input of width ≠ 6**
(`span(I4)` is `[]`); `bimage.isect` shares it through `perp_std`. It bit
twice while the driver was written, and it is the same family as BLINE's
`pt_in` truncation trap. **New, unpaid**; `bdegtwo.k4span`/`k4meet` are the
guards. And `notes/Pencil-strategy.md`'s two citations of BLINE as *"Steps
BE129–BE135"* — its **label** range — are repaired to *BE128–BE134* and
rolled forward to BDEGTWO's *BE135–BE140*.

**What did NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, (GR-15),
(BE-14), the 2-cut step, half (B) as a whole, class uniformity, cross-pair
welding, (BE-127)(i)'s theorem at side-degree `1`, and **every landed
measurement**. **(PENCIL-SATURATES-CHART) at side-degree `≥ 2` stays OPEN.**
Not a PENCIL event; E1/E2/E3 all decided **not fired** at source.

## RPOOL — the `§(K-res)/(RS-5)` row's two cheap items (arc ordinal 75, 2026-09-03, recon-opus, committing half of a concurrent pair)

### Spec (as dispatched)

The row's *close-it* named, **beside the wave**, a *"cheap first slice"* (the
255-residual pool sweep) and a **flank** (a `def = 0` (K-res) shape whose
*every* admissible colouring has `dim Z > 0`, which would refute (RS-5)).
Both were dispatchable only because of the **2026-09-03 declines-are-not-locks
directive** — the 2026-09-02 decline of the **wave** is a past priority call,
not a bar on its cheap first steps, and `notes/Phase39.md`'s *"nothing
dispatchable left"* was withdrawn with it. **The wave itself was not
re-litigated and remains uncommissioned.** Reservation:
`notes/Pencil-labels.md` §"Reserved namespace — direction RPOOL".

**No coordinator prediction was offered on the mathematics** — the spec said
so explicitly, and named instead which sections the coordinator had *not*
opened (*Steps RS1–RS10*, `resgrid.py`). That instruction — *confirm the
instrument actually does what the row says it does* — is what the direction
paid off first (below).

### Landing write-up (LANDED 2026-09-03)

**Verdict: HIT shape 1 — a named open statement REFUTED by an exhibited
witness**, with a law identifying exactly which members survive. `hK`,
(GR-15), (GR-10), class uniformity, `PencilPair K 3 G`, E1/E2 untouched;
**E3 stays ARMED (by GBAL), not fired** — every rank computed is a σ-fixed
construction, never a composite-guard generic sample. Canonical home:
**§(K-res)**, *Steps RS11–RS16*; driver `notes/scripts/w4/rpool.py`.
Reservation: (RS-11)–(RS-15) consumed, **(RS-16)–(RS-18) returned**, no M2
leaf needed.

**The instrument check came first, and it moved the spec.** The row says
*"`resgrid.py`'s sweep is the instrument"*. Opened at source, `resgrid.py`
has **no pool mode**: all four of its legs are keyed to a hard-coded
`shapes()` = `W19`/`S29`/`NT21c3` plus the θ control. The sweep is reusable
*in shape*, not runnable over the pool — so the slice needed a new driver
(`rpool.py`), which imports `resgrid`'s pieces read-only. Recorded because
the row's own wording would have led a reader to expect a flag.

**(RS-5) IS FALSE.** The witness is **`R20` = `nogood_subdiv.family_g(5,
(0,0,2), (4,4,4))`** — and `widened.W19` **is** `family_g(4, (0,0,2),
(4,4,4))`, asserted, so the flank is **`W19` with a one-edge-longer core**,
sitting inside the recorded 255-shape pool since 2026-08-02. At all **64** of
its admissible both-forest colourings the parameter-free floor **(RS-11)** is
positive, capping the σ-fixed rank at `113 < 114` at *every parameter point*;
measured max `113`, and **no colouring of `R20` whatever** — the 192
monochromatic-hub ones included — reaches `(0,0)`, so the refutation does not
depend on how "admissible" is read. Two independent deficiency oracles agree
on `def = 0`.

**The mechanism is a block split, and it is where (RS-3)(ii) was one
quantifier short.** (RS-11): `h₊ = h₋ = c(G)`, the per-block slacks
`s_± = 3c − m_±` sum to **exactly** `index`, and `dim Z_± ≥ max(0, g_± − s_±)`
— so a `(0,0)` colouring needs **each** block's forced witness covered by
**that block's own** slack. (RS-3)(ii) buys `f(core) ≤ index`, a bound on the
**sum**. `W19`/`S29` escape only because `index = 2` splits `1 + 1`;
`NT21c3`'s `C₆` core forces nothing; `R20` has `W19`'s forced `g = 1` and one
unit of index to split. **Across the pool: 30 of the 102 `def = 0` members
refute (RS-5), 72 satisfy it** — each of the 72 with an *exact rational target
point*, i.e. a per-shape proof, and the proof leg's miss set is asserted equal
to the sweep leg's flank set. **0 undecided, 0 skipped.**

**(RS-15), the covering law:** `flank ⟺ index < 2·g_forced`, no counterexample
at 102 pool members + 51 systematically generated fresh ones (**15 further
proven flanks off the recorded pool**). Cap disclosed: the `random_short`
generator the pool's own third family uses produced **0** in-band residual
`def = 0` shapes in 20 000 draws, which is why the extension is systematic
over the *core* rather than sampled; nothing with `g_forced ≥ 2` or with two
disjoint short cores was reached, so the law's right-hand side is **untested
above `g_forced = 1`**.

**What the wave now costs.** *Step RS9*'s three lines stand and a **fourth**
is added: a positive, **identified** fraction of the `def = 0` habitat is
outside the grid route entirely, joining the deficient fringe (RS-6) already
excluded. The wave is no longer *"prove (RS-5) uniformly"* — that is refuted —
but *"prove the repaired statement uniformly **and** route the
`index < 2·g_forced` members somewhere else"*, and the second half is new work
with **no named home**. The wave stays a **user call**.

**What did NOT move.** `PencilPair K 3 G`, `hK`, `hbareSplit`, (GR-15),
(GR-10), (BE-14), class uniformity, the Lean hold, and every landed
measurement. **(RS-1)–(RS-4) are untouched** — the geometry still transports
verbatim and (RS-4) is still a theorem; what fails is the hypothesis (RS-4)
needs. **(GR-15) is untouched in both directions**: the quantifiers are
disjoint, `R20` refutes `hnoRigid`, and the refutation says nothing about the
tight class. Not a PENCIL event; E1/E2/E3 all decided **not fired** at source.

## BSCOND — seventy-sixth ordinal (single dispatch, prepped 2026-09-03, **LANDED 2026-09-03**) — the ninth strategy pass's rank 1: **(BE-57)(iv)'s two window conditions**

**Selection provenance.** The **ninth strategy-only pass**
(`notes/Pencil-strategy.md` §8, coordinator-authored 2026-09-03) ranked this
**1 of 4**, on all four binding criteria and on its own **rut measurement**:
eleven consecutive (BE-14)-thread landings, **BONEONE (56) through BDEGTWO
(74)**, worked half (B) or a named sibling, while half (β)'s two window
conditions had sat *"open and ranked, not dropped"* since **BWIN (51)** —
24 ordinals — in `notes/Pencil-structure.md` **block 10, entry 3**. The pass
also **barred** `A_sharp` properness as a build until its own rank-2 recon
runs (a fifth attempt at one obstruction), which is why the thread moved
halves rather than continuing. Single dispatch at **`recon-opus`**.

### The spec, as dispatched

**Target.** Prove or refute **(S1)** — *some `δ₁`-attaining middle
configuration has `p_{w₁} ≠ p_{w₂}`* — and **(S2)** — *the meeting-lines
regime is handled by (BE-55)(iii) only when the forced equality is of the
boundary planes; a middle forcing some other algebraic relation between its
boundary flags that pins `λ` onto `W^{⊥K}` would need its own argument* —
both to be **read at source in `notes/Pencil-informal.md` §(K-bare-ext)
before anything else**. *"A refutation is worth as much as a proof — it costs
the window's class theorem its carrier and re-routes (β), the first hard
information on that half since BWIN."*

**The three findings the coordinator supplied, each verified at source by the
coordinator and to be quoted rather than inherited.** (1) **(S1)'s evidence
is exactly the class this arc has twice broken** — *"both samplers reject
coincidence, and every drawn middle satisfies it"* makes the second clause
the reason the third is vacuous, so `RESEARCH-ARC.md` §4's **BSATUR**
sharpening (*name the sampler's support and ask which of the claim's own
variables it varies*) and its **RPOOL** sharpening both apply, with the
instruction to *establish what those two samplers actually reject before
weighting any existing figure*. (2) **(S2) is an asserted absence in the one
section where five claims of that shape have fallen** — (BE-41)(ii),
(BE-66)(iv), (BE-109)(iv), (BE-110)(iv), (BE-134)(i) — so *"no such mechanism
is known"* is *"the sentence to attack, not to record"*. (3) **Nobody has
attacked either**, so there is no prior pass's optimistic residue to build on
and no prior pass's framing to inherit. (4) **What a decision does NOT buy**:
S-mark's other half stays open with the **METHOD** as its obstruction
((BE-139)), and (BE-14) needs both halves.

**Bars.** Committing; the 2026-08-05 Lean hold binds (**no `.lean`**); every
driver in the **foreground** with an explicit `timeout` parameter, one at a
time, never backgrounded (dispatch-log F6); **out of scope as a bar, not a
preference** — no `A_sharp` properness and no further single-clause repair of
(PENCIL-SATURATES-CHART) at side-degree `≥ 2` (§8's rank 2, barred as a build
until its own recon runs); no re-opening of `notes/Pencil-structure.md`
blocks 4/5 or §8.6's durable negatives; the phase note at **574/580 lines**
with its `**Status:**` header at **525/525 words**, so a header edit must be
**word-neutral or negative** and the landing must **merge or rotate rather
than append**; the `(K-bare)` row **recomputed, never bumped**;
`notes/scripts/README.md` *Harness debt* required reading before any
numerics, with **no `Λ²`-side draw through `bimage.pt_in`**. Code **BMID**
was **rejected** at reservation for priming the answer — this registry had
rejected it once already, at BWIN's own reservation.

### LANDING WRITE-UP — BSCOND, 2026-09-03: **BOTH CONDITIONS DECIDED, AND THEY WERE ONE GAP — (S1) IS REMOVABLE, (S2)'s FIRST HALF IS A THEOREM, ITS SECOND HALF IS REFUTED AS STATED AND THEN CLOSED**

**THE TWO CONDITIONS COLLAPSE INTO ONE, BY A TWO-LINE INCIDENCE LEMMA.** The
pencil condition at `u` puts `p_{w₁}` in `π_u` and at `v` puts `p_{w₂}` in
`π_v` — at *every* configuration, since `w₁ ∼ u` and `w₂ ∼ v` are the two
bridges. So `p_{w₁} = p_{w₂}` forces that point onto `L = π_u ∩ π_v`, and the
two leading lines `ℓ_u = p_u ∨ p_{w₁}`, `ℓ_v = p_v ∨ p_{w₂}` **meet** there.
**(S1) failing IS (S2)'s meeting-lines regime**, and (S2)'s feared *"other
algebraic relation between its boundary flags"* is not hypothetical — it is
(S1)'s own failure ((BE-143)). Filing them as two independent side
conditions, one *"checkable per middle"* and one an asserted absence, is what
hid the implication for 24 ordinals.

**(S1) IS REMOVABLE, NOT MERELY TRUE.** (BE-57)(i) invokes `p₁ ≠ p₂` at
exactly one place — *"the boundary lines are skew when `p₁ ≠ p₂` and the
boundary planes differ"*. **(BE-55)(iii)'s proof turns out to be
plane-agnostic**: it is stated for `π₁ = π₂ = π` and instantiated at
`σ = π`, `q = L ∩ π`, but every step needs only *a plane containing both
leading lines with `L` outside it*, and `σ := ℓ_u ∨ ℓ_v` always is one. From
cross-incidence-freeness and `π_u ≠ π_v` alone: `L ⊄ σ`; `q := L ∩ σ` is a
single point; `q` **is** `ℓ_u ∩ ℓ_v` (derived, not assumed — each leading
line meets `L` by (BE-56)(ii), inside `σ`, and `L ∩ σ` is that one point);
`span(ℓ_u ∧ ℓ_v) = Λ²σ`, self-conjugate; and `λ^{⊥K} ∩ Λ²σ = q ∧ σ = Λ_{uv}`
**exactly**, so the rank-one kill step is unchanged ((BE-144)). Delete the
hypothesis and the theorem stands, on the window's own regime.

**AND THE FORCING LIST IS EXHAUSTIVE AT TWO, BY AN ENUMERATION PLUS AN
ARGUMENT.** `ℓ_u`, `ℓ_v` are non-skew **⟺ `L ∩ π₁ = L ∩ π₂` ⟺ `L` meets the
line `π₁ ∩ π₂`** — a Schubert hyperplane section, codimension `1` in the
4-dimensional Grassmannian, asserted equal to the skewness fact at 200/200
draws and hit by **0** of them. Since a dense open is not contained in a
proper closed set, the `(≠, ≠)` cell of the `2 × 2` table over
`(π₁ = π₂?, p₁ = p₂?)` **cannot** force, so forcing requires `π₁ = π₂` or
`p₁ = p₂` and **exactly three of four cells force** ((BE-145)). **(S2)'s
first half is PROVED**, and (BE-55)(iii)'s coverage, read through (BE-144),
is complete. *That an exhaustiveness claim needs an enumeration and not a
sample is §4's rule, applied literally: the table is enumerated, the
impossibility of the fourth cell is argued.*

**(S2)'s SECOND HALF IS REFUTED AS STATED — the mechanism exists and it is
(S1) failing.** At a **free** `L` no middle can pin `λ`: the admissible lines
are a dense open of the Klein quadric `𝒬`, and `𝒬 ∩ P(W^{⊥K})` is proper
closed for `t ≥ 1` because **`𝒬` spans `Λ²K⁴`** — census `{0: 120, 1..5: 0}`
over 120 draws per `t`, with `t = 0` the vacuous corner (BE-56)(iii)'s own
`max` covers. But `p_{w₁} = p_{w₂} = p` forces `L` **through `p`**, a
codimension-2 restriction the free regime never sees; the lines through `p`
span the **self-conjugate** `Σ_p := p ∧ K⁴`, so
**`λ ∈ W^{⊥K}` for every admissible `L` ⟺ `W ⊆ Σ_p`** — asserted as an
equivalence at 60 configurations, with **both branches inhabited by real
window middles**: inside at **16** shape-seeds (the five landed barbells, the
four-branch theta and **both R-node middles**), outside at **4** ((BE-146)).
The generic slice really is defeated there.

**AND IT CLOSES BY A DIMENSION CAP RATHER THAN A REPAIRED GENERICITY — the
COINCIDENCE EXCESS LAW.** `Λ_{uv} ⊆ Σ_p` always at a coincident middle, so
**(a)** `W ⊆ Σ_p` ⟹ `λ` is pinned and `V = W`, but `ρ̄₁ = Λ_{uv} + W ⊆ Σ_p`
**caps `dim ρ̄₁ ≤ 3`**, and then `excess = dim ρ̄₁ − 2 ≤ 1`; **(b)**
`W ⊄ Σ_p` ⟹ some line through `p` pairs nonzero with `W`, so generic
`L ∋ p` restores `dim V = t − 1` and (BE-56)(iii) runs **verbatim**. Either
way `excess ≤ 1` in the window ((BE-147)). Measured exactly: case (a) census
`(dim ρ̄₁, t, excess) ∈ {(2,0,0), (3,1,1), (3,2,1)}` with
`excess = dim ρ̄₁ − 2` at every row; case (b) `(5,3,2)` with `dim V = t − 1`
and the excess law tight. **Corollary worth its own line: `δ₁ = 4` excludes
case (a) outright**, so the window's hardest arithmetic row can only meet the
coincidence regime through case (b), where nothing new is used.

**THE END-TO-END CHECK, AT THE STRATUM THE HYPOTHESIS EXCLUDED.** **100**
coincidence configurations over **20** shape-seeds / **10** shapes, each
through `assert_generic_star` **and** `verify_pencil_witness` with the
coincidence the only repeated point: `dim Z = 4` at **100/100**; the identity
`ρ̄₁ ∩ Z = Λ_{uv}` **and** (b1) at **all 80** rows with `dim ρ̄₁ ≤ 4`; the
identity failing at **all 20** rows with `dim ρ̄₁ = 5`, which (BE-56)(iv)
*requires* ((BE-148)). **Non-vacuous in both directions.** Coincident middles
are built by (BE-48)'s parametrization run **planes-first**: pick the shared
point, then force the plane at every branch vertex whose closed star must
contain it.

**THE SUPPORT AUDIT IS THE COORDINATOR'S FINDING 1, CONFIRMED AND SHARPENED
TWICE.** Read at source: `bearcase.sample_piece_config` and
`bsharp.sample_piece_config_adj` each carry
`if len(set(pt.values())) != len(V): continue`, a **global** pairwise-
distinctness filter — so *"every drawn middle satisfies it"* is the filter.
**Sharpening 1:** `binduc.assert_generic_star`, the guard the sentence most
naturally names, rejects coincidence only on **edges** plus collinearity at
distance `2`, and `dist_C(w₁,w₂) ≥ 3` in the window — so *"both samplers
reject coincidence"* **overstates the guard** while understating the problem.
**Sharpening 2:** `kbare_common.verify_pencil_witness` — the pencil
*predicate* — rejects only adjacent coincidence, so the **mathematics admits
`p_{w₁} = p_{w₂}`**: what the clause called an absence of *forcing* is an
absence of *prohibition*, the opposite claim. And `bwin.resweep` rejects
`rank(L + [p₁,p₂]) ≠ 4`, which `p₁ = p₂` makes unsatisfiable — **0 of 60**
end draws over a constructed coincident middle survived. **Three layers, none
able to produce the case, and (BE-55)(i)'s own honest domain excluding it by
hypothesis** ((BE-142)). The quantitative form: `bwin.full_measure`'s own
`(BE-56)(ii)` assert **fires** at **30 of 100** rows, so the landed
measurement could not have been run where the claim needed testing.

**The coordinator's framing, classified** (`RESEARCH-ARC.md` §7): **all four
findings CONFIRMED, and finding 2's prediction was the one that paid.**
Finding 1 is confirmed and **sharpened twice** (the named guard does not do
the job, and the predicate *admits* the coincidence). Finding 2 — *"no such
mechanism is known" is the sentence to attack* — is **confirmed exactly**:
the mechanism exists, and this is the **sixth** clause of that shape to fall
in this section. Finding 3's *"no framing to inherit"* was right and turned
out to matter in an unforeseen direction: the two conditions were *labelled*
as independent, and the labelling was the obstacle. Finding 4 stands
unmodified — **S-mark's other half is untouched**. What the spec did **not**
predict, and what a refutation-hunting reading of its own framing missed:
the refutation and the proof are the **same object**, so *"a refutation costs
the window's class theorem its carrier"* is wrong twice over — the theorem
comes out **stronger**, with a hypothesis deleted.

**One harness finding, and it is a silent guard-defeat rather than a wrong
answer.** `bwin.dehom` returns a **list** where every sampler in the tree
stores **tuples**: unhashable (so a `len(set(...))` check raises) and, worse,
**unequal to a tuple**, so `assert_generic_star`'s `pt[u] != pt[v]` edge
check silently passes for any edge with one endpoint written by `dehom`.
`bscond.aff` is the local one-line fix. **No landed figure is affected** —
`bwin` writes only the two terminals that way and their distinctness is
separately implied — but a future module writing an interior vertex through
`dehom` would lose the guard. Recorded as a *Recorded observation* rather
than a new debt item, since the fix is one line at the call site. Both
recorded silent hazards (`bimage.pt_in`'s truncation, `bimage.span`'s
width-6 case) were **navigated**, not tripped: no `Λ²`-side draw through
`pt_in`, and every `K⁴` subspace through the pre-existing
`bwin.k4_span`/`k4_isect` — so **no new wrapper is minted**.

**What did NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, (GR-15),
(BE-14), the 2-cut step, **S-mark**, (BE-32)(+), the short-cycle law,
BSHARP's dichotomy, BRULE's separation theorem, (BE-58)(i)–(iv), cross-pair
welding, class uniformity, and **every landed measurement** (BWIN's 358
guarded draws, the 160/160 `cls` census, the 84/84 per-`L` criterion, the
42-draw excess census). **Half (B) at side-degree `≥ 2` stays OPEN with the
METHOD as its obstruction** — closing (S1)/(S2) does **not** close S-mark.
Three landed surfaces are **annotated at source** (per F12): (BE-57)(i)'s
hypothesis list, (BE-55)(iii)'s scope and cap 3, (BE-56)(ii)'s scope; and
(BE-57)(iv) as a whole is **SUPERSEDED**. Not a PENCIL event; E1/E2/E3 all
decided **not fired** at source. **Two labels returned unused**: (BE-149)
and *Step BE148*.

## BARCH — seventy-seventh ordinal (concurrent round of four, prepped 2026-09-03, **LANDED 2026-09-03**) — the ninth strategy pass's **rank 2**: does ANY `p_x`-free-subspace method survive at side-degree `≥ 2`, and is the 12-block residue reachable without the clause?

Workbook home: `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE148–BE154*, labels (BE-149)–(BE-155). Driver `notes/scripts/w4/barch.py` (five modes).

### The spec, as dispatched

Rank 2 of the 2026-09-03 strategy pass, dispatched **as a
recon** and deliberately **not** as *"is `A_sharp` proper"*. Two questions:
**(1)** does **any** `p_x`-free-subspace method survive at
`k = deg_i(x) ≥ 2`, given that BDEGTWO's mechanism makes the pendant
multiplier *free* at `k = 1` and *determined* at `k ≥ 2` so that
`A_sharp` moves with `p_x`; and **(2)** if not, is the 12-block residue
reachable **without** (PENCIL-SATURATES-CHART) at all — can 14 → 12, or the
per-side inequalities, be had by another route at `k ≥ 2`? The spec's motive
was the `/coordinate-phase` **recurring-wall** rule: four
structurally-different attempts (BSATUR, BSIGMA, BLINE, BDEGTWO) hit **one**
named obstruction, each varying the **upstream** construction, so the shared
**downstream** object was to be suspected. §8 barred `A_sharp` properness — and
any further single-clause repair — **as a build** until this recon ran, with
the instruction to **price** `A_sharp` properness as one candidate *inside* the
method question rather than attempt it.

### LANDING WRITE-UP — BARCH, 2026-09-03: **the method class is NOT DEAD — it CHANGES AMBIENT — and 14 → 12 reduces to a strictly weaker TWO-SIDED clause**

**BOTH questions answered, and the expected answer to the first
one is WRONG.**

1. **The method class is NOT dead — it changes ambient.** `s` and `r` are
   **both** `p_x`-free maps on the fixed core motion space, and BDEGTWO used
   only the first. Their graph `Γ ⊆ Λ²K⁴ ⊕ Λ²K⁴` is a **fixed** subspace and
   `ρ̄_i ∩ Π_x = φ_p(Γ ∩ (Π_x ⊕ Π_x))` **exactly** (99/99, asserted as
   subspaces), so the clause **is** a surjectivity statement about `Γ` — a
   condition on the point `p_x` against a **fixed** subspace, which is
   precisely (BE-114)(iii)'s technique. **(BE-139)(iv)'s *"provably
   unavailable at `k ≥ 2`"* is right inside `Λ²K⁴` and OVER-SCOPED as
   written** ((BE-149)).
2. **A second `p_x`-free subspace exists in `Λ²K⁴` itself**:
   `R₀ = r(ker s) ⊆ R = ρ̄(core; c₁, c₂)`, with **BAD ⟹ `ℓ₁ ∈ A` or
   `Π_x ∩ R₀ ≠ 0`**. It certifies GOOD at **every** `dim A ≤ 5` row (63/99,
   sound 63/63) and none at `dim A = 6`. A **general path bound** —
   `ρ̄(H;u,v) ⊆ Σ_P ⟨ℓ_e⟩`, asserted at 99/99 — gives the structural reason
   `A` saturates and `R` does not: `A`'s bound is the distance to the **far**
   terminal, `R`'s the distance between **two neighbours of `x`** ((BE-150)).
3. **The graph condition does what neither can.** `dim Γ_Π(p) ≤ 1` proves
   GOOD; along the fibre it fires on **39 of the 54** configurations where the
   relaxed condition is bad at every swept point — **21 of them at
   `dim A = 6`** ((BE-151)). The residue is class uniformity, not
   decidability.
4. **Question 2, half one: the per-side weakening is DEAD.** Exhaustively over
   6 400 tuples, `(PS-f)` leaves **313/164/74/24/0** escapes at `f = 2..6`, so
   the landed clause is the **weakest per-side member** that works, and
   relaxing to BSATUR's own `ρ_i ≥ 5` still leaves 24 (2 attaining)
   ((BE-152)).
5. **Question 2, half two: a TWO-SIDED clause does it.** **(E4)**
   `c_i(Π_x) = 2 ⟹ e₁+e₂ ≥ 4`, `e_i = ρ_i − c_i(Π_x)`: **0** escapes,
   implied by (PENCIL-SATURATES) (0 counterexamples) and **strictly weaker**
   (970 tuples), (BE-101)(ii) intact at `a = 0`, and it **HOLDS at
   (BE-104)(i)'s own recorded witness** — because that refutation exhibits
   **one side**, and (E4) is about the **pair**. Patching only that corner
   leaves 287 escapes ((BE-153)).

**§8's BAR: LIFTS for two named new objects, STAYS DOWN for `A_sharp`.**
Recorded at (BE-154)(iii) and — per §8's own instruction that a lift must be
recorded **in §8, with its reason** — owed there too. `A_sharp` properness
stays barred *as posed*, and (BE-149) explains why: it keeps the refuted
downstream object. The lifts are (a) **`Γ`-properness** — an incidence lemma
for one fixed subspace of `Λ²K⁴ ⊕ Λ²K⁴` against a 3-parameter family of
products of **totally singular** 2-spaces (`Π_x = Σ_{p_x} ∩ Λ²π_x`); one half
of (BE-115) lifts to it, the Klein-quadric half does not — and (b) **(E4)** as
the clause in (BE-101). Both are **new downstream objects**, which is what the
recurring-wall rule asks for. **The cheapest decisive move is a
falsification**: a peel with `c_i(Π_x) = 2` and `e₁+e₂ ≤ 3`, which on
BSATUR's `ρ_i = 5` witness needs `ρ̄_j ⊆ Π_x` outright ((BE-154)(iii)); the
smallest concrete commit is one new driver mode running `cert`'s test at
`bdegtwo.sweep_points`' 411 **chart** points at both sides of the peel
((BE-154)(iv)).

**What did NOT move, said plainly.** `PencilPair K 3 G`, `hbareSplit`, `hK`,
(GR-15), (BE-14), S-mark, half (β), the 2-cut step, class uniformity, the 12
unwitnessed blocks ((BE-97)(iv)), `⟨M⟩`. **(PENCIL-SATURATES-CHART) itself
stays OPEN**, (E4) is **unproved**, and every certificate here is
per-configuration. **(β) at the window went UNCONDITIONAL at BSCOND and half
(B) is S-mark's OTHER half; (BE-14) needs BOTH** — closing nothing here
closes nothing there, and neither would closing something. **No landed
measurement is refuted**: (BE-139)(i)'s subspace identity reproduces and
(BE-139)(iii)'s 13 `(dim A, dim A_sharp)` pairs come out identical.

**Driver.** `notes/scripts/w4/barch.py`, five modes
(`graph|two|cert|arith|support`) plus `validate` (117 s, fits the foreground
budget). Exact ℚ; seed `20260902`; determinism checked byte-identical modulo
the driver's own timing lines. Figures gate discharged by the one-line
`git diff` check (a driver **added**, none modified).

**Three stale surfaces this landing must repair** (the per-commit rule that
three consecutive Phase-39 landings each tripped, dispatch-log F17):

- `notes/Phase39.md` **status header** (block at the top): *"at side-degree
  `≥ 2` **both gaps SETTLED, the obstruction the METHOD** ((BE-139)): no
  `p_x`-free subspace survives, clause **OPEN**"* — the clause after the colon
  is now scoped, not general.
- `notes/Phase39.md` **per-direction line** for BDEGTWO: *"THE OBSTRUCTION IS
  THE ARCHITECTURE ((BE-136)–(BE-141), *BE135–BE140*): no `p_x`-free subspace
  survives."* — same correction.
- `notes/Pencil-strategy.md` **§8 rank 2** — its kill condition (*"the method
  class settled either way, or a `p_x`-varying properness argument landed"*)
  has **FIRED** on the first clause; §8's **bar paragraph** needs the lift
  recorded with its reason, per its own rule.

**Cost.** One read-only recon dispatch, no build, no `.lean` (the 2026-08-05
Lean hold binds). Ordinal and the §7 tally are the coordinator's to reconcile;
this write-up cites them and increments neither.

## OBAR — seventy-eighth ordinal (one direction of a four-way concurrent round, drafted read-only 2026-09-03, **LANDED 2026-09-03**) — §8.2's U3 gate: is `H ∪ {bar along M}` an admissible (OC-35) subgraph?

**Selection provenance.** The **ninth strategy-only pass**
(`notes/Pencil-strategy.md` §8, coordinator-authored 2026-09-03) rewrote §8.2's
U3 row from *"live, rank 3"* to **already-pursued**, its first step having been
delivered more generally as **(OC-35)** by SIGZ (*Steps O31–O36*), and isolated
**exactly one genuine residue**: the ledger nobody ran on `H ∪ {bar along M}`,
U3's own object — with the row's own flag saying, in as many words, that
*whether that object is even an admissible (OC-35) subgraph* had **not been
checked**, and that *"that check gates the residue"*. The same flag sits in
§4.6's U3 blockquote, which adds *"confirm before spending a slice"* and notes
that the two surfaces must agree. The dispatch's value case was the **U1–U3
interlock** (§4.6's own framing — one target, one machine, one logical form):
with **U2 struck 2026-09-03** by (OC-4)+(OC-3), settling U3 either frees U1 to
inherit the whole shortlist or restores a third bet.

### The spec, as dispatched

**Two steps, strictly ordered, step 1 gating step 2.** (1) Read (OC-35)'s
actual hypotheses **at source** and settle whether the meet-line-bar object
satisfies them, with two named ways it might not — `M` is *"a meet line, not an
edge of `H`"*, so the construction *"may not produce a subgraph of the ambient
graph at all, and may create degree-1 vertices"*. (2) **Only if admissible**,
run the ledger. *"A negative answer is a complete and valuable landing — it
kills the residue and U3 with it. Do not manufacture a positive."*

**The coordinator's four verified findings, to be quoted rather than
inherited.** (1) U3 is already-pursued with exactly one residue — *do not
re-derive its programme*. (2) The interlock is why it is worth a dispatch
despite that, and §2.3's logical-form move (negatives uniform, positives
per-shape) is the standing reason to care. (3) Two filters that **may kill it on
sight**: the growing-ground-set test, and counting saturation (§2.5, reinforced
by (OC-3)/(OC-37)/(GR-141)) — with the standing warning that **§2.5 is a
NEGATIVE result and must never be quoted as supplying freeness**, a
mis-citation that had to be repaired on the board once. (4) Calibrate against
**(OC-24)**: disproof-risk reduction *"can never be the binding obstruction"*.

**Bars.** Draft-only, read-only against every shared file, **commits nothing**;
the 2026-08-05 Lean hold binds (**no `.lean`**); every driver in the
**foreground** with an explicit `timeout`, one at a time, never backgrounded
(dispatch-log F6); measure and diff against **`HEAD`**, never the working tree,
since siblings leave it dirty; the shared scratchpad prefixed `OBAR`; **no
shared monotone counter touched** (the arc's direction count,
`RESEARCH-ARC.md` §7's prediction tally) — the coordinator reconciles those.
`notes/scripts/README.md` *Harness debt* required reading before any numerics,
with the three silent hazards named explicitly.

### LANDING WRITE-UP — OBAR, 2026-09-03: **THE GATE IS NEGATIVE THREE WAYS, ONE OF THEM BY A LANDED THEOREM — AND THE LEDGER WAS NEVER A COMPUTATION: U3's OBJECT IS (T3) RESTATED, POINTWISE**

**THE GATE FAILS ON ALL THREE OF (OC-35)'s CLAUSES, AND THE MIDDLE ONE IS THE
INTERESTING FAILURE.** (OC-35) quantifies over *"a subgraph with min degree ≥ 2
at any pencil placement"* and its proof gives **each edge** a covector
*"annihilating `C_e` — a 5-space"*. (i) `bc ∉ E(G)`: `H` is induced, so an edge
there would give `k = 1` against `k ≥ 3` (§(K-dom)'s own derivation from
`dim V_bc = 3`), equivalently a 4-cycle against `girth(G) ≥ 7`. (iii) A **bar
is one row**; (OC-36)'s `f(V(F)) = 5|E(F)| − 6(|V(F)| − 1)` and every term of
the `δ`/`ρ`/`slack` ledger count five, so the ledger is not merely inapplicable
to the object — evaluated on it, it is **wrong by four rows**. (ii) is the one
worth the dispatch: a **hinge** along `M` requires `C(M) ∈ L_b ∩ L_c`, hence
`pt(b) ∈ Π(c)` **and** `pt(c) ∈ Π(b)` — **both** halves of **(Λ0d)** failing —
and §(K-σ) **(σ7)** *proves* that impossible at exactly this split (`a` a
degree-2 non-hub adjacent to both hubs), field-neutrally. **So the load-bearing
side condition of the arc's own main route is what forbids U3's object**, and
the negative is **chart-wide rather than generic**: it holds even where (Λ0d)
does fail, which is where a sceptic would look. ((OC-56).)

**THE COORDINATOR'S SECOND SUSPECTED OBSTRUCTION IS REFUTED, AND THAT MATTERS
FOR HOW THE NEGATIVE READS.** The spec flagged that the construction *"may
create degree-1 vertices"*. It cannot: a bar only raises degrees, and `H`
itself has min degree ≥ 2 (`deg_H(b) = deg_H(c) = 2` at 18/18, from every
non-hub of `G′` having degree exactly 2 — §(K-frame) *Step FR12*'s table — and
`b`, `c` being hubs). So the
negative is **not** the cheap min-degree failure it might have been — the object
is a perfectly good *bar-and-hinge* framework, and what it is not is an
(OC-35) *hinge subgraph*.

**AND THE LEDGER WAS NEVER A COMPUTATION WAITING TO BE DONE — THIS IS THE
FINDING.** A `b`–`c` attachment adds **no topological path**, so there is no
`δ_Q`, no `slack`, and nothing for (OC-37)'s class floor to bound. What governs
it instead is a one-line identity, for **any** attachment covector space `A`:
`corank R(H ⊕_A bc) = corank R(H) + dim(A ∩ V_bc^{⊥_E})`, with the realized
`A`-coefficients **exactly** that subspace ((OC-57)) — the general form of the
*"close it up by adding three rows `B(m(b) − m(c), ρ) = 0`"* move
§(K-slide-comb) already uses. Specialize to a **bar** (`dim A = 1`) and the bar
is in some stress's support **iff `V_bc ⊥_B C(M)`**, which is **(T3)
verbatim** — §(K-pitch) *Step 3*'s *"escape ⟺ some motion `m` of `H` has
`B(C(M), m(b) − m(c)) ≠ 0`"*, the (K-wit) row's own content and its own close-it
sentence. **U3's target statement is the escape, restated — pointwise, at every
chart point, by rank–nullity.** ((OC-58).)

**SO U3's OWN KILL CLAUSE FIRES, AND BY A CHEAPER MECHANISM THAN THE ONE IT
NAMES.** §4.6 wrote *"if chart-wide stresses turn out to have no more structure
than pointwise ones, U3 is only a change of wording"* — and asked for a
support enumeration as *"the honest first step … prose, not a driver"*. The
kill fires, but it needs **no** comparison of chart-wide with pointwise
structure: the support in question is **one coordinate**, and its vanishing is
(K-wit). **The logical-form move does not survive either**: the non-existence
U3 wanted **is** `V_bc ⊄ C(M)^{⊥_B}`, a rank *lower* bound — the same side of
§2.3's wall the arc has always been on. Restating a lower bound as *"no stress
exists"* changes the grammar, not the logical form.

**THE OTHER READING IS NOT MERELY UNREALIZABLE — IT REFUTES THE STATEMENT.**
Read the object as a five-row **hinge** (the only (OC-35)-shaped reading) and
the same identity gives jump `= 6 − dim(V_bc + ⟨C(M)⟩) ≥ 2`, always, with the
hinge always in the support. So under that reading U3's non-existence claim is
**FALSE at every legal chart point**, independently of (σ7) ((OC-59)). The
dichotomy is complete and both branches are negative, and there is no third
reading — an attachment is a subspace `A`, and (OC-57) covers every one.

**ONE POSITIVE CARRIED OUT, PLUS A SECOND DERIVATION OF (T3).** The redundant
`b`–`c` constraints form the 3-space `V_bc^{⊥_B}`, which contains `★r` by (T1);
the redundant *bars* are its Klein conic; and at a `dim W = 5` seed
`V_bc ⊥_B C(M) ⟺ C(M) ∝ ★r`, because `C(M) ⊥_B T` is automatic
(`pt(a) ∈ M`) — an `r`-side re-derivation of (T3) independent of the
rank–nullity one, recovering (σ5)'s load-side form. And
`rank B|_{V_bc^{⊥_B}} = rank B|_{V_bc}`, so §(K-Δ) **(M1)**'s 3-or-2 dichotomy
transports verbatim (3 at 13/18, 2 at 5/18, all five on the `k = 3`
serial-chain habitat), while the **signature is not combinatorial** — both
`(2,1)` and `(1,2)` occur at seeds of the same shape, (OC-3) again ((OC-60)).

**CALIBRATION, AS INSTRUCTED.** No gap moves; **not** disproof-risk reduction
either, so (OC-24) does not even need invoking — nothing here touches the
disproof side. What lands is the **retirement of a residue**, and with §8.2's
U2 already struck, **U3 is struck completely**: the interlocked shortlist is
**U1 alone**. The two filters were applied and neither killed it on sight — the
ground set does formally grow (`E(H) ∪ {bar}`), which is exactly why the object
looked live, and (OC-58) shows that is cosmetic; §2.5 is used **only as a
negative**, never as freeness.

**WHAT THIS PASS DID NOT DO, stated because a successor will want it.**
`V_bc ⊥_B C(M)` is FALSE at 18/18 seeds and 36/36 (shape, split) pairs, so
**(OC-58)'s failure branch is never exercised numerically at `L = M`** — it is
carried by the proof, plus two controls that fire the *same* predicate positive
at *other* lines. The failure locus is known nonempty, known to be a σ-orbit
with `{V_bc ⊥_B C(bc)}` ((σ5)) and reachable by a chart move at all four
habitats; **constructing one was not attempted**. This is the BSATUR-shaped
limit of the pass's own evidence and is disclosed as cap 1 rather than smoothed.
Applying that same sharpening to itself is also why the pass carries a
`--splits` mode: every other mode holds the **split** fixed at one per shape,
so `--splits` ranges over all 48 eligible splits (36 with a usable seed) and
makes the split the varied variable.

**Reservation, and it DEVIATED DOWN.** §(K-out) **extended**, **Steps O52–O57**,
labels **(OC-56)–(OC-61)** CLAIMED, **(OC-62)–(OC-65)** and **O58–O60 reserved
and returned UNUSED**; driver `notes/scripts/w4/obar.py` (new), six modes. The
dispatched spec offered **(OC-58)+ / O53+**, but `notes/Pencil-labels.md`
declares §(K-out)'s tail **verbatim** at OWALL's landing — *"the live tail is
therefore (OC-56)+ / Step O52+"* — and **no other §(K-out) direction was in the
round** to hold the skipped `(OC-56)`/`(OC-57)`/`O52`. The direction opened at
the declared tail per that file's standing lesson (*"the registry outranks a
coordinator's spec on label naming"*), GLEAF's same-round precedent for
deviating **down**. **This is reservation defect shape FIVE of the round** —
shape 4 with the sign flipped, a scan reading a *declaration* as a
*consumption* — recorded in that file's OBAR reservation block; the defects
block's own FOUR-count is coordinator-owned and flagged rather than
incremented.
0-hit verified at `HEAD` as the first action, **HITS = 0 / FILES = 0** across
`*.md`/`*.tex`/`*.lean`/`*.py`/`*.m2` for all 18 patterns at **53bc9740**; on a
re-check at **d1efc63d** (BARCH landed mid-run) `OBAR` reads 2/2, both being
this reservation's **own declaration** in `Pencil-fanout.md` and
`Pencil-labels.md`, the other seventeen still 0/0. **The next tail is (OC-62) /
*Step O58***.

**Notes recorded AT the landing.** (1) The `(K-out)` gap-map row took a
**128-word append inside u14**, paid for by **two content-duplication trims** in
the status half — `(OC-39)`'s *"since upgraded to a theorem by (OC-49)"* and
`(OC-27)`'s *"138/138 witnesses"*, both of which the close-it half already
states **with its own figures**, and both labels surviving elsewhere in the row.
Net **1692 → 1810** against a 1823 cap: **no `SPECIAL_CAPS` bump**, row still
`combined`, `gapdiff.py K-out HEAD` **0 dropped** (68 → 75 labels, 7 added). The
coordinator's landing instruction was `≤ 1810` rather than the cap, precisely
because a five-word margin does not survive transcription — the lesson BSCOND
and BARCH each paid for. The next `(K-out)` landing must **recompute**. (2)
`notes/Pencil-strategy.md` §8.2 **and** §4.6 carry the *same* flag and say so
explicitly — both must move in **one** commit, and §8.6 gains the settled
negative with its back-link struck in that commit. (3) Concurrency: the
working tree was dirty for the whole drafting run; every load-bearing quote was
re-verified against `HEAD` **three times** — at `53bc9740`, at `d1efc63d` after
BARCH landed mid-run, and again at `a5d8101c` at the landing — with the
`(K-out)` row **unchanged at 1692 words** across all three, the u14 anchor
unique each time, and the siblings' only gap-map edit being to the
`(K-bare-ext)` row: **no collision on `(K-out)`**. Two siblings' drafts
(`DSAT`, `GLEAF`) were on disk untracked throughout and were **not** touched. (4) The
`pitch.H_motions_vbc` move-down trigger re-dates at a **sixth** consumer; no
move made, no new hazard item, all three recorded silent hazards navigated
rather than encountered.

## DSAT — seventy-ninth ordinal (one direction of a four-way concurrent round, drafted read-only 2026-09-03, **LANDED 2026-09-03**) — §8.2's C2 row: its own prescribed satisfiability trace

**Selection provenance.** `notes/Pencil-strategy.md` §8.2's **C2** row had sat
**live and unpriced** while naming its own prerequisite — *"a stronger motive
can be **unsatisfiable** — needs a satisfiability trace first (the L6b/F10
precedent)"* — and §8's below-the-top-four paragraph listed *"C2's
satisfiability trace (the L6b/F10 precedent — the trace is the gate, not the
conjunct)"*. Nobody had run it. Draft-only, one of four concurrent directions,
`recon-opus`.

### The spec, as dispatched

**Target.** Decide whether the strengthened motive — `IsNondegPencilRealization`'s
four landed conjuncts plus `V_bc` general position — is satisfiable **at the
actual objects the induction's consumer hands it**. *"UNSAT kills C2, which is a
real result: the board loses a candidate honestly, and the arc has been carrying
it unpriced."*

**The coordinator's five findings.** (1) The row's own two honest problems —
every existing conjunct per-body/local while `V_bc` is global on a
vertex-deleted subgraph; and a stronger motive can be unsatisfiable. (2) What C2
is **not**: **C1 is STRUCK** and (D4) already gives per-shape dominance, so
re-derive neither, and *"nothing in `(K-dom)` bears on C2"*. (3) The L6b/F10
precedent — a deferred-hypothesis leaf can be clean, correct and axiom-clean and
still unsatisfiable for the consumer's object, so trace against the
**consumer's objects**, not an abstract statement. (4) **Say which stratum** —
(D3)'s `k ≥ 4` on the class, `k = 3` exactly on the (K-res) residuals; a trace
that runs on one and reports for both is the defect to avoid. (5) Both filters
bite: growing-ground-set, and §2.5 counting saturation (a **negative**, never a
supply of freeness).

**Bars.** Draft-only, commit nothing; the 2026-08-05 Lean hold (no `.lean`);
every driver in the **foreground** with an explicit `timeout`, one at a time
(F6); measure against `HEAD`, never the working tree; scratch files prefixed
`DSAT`; no shared monotone counter; `notes/scripts/README.md` *Harness debt*
required reading, with **no `Λ²`-side draw through `bimage.pt_in`**, the
`bwin.k4_span`/`k4_isect` guards for `K⁴` subspaces, and `bwin.dehom`'s
list-vs-tuple guard defeat.

### LANDING WRITE-UP — DSAT, 2026-09-03: **THE TRACE RETURNS UNSAT, AND IT IS (D1)'s HABITAT SPLIT REACHED BY A DIFFERENT MECHANISM — SAT ON THE CLASS, PROVABLY UNSAT ON (K-res), SO C2 DIES AS A *UNIFORM* CARRY AND IS NOT SHOWN DEAD AS A CLASS-ONLY CONJUNCT**

**THE CONSUMER'S OBJECT, AND WHY THE INDEX SET IS HALF THE QUESTION.** Read off
`Escape.lean:334`: the split arm hands `hK` the motive **at
`G′ = G.splitOff v a b e₀`**, from the IH (`:400`), and `V_bc` there is the
relative twist of `H = G′ − a`. `G′` does not know which vertex was the split
partner, and `pencil_reduction` (`Reduction.lean:850`) gives the motive **no
habitat hypothesis** — so a carried conjunct must quantify over an index set of
its own. Pinning it is **(DM-5)**, and it is **forced**: (T1)'s two-port
derivation needs `deg(a) = 2` in both directions; the unrestricted form is false
at **172 of 180** higher-degree indices (`dim V_bc ≥ 4`, and `4 + 3 > 6` forces
both meets — **0** exceptions to that implication); and `dim mot(H/bc) > dim
mot(G′)` at **all 180**, so the identity below cannot reach them. **The pinned
set is adjacent edge pairs, so the growing-ground-set filter is PASSED** — what
is non-local is the conjunct's *value*, which is the honest form of the row's
first stated problem.

**THE IDENTITY, AND IT IS THE FINDING.** At a degree-2 `a` with `N(a) = {b,c}`,
at **any** rank-target realization,
`dim V_bc = dim mot(G−a) − dim mot(G) ≥ def₃(G−a) − def₃(G)` (**(DM-6)**,
*proven*). Three steps, no genericity: `dim V_bc = dim mot(H) − dim mot(H/bc)`
by definition; every `H`-motion welding `b` to `c` **extends to `G`** by
`m(a) := m(b)` — both hinge conditions at `a` read `0 ∈ ⟨C⟩`, and `a` has no
third neighbour — so `dim mot(H/bc) ≤ dim mot(G)`, with equality at a rigid `G`;
and `dim mot(H) ≥ 6 + def₃(H)` at every realization. **0 violations at 255
indices**, the welded space computed independently each time. So `dim V_bc` —
the subject of §2.4, of C1 and of C2 — is at every degree-2 index a **rigidity
count of `G − a`**, and generically a purely combinatorial one (85/85).

**HENCE A COMBINATORIAL UNSAT GATE, AND IT FIRES.** `def₃(G−a) − def₃(G) ≥ 4`
gives `dim V_bc ≥ 4`, and both isotropic 3-spaces are then met — **the conjunct
at `a` is unsatisfiable at every realization** (**(DM-7)**, *proven*; UNSAT
**proved**, not a failed search). It fires at **54 of 255** indices and the split
is **exactly class vs (K-res)**, asserted rather than observed: θ(3,3,6)
**5/8** (`a ∈ {16…20}`), NT21c3 **13/16** (`a ∈ {104…116}`), **0** at all five
class habitats. Census: `def₃` gap 3 at 201 indices, 4 at 54, nothing else.
Since `hK` carries the (K-res) residual (2026-08-02 route-3(b)), **the uniform
conjunct is UNSAT at objects the consumer hands the motive: C2's own kill
condition fires.**

**AND THE TWO HALVES OF THE KILL HAVE DIFFERENT EVIDENTIAL STATUS — the scope
line is part of the result, not a hedge.** The **(K-res) half is PROVED**
((DM-7) is an argument off a combinatorial trigger). The **class half is
MEASURED at five shapes** — 0 firings at 62 degree-2 indices is a *shape-family
cap*, and the shape family is precisely the axis this trace did not vary. So:
**C2 is dead as a *uniform* carry, and is NOT shown dead as a class-only
conjunct.** A future proposal to carry `V_bc` general position restricted to the
pinned class habitat is **not** answered by this landing; it is answered by
§(K-ind) *Step I6* (no chart morphism at `hcontract`) and by the `(K-dom)`
row's open successor — *which class shapes, if any, have a degree-2 `a` with
`def₃(G−a) − def₃(G) ≥ 4`?* (SD-6)'s branch bound `ℓ ≤ 5` is **not** the
mechanism: NT21c3's forced index `a = 110` sits on a branch of length **3**.

**THE SAT SIDE IS REAL, AND IT IS THE SIMULTANEITY NOBODY HAD TESTED.** At each
of the five class habitats **one** exact-ℚ realization satisfies the escape
reading at **every** degree-2 index at once — 8/8, 16/16, 11/11, 11/11, 15/15.
No landed measurement has that shape: (D4) measures one split per habitat, (F1)
one witness per shape for the four conjuncts plus the rank target, *Step F5* 16
`e₀`-end splits. Simultaneity was the live risk and it is **discharged on the
class** ((DM-9)) — as an **existence** claim at a named seed, never as *"the
conjunct holds"*.

**AND "GENERAL POSITION" HAS THREE READINGS, TWO OF THEM DEAD.** Read as *a
general point of `Gr(3,6)`*, the conjunct is unsatisfiable at **22 of 85**
indices at the max over **6** seeds — **including 6 of 8 at the class exemplar
θ(3,4,5)** — because `V_bc` sits in the discriminant hypersurface there. At
`k = 3` that is a **theorem** ((D1)'s corollary, six indices), and the driver
asserts the ordered chain Gram's **shape** (zero diagonal, single off-diagonal
entry) rather than its rank — *the basis matters, and asserting the shape in
`span_basis`' RREF basis is the first thing this driver got wrong.* The
`k ≥ 4` half is a **maximum over seeds, not an UNSAT proof**, and is the figure
in the section most likely to need a successor's correction. Net: the only
survivable reading is **ESC**, the (PC-Z) escape — there is no weaker,
more-generic condition available to carry instead ((DM-10)).

**THE COORDINATOR'S FRAMING, CLASSIFIED** (`RESEARCH-ARC.md` §7). **Finding 2 is
REFUTED and it is the load-bearing correction:** *"nothing in `(K-dom)` bears on
C2"* is false — the deciding mechanism is a `V_bc`-dimension count in §(K-dom)'s
own object, and it reproduces **(D1)'s exact habitat split**, class vs (K-res).
Two candidates, one section, same wall. **Finding 4 is CONFIRMED and inverted:**
the instruction to name the stratum was right, and the answer is that **no
`k`-stratum is the right frame** — the conjunct is indexed by every degree-2
vertex of one object, so one object mixes `k` = 3…9, and the invariant that
decides satisfiability is `def₃(G−a)`; the 54 forced indices have `k` = 6, 8, 9
and the `k = 3` ones are precisely those the gate does **not** fire on.
**Findings 1, 3 and 5 CONFIRMED:** the per-body/local-vs-global problem is
located exactly (the *value*, not the index set); tracing against the consumer's
object is what surfaced the index-set question at all; and both filters are
answered — growing-ground-set **passed**, §2.5 not a bar but sharpened, since
(DM-6) makes the *dimension* half of general position exactly as
combinatorially certifiable and as useless as §(K-ind) *Step I5*(1) found the
Jacobian rank to be.

**ONE SOURCE-DERIVED FINDING WITH NO DRIVER, FLAGGED AS SUCH.**
`IsNondegPencilRealization` is **both** an antecedent (through
`PencilNondegFeasible`, `Motive.lean:133`, inside `PencilPair`'s `G.Simple →`
clause) **and** a consequent (through `HasGenericPencilRealization`, `:140`), so
a fifth conjunct does not simply strengthen the motive: it narrows the antecedent
and moves graphs across `Escape.lean:396`'s `by_cases hfeas` from the `hK`
branch onto **`hbareSplit`** — C2 buys a stronger `hK` input by enlarging kernel
(K-bare)'s habitat (currently absorbed by (BE-14)'s unconditional target, and
worth pricing before, not after). And its `mono` residual
(`IsNondegPencilRealization.mono`, `:245`) lands on the cut arm's own recorded
sharp boundary: `PencilNondegFeasible.mono` (`:272`) discharges the fourth
conjunct's residual only at demotions to `H`-degree **≤ 1**, its docstring
saying that at degree **2** it *"genuinely has no source in `G`'s witness"* —
and degree 2 is the new conjunct's whole index set ((DM-11)). One piece of good
news: the **fourth** conjunct, read off its definition body rather than off
`repin.star_span_ranks`' docstring (which overstates it at a hub), is exactly
`dim Λ²π̂ = 3` at a degree-2 `a`, asserted directly at 85/85 indices — so the
new conjunct is supported by a landed one.

**ONE HARNESS OBSERVATION, AND IT IS A DEBT ITEM, NOT A DEFECT.** All three
recorded silent hazards are **unreachable** from `dsat.py`, which is stronger
than avoided: it imports **no** `bimage`/`bwin`/`binduc` device at all, so
`pt_in`'s truncation, `span`'s width-6 case and `dehom`'s list-vs-tuple guard
defeat cannot be called from it. Every subspace goes through
`repin.span_basis` / `repin.lambda2_through` / `exactcore.nullspace` with a
dimension assert, and the acceptance gate is `dominance.base_seed`'s composite
`repin.star_generic`, re-asserted in-file. The debt item is a **move-down
trigger**: `dominance.py`'s split-seed / habitat device set reaches its second
and third consumers (`notes/scripts/README.md` *Harness debt*, opened and left
**unpaid** for a coordinator action, as ZNEQ's `ocon.meet` item was).

**Labels and the declared tail.** The spec offered `(D8)`–`(D14)`;
**`(DM-5)`–`(DM-11)`** were minted instead, per `notes/Pencil-labels.md` clause
**(L1)** and its own worked example for this very section — reservation defect
shape **three** of the round, whose diagnosis lives in that file's defects block
and is not repeated here. The reserved **step** names `D8`–`D14` were kept, with
bare `D8` adjudicated **taken-but-unrelated** (4 hits / 2 files,
`notes/Phase23-design.md`'s Phase-23f *Layer* steps) and resolved by L3
qualification. **The tail declared for the next reservation is (DM-12) /
*Step D15***, 0-hit verified at this landing — so a successor to §(K-dom) opens
**there**, not at `(D15)` (wrong family) and not at `(DM-13)`. **(L7) fired
again on this range's opening token**, `(DM-5)` carrying 1 hit as (L1)'s own
prescription: its second confirmation on the day it was minted. **Nothing
returned unused** — seven claim slots reserved, seven minted; seven steps
reserved, seven consumed.

**What did NOT move.** `PencilPair K 3 G`, `hK`, `hbareSplit`, `hcontract`,
(GR-15), (GR-10), (BE-14), S-mark, (RS-5), (OW), U1, **class uniformity**, and
every landed figure of §(K-dom) — (D1)–(D4), the rank table, the `3(k−3)` far
block, the 21 `--cap` seeds. **C1's strike is unaffected** and is not
re-derived. **§(K-ind) *Step I6* is untouched** and is now C2's *second* reason
rather than its only one: even the class-restricted conjunct stays
non-dispatchable as a transport argument, so this landing removes an excuse, not
a blocker. Not a PENCIL event; **E1/E2/E3 decided *not fired*, each with its
reason**: **(E1)** no g-flank — the direction touched neither (GR-15) nor any
admissible colouring; **(E2)** the clause needing real checking, since this
direction's own headline *is* a kill — it fires only when the target is refuted
**and** the ledger has no entry left *open-with-a-named-dispatchable-attack*,
and §8 still carries U1, (OW), collision dominance, S-mark, (AV-7)'s Case-I arm
and OGEOM's sentence, so it does **not** fire; **(E3)** the arc's target is not
proven. Five surfaces are **struck or annotated in the same commit** (F12):
§8.2's C2 row, §4-C2's kill-condition box, §8's below-the-top-four list, §8's
*"C2/U1 keep their standing notes"* clause and §4's gate box — plus §8.6, which
gains C2 with its back-links, and §(K-ind) *Step I6*. **One F12 item resolved
differently from the draft's prediction, recorded because the list was wrong:**
the `(K-ind)` gap-map **row** does not in fact carry C2's status — only §4-C2's
*Row:* pointer did — so that pointer is repointed to **(K-dom)** and the
`(K-ind)` row is left untouched rather than grown for no status change.

## GLEAF — eightieth ordinal (one direction of a four-way concurrent round, drafted read-only 2026-09-03, **LANDED 2026-09-03**, the round's last) — the ninth strategy pass's **rank 3**: (GR-144)'s successor 4, leaf-covering on the **branches**, and whether the landed matroid machinery reaches it

Workbook home: `notes/Pencil-informal-grid.md` §(K-grid) *Steps G165–G172*, labels
**(GR-145)–(GR-152)**. Driver `notes/scripts/w4/gleaf.py` (seven modes, `--validate` 298 s,
one foreground invocation).

### The spec, as dispatched

Rank 3 of the 2026-09-03 strategy pass, whose rationale called this *"the `hK` lane's
**only** live successor that is argument-shaped and reaches landed machinery"*, quoting the
`(K-grid)` close-it **u7**: *"untouched by (GR-142), still the one place the landed
Phase-12/13/14 machinery might reach"*. Two jobs: **state the branch-side demand
precisely**, and **settle whether matroid union / Tutte–Nash-Williams / the `k`-frame
matroid / Edmonds' covering reach it**. The spec flagged the trap explicitly — *confirm the
branch-side statement is not the same object (GR-141)/(GR-142) reach* — and named the
standing do-not-do: *the deliverable must be an argument, with the search demoted to an
adversarial control*. **A reasoned NO was priced as equal to a YES**, which is what the
return delivered.

### LANDING WRITE-UP — GLEAF, 2026-09-03: **the reach question SPLITS — the machinery DOES reach it, and what it reaches is a NECESSARY condition, so the lane is SPENT**

**Both jobs done, and the ranking rationale's two halves come apart.**

1. **Not the same object, and the reason is sharper than *different ground set*.**
   (GR-142) kills a family of **hub sets**; the branch-side demand lives on `Ĝ`'s
   **branch-copy multiset**. The load-bearing point is the **encoding**: the *leaf*
   (degree-cap) reading is **not a matroid** — two maximal independent sets of sizes 2 and 3
   at `K4(2,2,2,3,4,5)`, `X = {0,1}`, with a matroidal `|X| = 1` negative control — while
   the *star-containment* reading of the **same** demand ((GR-135)(iii)'s `deg = 3` half) is
   a **contraction**. This discharges (GR-144)'s own *"what would change this"* clause (c)
   affirmatively ((GR-147)).
2. **THE REACH IS REAL, and it is a theorem.** At a fixed leaf assignment the demand **is**
   an Edmonds matroid-partition problem over the six contracted graphic matroids
   `M(G°)/K_j`, with criterion `Σ_j [c(F ∪ K_j) − c(F)] ≤ σ(F)` at every branch set —
   **(GR-129)'s own `σ`, used a third time** — plus two equivalent forms, one of which makes
   `F = ∅` an equality. Four independent oracles agree at **4 344** instances, with two
   further matroid-free depth-first oracles and both verdicts exercised ((GR-148)). Every
   declaration it consumes was opened at source **with its provenance tier named**: the
   **local Apache-2.0 mirror** (`Matroid.Union` over an *indexed family*,
   `union_indep_iff`, `Union_rank_eq`, `adjMap_rk_eq`), the **upstream `apnelson1/Matroid`
   dependency** (`Graph.cycleMatroid_contract`, `Matroid.eRk_contract_add_eRk` — in
   `.lake/packages/`, **not** vendored in-repo), **mathlib** (`Matroid.comapOn`,
   `Matroid.contract`) and **project-original** (`tutte_nash_williams`,
   `isSpanningTreePacking_of_isTight`, the Phase-13 idiom adapter, the constant-family
   basis-split).
3. **AND IT BUYS NOTHING, which is the verdict.** The demand is **implied by**
   (GR-18)(iii)'s residual and a **tautology** inside (GR-140)'s own synthesis normal form:
   `D_β = {α(head β), γ(tail β)}` makes two of a pure hub's three absence-pairs share a grid
   coordinate. It is (GR-143)'s **tier 1** read as an existence statement, and it admits
   **455 400 of 472 680** legal pairs against the residual's **229 320** — **226 080 pairs
   pass the demand and fail the residual** ((GR-146)). So a **proof** cannot advance
   (GR-10), and a **refutation** would be strictly stronger than a g-flank. **u7's kill
   condition fires on both clauses at once, in opposite directions.**
4. **Two theorems worth keeping regardless.** *(a)* At `Λ = ∅` **only pure hubs can fail** —
   a leafless hub needs `deg_Ĝ ≥ 12`, which forces purity — so the *"prescribed set of
   `≤ n` vertices"* in (GR-138)'s phrasing is not a parameter ((GR-145)). *(b)*
   **`σ(F) ≥ 1` at every proper nonempty `F`** at a `D = 0` class shape, a reading of
   (GR-25)'s cut criterion, so **(GR-130)(b)'s tight lattice is trivial on this stratum**
   ((GR-149)) — and this is what kills both natural refuting configurations by an *argument*
   rather than a search.
5. **The demand DECIDED, on a stratum wider than the residual's.** All 312 `n_hub = 4` and
   all **4 598** `n_hub = 6` `D = 0` class shapes (2 623 pure-hub, where `all_packings`
   decides none and `synth_first` decided 150), plus 36 constructed class shapes to
   **`n_hub = 20`** with `|S|` up to 16; **0 failures**, 98.3 % of assignments passing, and a
   **two-block** assignment sufficing everywhere ((GR-150)). The **cover graph** a colouring
   proof would face has max degree **`≤ 2`** against six colours, by an argument — the
   degree-3 configuration is a proper tight set ((GR-151)).
6. **Where it stops, honestly.** The criterion's nonempty-`F` content is **never binding
   anywhere evaluated** (4 344 instances, 0 exceptions), which would make the demand
   *exactly* a hypergraph colouring — recorded as a **conjecture**, with the `σ` form named
   as where a proof goes ((GR-152)). The `n_hub ≤ 6` strata **do not exercise** that content
   at all (all 52 negatives are `F = ∅`); only the constructed `n_hub = 10` leg does, so of
   the 4 344 instances just **1 218** could have refuted it — a cap the pass's own support
   leg found rather than assumed away.

**One CORRECTION the coordinator's verification forced, and it is the kind worth recording.**
The draft listed **three** missing Lean bridges, one of them *"the heterogeneous per-set
rank formula"*. That is **not** a gap: `Matroid.Union_rank_eq` is heterogeneous outright
(`∑ i, (Ms i).rk Y` over *different* matroids), and what is constant-family is only
`BodyBar/TreePacking.lean`'s **`Set`-side idiom adapter**, whose own docstring says so. The
item was **downgraded to that adapter's heterogeneous twin** and the count now reads **two
bridges**, both counting/reduction steps. *A landed theorem listed as owed work is what a
successor prices a build against* — which is why the correction is in the step and not only
in the return.

**What did NOT move, said plainly.** `PencilPair K 3 G`, `hK`, **(GR-10)**, **(GR-15)**,
(GR-18)(iii)'s residual, (GR-140)(ii)'s synthesis criterion, class uniformity, the
`Λ ≠ ∅` merging conjunct, `hbareSplit`, S-mark. **No gap-map status word moves on (GR-10)
or (GR-15)**; the `(K-grid)` row gains eight labels and loses one forward-looking clause.
**E1 does not fire** — and this direction had a literal shot at it, since a refutation of
the demand *is* a g-flank; it is decided negative over the widest `hK`-side stratum the arc
has searched. Not a PENCIL event.

**Cost.** `--state` 45 s, `--encode` 0.4 s, `--edmonds` 103 s, `--slack` 9 s, `--decide`
43 s, `--value` 58 s, `--flank` 39 s; `--validate` **298 s**, so unlike `gglob.py` the whole
gate fits **one** 600 s foreground invocation. Run at `recon-opus`, draft-only, and landed
by the direction itself at the coordinator's instruction.

**Reservation record.** Reserved **(GR-146)–(GR-153) / G166–G173**; used
**(GR-145)–(GR-152) / *Steps G165–G172*** — a **deliberate one-step deviation DOWN** to the
tail GGLOB's landing declared verbatim in two places. **(GR-153) and *Step G173* are
returned unused**, and **the tail this direction declares for the next reservation is
(GR-153) / *Step G173***. Full record, including the (L7) per-token check and the metric it
reports, in `notes/Pencil-labels.md` §"Reservation — GLEAF"; the defect taxonomy is that
file's *Coordinator reservation defects* block (**shape 4**), **not duplicated here**.
