-- Phase 39, kernel-(K) THIRD fan-out direction Q -- (ANH-R1) AS A PURE
-- CONDITION: the bracket closed form of `C(H/P - beta)` at the stratum
-- where the reduced object is a single cycle, established as an IDENTITY
-- over the function field.
--
-- Workbook section: `(K-ann)`, Steps A14+; labels `(ANH-13)+`; driver blocks
-- `(ANH-Q0)`-`(ANH-Q4)` (the reserved direction-Q namespace,
-- `notes/Pencil-labels.md` 2026-08-06 G/Q/O table; the block prefix appends
-- a letter per that file's sanctioned form, because a bare `(Q..)` would
-- collide with section (K-pitch)'s placement quartic `Q(z)`).
--
-- Read `notes/scripts/m2/README.md` FIRST: the four conventions of this
-- layer bind.  Convention 1 in particular -- an M2 verdict is EVIDENCE for
-- the workbook at exactly the standing of the exact-Q numerics, never a
-- substitute for a Lean proof -- and convention 3, the divergence pin: every
-- primitive re-derived here names its canonical Python home and is pinned by
-- an in-driver check, which is (ANH-Q0).
--
-- THE OBJECT.  At a `k = 4` class triple with a length-5 branch `beta` of
-- `H/P`, the reduced graph `H/P - beta` has body-hinge count exactly 0, and
-- (ANH-R1) is its INDEPENDENCE at the pencil placement.  When its cycle rank
-- is 1 (equivalently `c(G) = 3`) it is a bare 6-cycle of bodies, and a
-- self-stress of a cycle is ONE screw `S` with `B(S, C_e) = 0` at all six
-- hinge lines ((ANH-6)'s branch constancy).  So
--
--     C(H/P - beta)  =  det [ C_0 ; C_1 ; ... ; C_5 ]
--
-- the 6x6 Pluecker determinant of the cycle's hinge lines: the pure
-- condition in White-Whiteley's sense, a bracket polynomial of degree 12.
-- `notes/scripts/w4/anhr1.py --frame` establishes that at every such site
-- the hinge lines are the chain of a 7-point OPEN polygon (the welded body
-- `X` breaks the hexagon, its two lines hanging off two different companion
-- vertices) and that NO panel of the pencil chart constrains those seven
-- points -- so the object computed in (ANH-Q2) is the shape-independent,
-- UNIVERSAL one.
--
-- randomness: none.  Deterministic; no `random`, no `randomKRationalPoint`,
-- no probabilistic Groebner shortcut, no characteristic-p sampling.
--
-- Reproduce:  M2 --script notes/scripts/m2/anhr1.m2   (from the repo root)

print "== anhr1.m2 -- (ANH-R1)'s pure condition, in closed bracket form ==";
print("M2 version: " | version#"VERSION");
print "randomness: none";
print "";

------------------------------------------------------------------------
-- Plueckerology.  Canonical Python homes (convention 3):
--   PL / wedge2 / hat  -> notes/scripts/exactcore.py
--   hodge_star         -> notes/scripts/w4/repin.py
--   klein  (the form B)-> notes/scripts/w4/pitch.py
--   det4 (the bracket) -> notes/scripts/w4/pitch.py
-- They cannot be imported across the language boundary, so they are
-- re-derived here and PINNED by (ANH-Q0) against the harness's dictionary.
------------------------------------------------------------------------

PL = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
wedge2 = (P,Q) -> apply(PL, ij -> P#(ij#0)*Q#(ij#1) - P#(ij#1)*Q#(ij#0));
hodge  = (w) -> {w#5, -w#4, w#3, w#2, -w#1, w#0};
klein  = (u,v) -> sum(6, i -> u#i * (hodge v)#i);
det4   = (a,b,c,d) -> det matrix {a,b,c,d};

nOK = 0;
ok = (s) -> (print("   OK  " | s); nOK = nOK + 1;);

------------------------------------------------------------------------
-- (ANH-Q0)  the bracket dictionary, pinned -- the analogue of lambda1.m2's
-- (M0).  Four free points, no gauge, no geometry.
------------------------------------------------------------------------
R0 = QQ[u_0..u_3, v_0..v_3, p_0..p_3, q_0..q_3];
uu = {u_0,u_1,u_2,u_3}; vv = {v_0,v_1,v_2,v_3};
pp = {p_0,p_1,p_2,p_3}; qq = {q_0,q_1,q_2,q_3};
assert(klein(wedge2(uu,vv), wedge2(pp,qq)) - det4(uu,vv,pp,qq) == 0);
ok "(ANH-Q0) B(C(uv), C(pq)) = [u,v,p,q], four free points";
assert(klein(wedge2(uu,vv), wedge2(uu,vv)) == 0);
ok "(ANH-Q0) line extensors are B-isotropic";
assert(klein(wedge2(uu,vv), wedge2(uu,pp)) == 0);
ok "(ANH-Q0) two lines through a common point pair to 0 -- so consecutive";
print "       hinge lines of a body-hinge cycle placed by JOINS always do";
print "";

------------------------------------------------------------------------
-- On the gauge.  Both `det[C_0..C_5]` and every triple-bracket product
-- below are polynomial in the point coordinates and transform by det(g)^3
-- under `p -> g p` (det of Lambda^2 g is det(g)^3, and each bracket picks up
-- det g).  So their difference is a relative invariant of weight 3.  For a
-- configuration whose first four points are independent, g = [z0|z1|z2|z3]^-1
-- is the UNIQUE element of GL(4) carrying them to the standard basis, so the
-- slice `z0..z3 = e0..e3` meets that orbit exactly once; vanishing on the
-- slice therefore gives vanishing on the dense open `[z0z1z2z3] != 0`, hence
-- identically.  This is `lambda1.m2` (M4)'s argument verbatim.
--
-- FEASIBILITY, measured 2026-08-06.  The UNGAUGED form of (ANH-Q1) -- all 24
-- point coordinates indeterminate -- does finish, in 578 s, and confirms the
-- same identity (10944 terms in the expanded determinant).  It is not the
-- driver because it sits at `notes/scripts/README.md`'s 600 s foreground
-- boundary; the gauged form below runs in a second.  Recorded as MEASURED,
-- script not retained: it is (ANH-Q1) with the gauge block `E4` replaced by
-- four further free 4-tuples of ring generators, a one-line edit -- the same
-- disposition
-- `lambda1.m2` gives its own ungauged probe.  Between the two the practical
-- boundary of this layer is now bracketed from BOTH sides: degree 12 in 24
-- point indeterminates finishes at 578 s, degree 52 in 28 does not finish at
-- 600 s.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- (ANH-Q1)  THE CLOSED HEXAGON.  Six bodies in a cycle, the hinge line of
-- {u_i, u_{i+1}} the join of their points.  This is `H/P - beta` at a
-- bare-cycle site on which the welded body `X` does NOT lie.
------------------------------------------------------------------------
S1 = QQ[a_(4,0)..a_(5,3)];
E4 = apply(4, i -> apply(4, j -> if i == j then 1_S1 else 0_S1));
P1 = E4 | {apply(4, j -> a_(4,j)), apply(4, j -> a_(5,j))};
L1 = apply(6, i -> wedge2(P1#i, P1#((i+1)%6)));
Hex = det matrix L1;
b1 = (i,j,k,l) -> det4(P1#i, P1#j, P1#k, P1#l);
A1 = b1(0,1,2,3) * b1(2,3,4,5) * b1(4,5,0,1);
A2 = b1(1,2,3,4) * b1(3,4,5,0) * b1(5,0,1,2);
assert(Hex - (A2 - A1) == 0);
ok "(ANH-Q1) det[C_0..C_5] = B(C1,C3)B(C3,C5)B(C5,C1) - B(C0,C2)B(C2,C4)B(C4,C0)";
print "       i.e. the ODD triangle of the Gram minus the EVEN one --";
print "       an identity over the function field, gauge-transported";
assert(Hex != 0);
ok "(ANH-Q1) the closed-hexagon pure condition is NOT identically zero";
print "";

------------------------------------------------------------------------
-- (ANH-Q2)  THE OPEN CHAIN -- the object every observed bare-cycle site
-- actually presents.  Seven points z_0 .. z_6, hinge lines
-- `C_i = z_i v z_{i+1}` for i = 0..5: the welded body `X` closes the body
-- cycle but NOT the point polygon, because its two hinges hang off two
-- different companion vertices (`anhr1.py --frame`: 6/6 sites, 7 distinct
-- points, 0 panels constraining them).
------------------------------------------------------------------------
S2 = QQ[z_(4,0)..z_(6,3)];
F4 = apply(4, i -> apply(4, j -> if i == j then 1_S2 else 0_S2));
Z = F4 | {apply(4, j -> z_(4,j)), apply(4, j -> z_(5,j)), apply(4, j -> z_(6,j))};
L2 = apply(6, i -> wedge2(Z#i, Z#(i+1)));
Hex7 = det matrix L2;
b2 = (i,j,k,l) -> det4(Z#i, Z#j, Z#k, Z#l);
-- every monomial of the answer is a product of three Gram entries
-- B(C_i,C_j) = [z_i,z_{i+1},z_j,z_{j+1}] forming a PERFECT MATCHING of the
-- six lines into non-adjacent pairs (adjacent lines pair to 0), because the
-- two end points z_0, z_6 occur to degree 1: there are exactly five such
-- matchings.
gm = (i,j) -> b2(i,i+1,j,j+1);
Ma = gm(0,2)*gm(1,4)*gm(3,5);
Mb = gm(0,3)*gm(1,4)*gm(2,5);
Mc = gm(0,3)*gm(1,5)*gm(2,4);
Md = gm(0,4)*gm(1,3)*gm(2,5);
Me = gm(0,5)*gm(1,3)*gm(2,4);
cands = {Ma, Mb, Mc, Md, Me};
(mons2, cf2) = coefficients matrix {append(cands, Hex7)};
Acf = lift(submatrix(cf2, {0,1,2,3,4}), QQ);
bcf = lift(submatrix(cf2, {5}), QQ);
assert(solve(Acf, bcf) === null);
ok "(ANH-Q2) det[C_0..C_5] is NOT a combination of the five Gram matchings";
print "       -- so the closed hexagon's two-triangle form does NOT survive";
print "       the break at the welded body X";
assert(Hex7 != 0);
ok "(ANH-Q2) the open-chain pure condition is NOT identically zero";
GG = matrix apply(6, i -> apply(6, j -> klein(L2#i, L2#j)));
assert(det GG + Hex7^2 == 0);
ok "(ANH-Q2) det(Gram) = -C^2 : the SQUARE is an explicit bracket polynomial";
print "       in the ten surviving Gram entries (the five adjacent pairs";
print "       vanish; C_0 and C_5 do NOT meet, which is the break)";

-- IRREDUCIBILITY.  GL(4) is connected, so it permutes -- hence fixes -- the
-- irreducible factors of the relative invariant `C`; each factor is
-- therefore itself a bracket polynomial, of total degree divisible by 4, and
-- a degree-4 one is a single bracket.  On the slice every bracket meeting
-- {z4,z5,z6} stays non-constant, so an irreducible restriction rules out
-- every factor EXCEPT `[z0z1z2z3]`, which the slice sends to 1.  That last
-- one is killed by a second specialization making the bracket vanish while
-- keeping all six lines nonzero.
assert(#(factor Hex7) == 2);   -- the polynomial itself, and the unit -1
ok "(ANH-Q2) C is IRREDUCIBLE on the gauge slice";
S2b = QQ[zz_(4,0)..zz_(6,3)];
G3 = apply(3, i -> apply(4, j -> if i == j then 1_S2b else 0_S2b));
zdep = apply(4, j -> (if j < 3 then 1_S2b else 0_S2b));  -- z0 = z1+z2+z3
Zb = {zdep} | G3 | {apply(4, j -> zz_(4,j)), apply(4, j -> zz_(5,j)),
                    apply(4, j -> zz_(6,j))};
assert(det4(Zb#0, Zb#1, Zb#2, Zb#3) == 0);
L2b = apply(6, i -> wedge2(Zb#i, Zb#(i+1)));
assert(all(L2b, C -> C != {0,0,0,0,0,0}));
assert(det matrix L2b != 0);
ok "(ANH-Q2) [z0z1z2z3] does NOT divide C -- so C is irreducible outright";
print "       CONSEQUENCE: (ANH-R1)'s own certificate admits NO factorization";
print "       into smaller bracket conditions -- there is no (ANH-7)-style";
print "       one-bracket recipe for it, and none for (Lambda1)'s rank-2";
print "       two-linear-forms shape either";
print "";

------------------------------------------------------------------------
-- (ANH-Q3)  THE BAD LOCUS.  (ANH-11) inhabits `{C = 0}` by a COMMON
-- TRANSVERSAL: six lines meeting one line `L` lie in the SPECIAL linear
-- complex of axis `L`, and `C(L)` is then the self-stress.  Two things to
-- separate, and the second is what (ANH-11) does not say:
--   (a) the special-complex locus really is inside `{C = 0}`;
--   (b) `{C = 0}` is STRICTLY bigger -- a general (non-special) linear
--       complex also kills the determinant, and such configurations exist,
--       so the transversal construction reaches only part of the bad locus.
------------------------------------------------------------------------
-- (a) (ANH-11) ON THE CHAIN.  Anchor `L = z_1 v z_4` at two chain bodies.
-- The four lines incident to z_1 or z_4 meet `L` automatically; the two
-- others are made to meet it by placing `z_3` in the plane <z_1, z_4, z_2>
-- and `z_6` in the plane <z_1, z_4, z_5> -- exactly (ANH-12)'s "each
-- remaining incidence is affine-linear in one movable far vertex".
S3 = QQ[w_(0,0)..w_(2,3), r_0..r_5];
W = apply(3, i -> apply(4, j -> w_(i,j)));      -- z_0, z_2, z_5 free
G4 = apply(4, i -> apply(4, j -> if i == j then 1_S3 else 0_S3));
z1 = G4#0; z4 = G4#1;                            -- gauge: z_1 = e0, z_4 = e1
comb = (u,v,x,s,t,q) -> apply(4, i -> s*u#i + t*v#i + q*x#i);
z0 = W#0; z2 = W#1; z5 = W#2;
z3 = comb(z1, z4, z2, r_0, r_1, r_2);
z6 = comb(z1, z4, z5, r_3, r_4, r_5);
ZT = {z0, z1, z2, z3, z4, z5, z6};
L3 = apply(6, i -> wedge2(ZT#i, ZT#(i+1)));
CL = wedge2(z1, z4);
assert(all(L3, C -> klein(C, CL) == 0));
ok "(ANH-Q3)(a) all six chain lines meet L = z1 v z4, i.e. are B-perp to C(L)";
assert(det matrix L3 == 0);
ok "(ANH-Q3)(a) so the pure condition vanishes IDENTICALLY on that locus --";
print "       (ANH-11)'s common-transversal mechanism, re-derived symbolically";
print "       on the chain object rather than at sampled witnesses";
-- (b) a GENERAL complex.  The screw `S = C(e0e1) + C(e2e3)` has NONZERO
-- pitch (B(S,S) != 0), so it is no line and its complex has no axis: a chain
-- inside it has NO common transversal.  Build one: `B(z v z', S) = 0` is the
-- symplectic form, one linear condition, so the chain is built one point at
-- a time.  This is the localized form of the null-correlation device of
-- section (K-sigma) *Step sigma6*.
Sgen = {1_S3, 0_S3, 0_S3, 0_S3, 0_S3, 1_S3};
assert(klein(Sgen, Sgen) != 0);
ok "(ANH-Q3)(b) S = C(e0e1) + C(e2e3) is a screw of NONZERO pitch (no axis)";
-- an EXPLICIT integer chain inside that complex (an existence claim, so an
-- exact witness is a proof; no randomness -- the seven points are literals).
Sb = {1_QQ, 0_QQ, 0_QQ, 0_QQ, 0_QQ, 1_QQ};
omg = (P,Q) -> P#0*Q#1 - P#1*Q#0 + P#2*Q#3 - P#3*Q#2;
ZB = {{1_QQ,0,0,0}, {1_QQ,0,1,1}, {2_QQ,1,1,0}, {3_QQ,1,2,1},
      {1_QQ,1,2,0}, {3_QQ,1,1,1}, {2_QQ,1,2,1}};
assert(all(6, i -> omg(ZB#i, ZB#(i+1)) == 0));
LB = apply(6, i -> wedge2(ZB#i, ZB#(i+1)));
assert(all(LB, C -> C != {0,0,0,0,0,0}));
assert(all(LB, C -> klein(C, Sb) == 0));
ok "(ANH-Q3)(b) an explicit 7-point chain, all six lines inside that complex";
MB = matrix LB;
assert(det MB == 0);
assert(rank MB == 5);
ok "(ANH-Q3)(b) C vanishes there and the perp is EXACTLY <S> (rank 5)";
print "       -- S has nonzero pitch, so the six lines have NO common";
print "       transversal: the BAD LOCUS of C STRICTLY CONTAINS (ANH-11)'s";
print "       common-transversal locus.  A second, axis-free mechanism, the";
print "       localized null-correlation device of section (K-sigma) Step sigma6";
print "";

------------------------------------------------------------------------
-- (ANH-Q4)  THE THETA CORE, the next stratum up (reduced order 6 with
-- n = 2 nodes and three branches).  A self-stress is one screw per branch,
-- B-perp to that branch's lines, with equilibrium `S_1 + S_2 + S_3 = 0` at
-- the two nodes.  With branch lengths (5,5,2) the two length-5 screws are
-- PINNED to the 1-dimensional Klein-perps `kappa_1`, `kappa_2` of their five
-- lines (Step A6), so the pure condition collapses to the statement that
-- `kappa_1 + kappa_2` is not B-perp to both lines of the short branch:
-- a 2x2 determinant in bracket data, NOT a 6x6 one.  The STRUCTURE is a
-- consequence of (ANH-6); the non-vanishing is witnessed here at an exact
-- rational configuration (moment-curve points), which is all an existence
-- claim on an irreducible local chart needs.
------------------------------------------------------------------------
-- FEASIBILITY, measured 2026-08-06: the GENERIC-POINT form of this block --
-- twelve free points, 48 indeterminates, two 5x6 Klein-perp kernels over the
-- polynomial ring -- does NOT finish at 600 s (killed).  So the symbolic
-- reach of this layer on (ANH-R1) stops at the bare-cycle stratum, which is
-- the measurement direction Q was sent to make.  Recorded as MEASURED,
-- script not retained: it is the block below with `Y` replaced by twelve
-- free 4-tuples of ring generators, a one-line edit.  What survives here is
-- the STRUCTURE (a proof-level consequence of (ANH-6), not a computation)
-- plus an exact rational witness for the non-vanishing -- which is all a
-- non-vanishing existence claim on an irreducible chart needs.
mc = (t) -> {1_QQ, t, t^2, t^3};       -- moment curve: every bracket nonzero
Y = apply(11, i -> mc(i));
-- branch 1: Y_0 .. Y_5 (five lines); branch 2: Y_0, Y_6..Y_9, Y_5 (five);
-- branch 3: Y_0, Y_10, Y_5 (two).  11 bodies, 12 hinges, count 0, c' = 2.
br1 = apply(5, i -> wedge2(Y#i, Y#(i+1)));
br2 = {wedge2(Y#0, Y#6), wedge2(Y#6, Y#7), wedge2(Y#7, Y#8),
       wedge2(Y#8, Y#9), wedge2(Y#9, Y#5)};
br3 = {wedge2(Y#0, Y#10), wedge2(Y#10, Y#5)};
assert(5 * 12 - 6 * (11 - 1) == 0);
ok "(ANH-Q4) theta(5,5,2) core: 11 bodies, 12 hinges, body-hinge count 0";
kperp = (LL) -> (
    K := generators kernel matrix apply(LL, C -> hodge C);
    K);
K1 = kperp br1; K2 = kperp br2;
assert(numgens source K1 == 1 and numgens source K2 == 1);
ok "(ANH-Q4) each length-5 branch pins its screw to a 1-dim Klein-perp";
k1 = flatten entries K1; k2 = flatten entries K2;
-- equilibrium at the two nodes forces S_3 = -(S_1 + S_2) with S_1 = s*k1,
-- S_2 = u*k2, so the pure condition is the 2x2 determinant of the pairings
-- of k1, k2 against the two lines of the SHORT branch: bounded-size again,
-- but in objects (kappa_1, kappa_2) that are themselves degree-10 brackets.
Mth = matrix {{klein(k1, br3#0), klein(k2, br3#0)},
              {klein(k1, br3#1), klein(k2, br3#1)}};
assert(det Mth != 0);
ok "(ANH-Q4) the theta(5,5,2) pure condition is nonzero at an exact witness,";
print "       hence NOT identically zero on the local chart";
print "";

print("   " | toString nOK | " assertions OK");
print "PASSED";
