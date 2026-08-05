-- notes/scripts/m2/lambda1.m2 -- Phase 39 (PENCIL), kernel-(K) arc.
--
-- (L1) = the workbook's (Lambda1), notes/Pencil-informal.md S(K-Lambda) Step 2:
--
--     (q . w+)^2 * Phi_loc(lam) = -2 * B(w+, w-) * (lam . w+) * (lam . w-)
--
-- established here as an IDENTITY OVER THE FUNCTION FIELD -- i.e. with the
-- frame's coordinates treated as indeterminates -- rather than as the
-- per-frame evidence `python3 notes/scripts/w4/lambda.py --witt` produces
-- (23 sampled rational frames, each reporting the factorization scalar
-- exactly 1).  That driver is NOT superseded: it is the exact-rational
-- record, its figures are frozen, and this file is additive.
--
-- STATUS OF THIS OUTPUT.  Evidence for the workbook, at the same standing as
-- the exact-Q numerics -- never a substitute for Lean.  The project
-- formalizes everything its argument uses (DESIGN.md "Formalize everything
-- the argument uses"); "verified in Macaulay2" is not a proof this project
-- may cite in place of a formalization.  See notes/scripts/m2/README.md.
--
-- Conventions are those of the Python harness and are re-derived here, not
-- imported: Pluecker order (01,02,03,12,13,23) = exactcore.PL; hodge_star and
-- klein = repin.hodge_star / pitch.klein; cross4 = pitch.cross4 (Laplace
-- cofactors of a 3x4, sign (-1)^(i+1)).  Check (M0) pins the bracket
-- dictionary that connects them.
--
-- Determinism: no randomness anywhere, hence no seed.  The M2 version is
-- printed and is PART OF THE FIGURE (see the README's baseline rule).
--
-- Invocation (frozen; run from the repo root):
--     M2 --script notes/scripts/m2/lambda1.m2

-- ---------------------------------------------------------------- primitives

PLidx  = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};   -- exactcore.PL
wedge2 = (P,Pt) -> apply(PLidx, ij -> P#(ij#0)*Pt#(ij#1) - P#(ij#1)*Pt#(ij#0));
hstar  = v -> {v#5, -v#4, v#3, v#2, -v#1, v#0};   -- repin.hodge_star
dotv   = (u,v) -> sum(#u, i -> u#i * v#i);        -- exactcore.dot
klein  = (x,y) -> dotv(x, hstar y);               -- pitch.klein
Qform  = x -> klein(x,x);                         -- pitch.Q
det4   = (p,q,r,s) -> det matrix {p,q,r,s};       -- the bracket [p,q,r,s]

cross4 = (l1,l2,l3) -> (                          -- pitch.cross4
    A := {l1,l2,l3};
    apply(4, i -> (
        cols := select(toList(0..3), j -> j =!= i);
        (-1)^(i+1) * det matrix apply(3, r -> apply(cols, j -> A#r#j))
    ))
);

-- p ^ x for p in K^4 and x a Pluecker 2-vector; = 0 iff the line x meets p
wedge3 = (p, x) -> (
    posOf := (ii,jj) -> position(PLidx, ij -> ij == {ii,jj});
    apply({{0,1,2},{0,1,3},{0,2,3},{1,2,3}}, t -> (
        i := t#0; j := t#1; k := t#2;
        p#i * x#(posOf(j,k)) - p#j * x#(posOf(i,k)) + p#k * x#(posOf(i,j))
    ))
);

-- contraction of a Pluecker 2-vector by a covector; = 0 iff the line x lies
-- in the plane {nu = 0}
contract2 = (nu, x, Rr) -> (
    Mm := new MutableList from apply(4, i -> new MutableList from apply(4, j -> 0_Rr));
    scan(6, k -> ( i := (PLidx#k)#0; j := (PLidx#k)#1;
                   Mm#i#j = x#k; Mm#j#i = -x#k ));
    apply(4, j -> sum(4, i -> nu#i * Mm#i#j))
);

ok = (label, val) -> ( assert val; print("  OK   " | label) );

print "== (L1) symbolically: (Lambda1) as an identity over the function field ==";
print("  M2 version " | version#"VERSION" | " (pinned; part of the figure)");
print "  randomness: none -- deterministic symbolic computation, no seed";

-- ------------------------------------------------- (M0) the bracket dictionary
-- S(K-Lambda) "Standing notation" states the pairing dictionary
--     B(C(uv), C(pq)) = [u,v,p,q]
-- and every bracket row below (m, n, q, s, p+) is an instance.  Verified with
-- four free points: 16 indeterminates.

print "";
print "(M0) pairing dictionary  B(u^v, p^q) = [u,v,p,q]   [4 free points]";
R0 = QQ[p1_0..p1_3, p2_0..p2_3, p3_0..p3_3, p4_0..p4_3];
g0 = gens R0;
P1 = take(g0,{0,3}); P2 = take(g0,{4,7}); P3 = take(g0,{8,11}); P4 = take(g0,{12,15});
ok("B(u^v, p^q) - [u,v,p,q] = 0",
   klein(wedge2(P1,P2), wedge2(P3,P4)) - det4(P1,P2,P3,P4) == 0);
ok("alpha-planes are totally isotropic: [a,u,a,v] = 0",
   klein(wedge2(P1,P2), wedge2(P1,P3)) == 0);
ok("Pluecker relation: Q(u^v) = 0", Qform wedge2(P1,P2) == 0);

-- ---------------------------------------- (M1) the universal cofactor identity
-- The structural half of (Lambda1), with m, n, q, s, lam FREE covectors in
-- K^4: 20 indeterminates, no geometry, no gauge.  Writing cof(u) :=
-- cross4(u,m,n), this is the statement that the linear map lam |-> cof(lam)
-- has rank <= 2 with image <cof(s), cof(q)> and the precise normalization
-- kappa = -1/(q . cof s) claimed in Step 2's proof.

print "";
print "(M1) universal cofactor identity   [m,n,q,s,lam free: 20 indeterminates]";
U1 = QQ[mm_0..mm_3, nn_0..nn_3, qq_0..qq_3, ss_0..ss_3, ll_0..ll_3];
g1 = gens U1;
mv = take(g1,{0,3}); nv = take(g1,{4,7}); qv = take(g1,{8,11});
sv = take(g1,{12,15}); lv = take(g1,{16,19});
cof = u -> cross4(u, mv, nv);
wp1 = cross4(mv,nv,sv); wm1 = cross4(mv,nv,qv);
ok("cross4(m,n,s) = cross4(s,m,n)  (cyclic rows; pins the driver's argument order)",
   wp1 == cof sv and wm1 == cof qv);
ok("q . cof(s) = - s . cof(q)", dotv(qv,wp1) + dotv(sv,wm1) == 0);
ok("(q.w+) cof(lam) = (lam.w+) w- - (lam.w-) w+",
   all(4, i -> dotv(qv,wp1) * (cof lv)#i - dotv(lv,wp1) * wm1#i
               + dotv(lv,wm1) * wp1#i == 0));
ok("q . w+  is not the zero polynomial", dotv(qv,wp1) != 0);

-- --------------------------------- (M2) the universal quadratic expansion
-- Same 20 indeterminates plus a FREE symmetric 4x4 Gram (10 more).  Squaring
-- (M1) against an arbitrary quadratic form gives the general expansion; the
-- two cross terms Q(w+), Q(w-) are the ONLY geometric input (M3) has to kill.

print "";
print "(M2) universal quadratic expansion   [+ free symmetric Gram: 30 indets]";
U2 = QQ[mm_0..mm_3, nn_0..nn_3, qq_0..qq_3, ss_0..ss_3, ll_0..ll_3, gg_0..gg_9];
g2 = gens U2;
mv = take(g2,{0,3}); nv = take(g2,{4,7}); qv = take(g2,{8,11});
sv = take(g2,{12,15}); lv = take(g2,{16,19}); ge = take(g2,{20,29});
symIdx = {{0,0},{0,1},{0,2},{0,3},{1,1},{1,2},{1,3},{2,2},{2,3},{3,3}};
GS = new MutableList from apply(4, i -> new MutableList from apply(4, j -> 0_U2));
scan(#symIdx, k -> ( GS#((symIdx#k)#0)#((symIdx#k)#1) = ge#k;
                     GS#((symIdx#k)#1)#((symIdx#k)#0) = ge#k ));
Gfree = apply(4, i -> apply(4, j -> GS#i#j));
pairG = (x,y) -> sum(4, i -> sum(4, j -> x#i * Gfree#i#j * y#j));
cof = u -> cross4(u, mv, nv);
wp2 = cross4(mv,nv,sv); wm2 = cross4(mv,nv,qv);
qw2 = dotv(qv, wp2); lp2 = dotv(lv,wp2); lm2 = dotv(lv,wm2);
ok("(q.w+)^2 Phi(lam) = (lam.w+)^2 Q(w-) - 2(lam.w+)(lam.w-)B(w+,w-) + (lam.w-)^2 Q(w+)",
   (qw2)^2 * pairG(cof lv, cof lv)
     - ( lp2^2 * pairG(wm2,wm2) - 2*lp2*lm2*pairG(wp2,wm2) + lm2^2 * pairG(wp2,wp2) )
     == 0);

-- ---------------------------------------- (M3) the alpha/beta isotropy lemma
-- The geometric input, gauge-free: 4 free points, 16 indeterminates.  If
-- z in Lambda^2 K^4 is B-orthogonal to three independent lines through pt(a)
-- then z lies in alpha_a (a maximal isotropic 3-space), so Q(z) = 0; and
-- likewise for three independent lines of a plane and beta.  Applied to
-- w+ = cross4(m,n,s) (perp to C_ab, C_ac, C_aw -- all through pt(a)) and
-- w- = cross4(m,n,q) (perp to C_ab, C_ac, C_bc -- all inside plane(a,b,c)),
-- this is exactly Q(w+) = Q(w-) = 0.

print "";
print "(M3) alpha/beta isotropy lemma   [a,b,c,w free: 16 indeterminates]";
R3 = QQ[aa_0..aa_3, bb_0..bb_3, cc_0..cc_3, ww_0..ww_3];
g3 = gens R3;
av3 = take(g3,{0,3}); bv3 = take(g3,{4,7}); cv3 = take(g3,{8,11}); wv3 = take(g3,{12,15});
alphaGens = {wedge2(av3,bv3), wedge2(av3,cv3), wedge2(av3,wv3)};
betaGens  = {wedge2(av3,bv3), wedge2(av3,cv3), wedge2(bv3,cv3)};
ok("alpha_a = <C_ab, C_ac, C_aw> is totally isotropic",
   all(3, i -> all(3, j -> klein(alphaGens#i, alphaGens#j) == 0)));
ok("beta_pi = <C_ab, C_ac, C_bc> is totally isotropic",
   all(3, i -> all(3, j -> klein(betaGens#i, betaGens#j) == 0)));
ok("alpha_a is 3-dimensional over the function field",
   minors(3, matrix alphaGens) != 0);
ok("beta_pi is 3-dimensional over the function field",
   minors(3, matrix betaGens) != 0);
-- rank 3 => the three B-orthogonality conditions cut out a 3-space, which
-- therefore IS alpha_a (resp. beta_pi); total isotropy then gives Q(z) = 0.
ok("the 3 conditions B(z, .) = 0 have rank 3 (hodge_star is invertible)",
   minors(3, matrix apply(alphaGens, x -> hstar x)) != 0
   and minors(3, matrix apply(betaGens, x -> hstar x)) != 0);

-- ------------------------------ (M4) (Lambda1) end-to-end on the gauge slice
-- Gauge.  Both sides of (Lambda1) are bracket polynomials, hence GL(4)
-- relative invariants: under a simultaneous p |-> g p every bracket -- and
-- so, by (M0), every Klein pairing of two of these lines -- scales by det g.
-- Counting weights: Phi_loc |-> (det g)^5, (q.w+)^2 |-> (det g)^8, so the
-- left side |-> (det g)^13; B(w+,w-) |-> (det g)^7 and (lam.w+), (lam.w-)
-- |-> (det g)^3 each, so the right side |-> (det g)^13 as well (lam has no
-- point coordinates: it is a covector in the C-basis, which g does not
-- move).  For any frame with b, x1, x2, x3 independent the matrix
-- g = [b|x1|x2|x3]^{-1} is the UNIQUE element of GL(4) carrying them to
-- e0,e1,e2,e3, so the slice below meets every such GL(4)-orbit exactly once
-- and LHS-RHS = (det g)^{-13} (LHS-RHS)(slice).  Vanishing on the slice
-- therefore gives vanishing on a Zariski-dense subset of the full 28-
-- coordinate configuration space, hence identically.
--
-- The remaining three points a, c, w and the far covector lam stay FREE, so
-- the identity below uses NONE of (Lambda0)'s genericity clauses and none of
-- the panel / meet-line data: pt(a) is not constrained to the meet line M.
--
-- Why the slice and not all 28 coordinates: the ungauged expansion has
-- degree 52 in 28 point indeterminates and does not finish (measured
-- 2026-08-05: killed at 600 s inside cross4 on the ungauged rows).

print "";
print "(M4) (Lambda1) end-to-end   [b,x1,x2,x3 gauged; a,c,w,lam free: 16 indets]";
R4 = QQ[a_0..a_3, c_0..c_3, u_0..u_3, l_0..l_3];
g4 = gens R4;
av = take(g4,{0,3}); cv = take(g4,{4,7}); uv = take(g4,{8,11}); lv = take(g4,{12,15});
ev = i -> apply(4, j -> if j == i then 1_R4 else 0_R4);
bv = ev 0; x1 = ev 1; x2 = ev 2; x3 = ev 3;

-- the length-4 companion b - x1 - x2 - x3 - c and its four lines
Cl  = {wedge2(bv,x1), wedge2(x1,x2), wedge2(x2,x3), wedge2(x3,cv)};
Cab = wedge2(av,bv); Cac = wedge2(av,cv); Cbc = wedge2(bv,cv); Caw = wedge2(av,uv);
mv = apply(Cl, Ci -> klein(Ci,Cab));
nv = apply(Cl, Ci -> klein(Ci,Cac));
qv = apply(Cl, Ci -> klein(Ci,Cbc));
sv = apply(Cl, Ci -> klein(Ci,Caw));
Gram = apply(4, i -> apply(4, j -> klein(Cl#i, Cl#j)));

ok("structural zeros  m1 = n4 = q1 = q4 = 0",
   mv#0 == 0 and nv#3 == 0 and qv#0 == 0 and qv#3 == 0);
ok("Gram of the companion span is banded (adjacent lines meet)",
   all(4, i -> Gram#i#i == 0) and Gram#0#1 == 0 and Gram#1#2 == 0 and Gram#2#3 == 0);
ok("its three surviving entries B(C1,C3), B(C1,C4), B(C2,C4) are all nonzero",
   Gram#0#2 != 0 and Gram#0#3 != 0 and Gram#1#3 != 0);

wp = cross4(mv,nv,sv); wm = cross4(mv,nv,qv);
inS = wv -> apply(6, k -> sum(4, i -> wv#i * Cl#i#k));
wpv = inS wp; wmv = inS wm;

ok("w+ != 0 and w- != 0 as polynomial vectors",
   any(4, i -> wp#i != 0) and any(4, i -> wm#i != 0));
ok("Q(w+) = 0  (w+ is a line extensor)", Qform wpv == 0);
ok("Q(w-) = 0  (w- is a line extensor)", Qform wmv == 0);
ok("w+ passes through pt(a):  a ^ w+ = 0   (w+ spans S cap alpha_a)",
   wedge3(av, wpv) == {0,0,0,0});
ok("w- lies in plane(a,b,c)                (w- spans S cap beta_pi_a)",
   contract2(cross4(av,bv,cv), wmv, R4) == {0,0,0,0});
ok("rank [w+; w-] = 2 over the function field",
   any(subsets(toList(0..3),2), t -> wp#(t#0)*wm#(t#1) - wp#(t#1)*wm#(t#0) != 0));

qw  = dotv(qv, wp);
Bpm = klein(wpv, wmv);
ok("q . w+ != 0 and B(w+,w-) != 0 as polynomials", qw != 0 and Bpm != 0);

-- Phi_loc as a 4x4 symmetric matrix, exactly as lambda.py --witt builds it:
-- row i of the linear map is cross4(e_i, m, n).
Lmat = apply(4, i -> cross4(ev i, mv, nv));
PhiM = apply(4, i -> apply(4, j ->
          sum(4, p -> sum(4, r -> Lmat#i#p * Gram#p#r * Lmat#j#r))));
ok("Phi_loc is not the zero form", any(4, i -> any(4, j -> PhiM#i#j != 0)));

residM = apply(4, i -> apply(4, j ->
            (qw)^2 * PhiM#i#j + Bpm * (wp#i * wm#j + wm#i * wp#j)));
ok("(Lambda1) matrix form: (q.w+)^2 PhiM = -B(w+,w-)(w+ w-^T + w- w+^T), all 16 entries",
   all(4, i -> all(4, j -> residM#i#j == 0)));
ok("the factorization scalar is exactly 1 (no residual constant)",
   (qw)^2 * PhiM#0#0 + Bpm * (2 * wp#0 * wm#0) == 0);

Phi = sum(4, i -> sum(4, j -> lv#i * PhiM#i#j * lv#j));
lp = dotv(lv,wp); lm = dotv(lv,wm);
ok("(Lambda1) scalar form: (q.w+)^2 Phi_loc(lam) = -2 B(w+,w-)(lam.w+)(lam.w-)",
   (qw)^2 * Phi + 2 * Bpm * lp * lm == 0);
ok("hence rank Phi_loc = 2 generically, and {Phi_loc = 0} is two rational hyperplanes",
   Bpm != 0 and any(subsets(toList(0..3),2),
                    t -> wp#(t#0)*wm#(t#1) - wp#(t#1)*wm#(t#0) != 0));

print "";
print "PASSED -- (Lambda1) holds identically over the function field of the local frame.";
print "  Confidence upgrade for notes/Pencil-informal.md S(K-Lambda) Step 2:";
print "  per-frame evidence (23 rational frames) -> symbolic identity.";
