-- earbad.m2 -- the placement bad sets B_k(r) of the short open ear step,
-- per flag orbit, as varieties in the Grassmannian (workbook §(K-main)
-- Step MC13, claims (MC-43), (MC-45), (MC-46), (MC-47): the 2026-09-24
-- second-reader continuation of Step MC10's (MC-27)).
--
-- Notation (Step MC10).  A flag pair (p_a, pi_a; p_b, pi_b) in a standard
-- frame of its orbit (i)-(iv); an ear_j placement is p_a, x_1, ..., x_j, p_b
-- with x_1 in pi_a, x_j in pi_b, middle points free (j = 1: the point on
-- m = pi_a cap pi_b); Lambda_j is the span of its j + 1 hinge lines.  For
-- dim rho = r and r + j <= 5 the bad set is
--     B_j(r) = {rho in Gr(r, 6) : rho cap Lambda_j != 0 at EVERY placement},
-- and rho cap Lambda != 0 iff wedge^r rho ^ wedge^(j+1) Lambda = 0: LINEAR in
-- the Pluecker coordinates of rho, with one equation per coefficient of the
-- placement polynomials.  So B_j(r) = Gr(r, 6) cut by an exact linear space,
-- computed here with the placement coordinates as indeterminates (an identity
-- in the placement, valid for the whole orbit by projective equivariance).
--
-- Checks (each prints one OK line; a failing assert exits 1):
--   (B0)  the Pluecker order (01,02,03,12,13,23) of exactcore.PL, and
--         M2's Grassmannian variable order = subsets(6, r);
--   (B1)  B_3(2) subset B_2(2), in all four orbits ((MC-45), r = 2);
--   (B2)  orbits (i), (ii), r = 2, 3: B_2(r) is EXACTLY the union of
--         {rho >= Pen_a}, {rho >= Pen_b} and (r = 3) {rho <= Pen_a + Pen_b},
--         and B_2(r) subset B_1(r) ((MC-46));
--   (B3)  orbit (iii): B_2(1) = B_3(1) = empty, B_2(2) = B_3(2) = {rho <= N3},
--         B_2(3) = {dim(rho cap N3) >= 2}, N3 = Pen_a + Pen_b (3-dim) ((MC-47));
--   (B4)  orbit (iv): Lambda_2 = Lambda^2 pi at every placement, so
--         B_2(r) = {rho cap Lambda^2 pi != 0} (r = 1, 2), and B_2(r) is NOT
--         contained in B_1(r) ((MC-47)).
-- Exact over QQ; randomness: none; writes nothing.
--   M2 --script notes/scripts/m2/earbad.m2
-- Re-derived primitives (convention 3): wedge2 = exactcore.wedge2 in the
-- order exactcore.PL, pinned by (B0).

kk = ZZ/5; print "earbad_p5.m2 (earbad.m2 over ZZ/5; Step MC20's second reading, 2026-09-25)";
print ("M2 version " | version#"VERSION");
print "randomness: none";

R = kk[u0,u1,u2,w0,w1,w2,v0,v1,v2,v3,y0,y1,y2];
PLi = {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)};    -- exactcore.PL
wedge2 = (x,y) -> apply(PLi, ij -> x_(ij_0)*y_(ij_1) - x_(ij_1)*y_(ij_0));
comb = (cs, bs) -> sum apply(#cs, i -> cs_i * bs_i);
e = apply(4, i -> apply(4, j -> if i == j then 1_R else 0_R));

-- (B0)
assert(wedge2(e_0, e_1) == {1,0,0,0,0,0} and wedge2(e_1, e_3) == {0,0,0,0,1,0}
       and wedge2(e_2, e_3) == {0,0,0,0,0,1});
Ptest = kk[p_0..p_5];
assert(first entries gens Grassmannian(1, 3, Ptest) == {p_2*p_3 - p_1*p_4 + p_0*p_5});
print "OK (B0) Pluecker order = exactcore.PL; Grassmannian order = subsets(6, r)";

-- frames: (p_a, basis of pi_a, p_b, basis of pi_b, basis of m)
frame = hashTable {
 "i"   => (e_0, {e_0, e_2, e_3}, e_1, {e_1, e_2, e_3}, {e_2, e_3}),
 "ii"  => (e_0, {e_0, e_1, e_2}, e_1, {e_1, e_2, e_3}, {e_1, e_2}),
 "iii" => (e_0, {e_0, e_1, e_2}, e_1, {e_0, e_1, e_3}, {e_0, e_1}),
 "iv"  => (e_0, {e_0, e_1, e_2}, e_1, {e_0, e_1, e_2}, {e_0, e_1, e_2})
};
-- the two terminal pencils and N = Pen_a + Pen_b, as sets of Pluecker indices
-- (every one is a coordinate subspace in these frames)
pens = hashTable {
 "i"   => ({1,2}, {3,4}),       -- Pen_a = <e02, e03>, Pen_b = <e12, e13>
 "ii"  => ({0,1}, {3,4}),       -- Pen_a = <e01, e02>, Pen_b = <e12, e13>
 "iii" => ({0,1}, {0,4}),       -- Pen_a = <e01, e02>, Pen_b = <e01, e13>
 "iv"  => ({0,1}, {0,3})        -- Pen_a = <e01, e02>, Pen_b = <e01, e12>
};
earLines = (fr, k) -> (
  (pa, A, pb, B, M) := fr;
  if k == 1 then (
     y := comb(take({y0,y1,y2}, #M), M);
     return {wedge2(pa, y), wedge2(y, pb)});
  x1 := comb({u0,u1,u2}, A);
  xk := comb({w0,w1,w2}, B);
  mids := if k == 3 then {{v0,v1,v2,v3}} else {};
  pts := {pa, x1} | mids | {xk, pb};
  apply(#pts - 1, i -> wedge2(pts_i, pts_(i+1))));
extPow = L -> (m := matrix L; apply(subsets(6, #L), I -> det submatrix(m, , I)));
spanOf = vs -> (
  mons := unique flatten apply(vs, f -> flatten entries monomials f);
  if #mons == 0 then return map(kk^(#vs), kk^0, 0);
  matrix apply(vs, f -> apply(mons, mm -> coefficient(mm, f))));
sgn = (A, I) -> (
  B := select(I, b -> not member(b, A));
  s := 0; scan(A, a -> scan(B, b -> if b < a then s = s + 1));
  if even s then 1 else -1);
wedgeEqs = (r, lam, Smat, P) -> (
  sr := subsets(6, r); sl := subsets(6, lam); pv := gens P; eqs := {};
  scan(numcols Smat, c -> (
     s := flatten entries Smat_{c};
     scan(subsets(6, r + lam), I -> (
        f := sum apply(subsets(I, r), A -> (
             B := select(I, b -> not member(b, A));
             sgn(A, I) * s_(position(sl, J -> J == B)) * pv_(position(sr, J -> J == A))));
        if f != 0 then eqs = append(eqs, f)))));
  ideal eqs);
ringFor = r -> kk[p_0..p_(binomial(6, r) - 1)];
badIdeal = (orb, k, r, P) -> (
  Lk := earLines(frame#orb, k);
  trim(Grassmannian(r - 1, 5, P) + wedgeEqs(r, #Lk, spanOf extPow Lk, P)));
linPart = (orb, k, r, P) -> (
  Lk := earLines(frame#orb, k); wedgeEqs(r, #Lk, spanOf extPow Lk, P));
-- the Schubert-type conditions on coordinate subspaces
coordIdeal = (r, P, keep) -> trim(Grassmannian(r - 1, 5, P) +
   ideal apply(select(#(subsets(6, r)), i -> not keep((subsets(6, r))_i)), i -> (gens P)_i));
containsAll = (T) -> (I -> isSubset(T, I));        -- rho >= span(T)
insideOf = (S) -> (I -> isSubset(I, S));          -- rho <= span(S)
sameVar = (I, Js) -> radical I == intersect Js;
subsetVar = (I, J) -> isSubset(J, radical I);   -- V(I) subset V(J)

-- (B1)
for orb in {"i","ii","iii","iv"} do (
  P := ringFor 2;
  assert subsetVar(badIdeal(orb, 3, 2, P), linPart(orb, 2, 2, P)));
print "OK (B1) B_3(2) subset B_2(2) in orbits (i), (ii), (iii), (iv)";

-- (B2)
for orb in {"i","ii"} do (
  (A, B) := pens#orb; N := sort unique(A | B);
  P2 := ringFor 2;
  assert sameVar(badIdeal(orb, 2, 2, P2),
                 {coordIdeal(2, P2, containsAll A), coordIdeal(2, P2, containsAll B)});
  assert subsetVar(badIdeal(orb, 2, 2, P2), linPart(orb, 1, 2, P2));
  P3 := ringFor 3;
  assert sameVar(badIdeal(orb, 2, 3, P3),
                 {coordIdeal(3, P3, containsAll A), coordIdeal(3, P3, containsAll B),
                  coordIdeal(3, P3, insideOf N)});
  assert subsetVar(badIdeal(orb, 2, 3, P3), linPart(orb, 1, 3, P3)));
print "OK (B2) orbits (i), (ii): B_2(2) = {>= Pen_a} u {>= Pen_b}, B_2(3) = that u {<= Pen_a + Pen_b}; both inside B_1";

-- (B3)
(A3, B3) := pens#"iii"; N3 := sort unique(A3 | B3);
P1 = ringFor 1;
assert(badIdeal("iii", 2, 1, P1) == ideal(1_P1) or dim badIdeal("iii", 2, 1, P1) == 0);
assert(dim badIdeal("iii", 3, 1, P1) == 0);
P2 = ringFor 2;
assert sameVar(badIdeal("iii", 2, 2, P2), {coordIdeal(2, P2, insideOf N3)});
assert sameVar(badIdeal("iii", 3, 2, P2), {coordIdeal(2, P2, insideOf N3)});
P3 = ringFor 3;
assert sameVar(badIdeal("iii", 2, 3, P3),
               {coordIdeal(3, P3, I -> #select(I, i -> member(i, N3)) >= 2)});
print "OK (B3) orbit (iii): B_2(1) = B_3(1) = empty; B_2(2) = B_3(2) = {rho <= N3}; B_2(3) = {dim(rho cap N3) >= 2}";

-- (B4)
L2 = earLines(frame#"iv", 2);
assert(rank matrix spanOf extPow L2 == 1);      -- wedge^3 Lambda_2 has one direction: Lambda_2 is constant
lam2pi = {0, 1, 3};                              -- Lambda^2 pi = <e01, e02, e12>
for r in {1, 2} do (
  P := ringFor r;
  Bconst := trim(Grassmannian(r - 1, 5, P) + wedgeEqs(r, 3,
      transpose matrix {apply(subsets(6, 3), I -> if I == lam2pi then 1_kk else 0_kk)}, P));
  assert sameVar(badIdeal("iv", 2, r, P), {Bconst});
  assert(not subsetVar(badIdeal("iv", 2, r, P), linPart("iv", 1, r, P))));
print "OK (B4) orbit (iv): Lambda_2 = Lambda^2 pi at every placement; B_2(r) = {rho cap Lambda^2 pi != 0} (r = 1, 2), not inside B_1(r)";
print "earbad: all checks passed";
