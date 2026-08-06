-- notes/scripts/m2/outerwide.m2
--
-- Phase 39, section (K-out) Step O11.  THE (OC-8) CLAUSE AT A LENGTH-5-CHAIN
-- END, AT THE GENERIC POINT OF THE LOCAL FRAME -- and a CLOSED FORM for its
-- bad locus.
--
-- WHY THIS DRIVER EXISTS.  `notes/Pencil-informal.md` section (K-out) *What
-- would change this* item 6 says: `R_1` is a FAR object, so `m2/lambda0.m2`'s
-- gauge slice does not reach it, but `dim(R_1 cap L_b) = 1` "would follow from
-- `L_b subseteq.not R_1` as a polynomial non-vanishing", and that is the one
-- piece of (OC-8) that looks symbolically tractable
-- (`notes/Pencil-strategy.md` section 5.3).
--
-- (OC-11) removes the far-ness.  `dim R_1 = 5` is a THEOREM ((OC-10)), so
-- `R_1` is a hyperplane; and `R_1` is contained in the hinge-line span of
-- EVERY `b`-to-`v*` path of `K = (H/X) - e_1` (each edge of such a path
-- contributes `m(u) - m(w) in <C(u,w)>`), so when some path has length exactly
-- 5 -- which is the minimum the isostatic count allows, and which
-- `outerwide.py --wrench` measures at every degree-3-hub end -- the
-- containment is an EQUALITY:
--
--     R_1 = < C(b,u), C(u,w2), C(w2,w3), C(w3,w4), C(w4,x) >,   x in X.
--
-- Then, with `C(b,u) in L_b` and `C(b,a) in L_b` (both `pt(u)` and `pt(a)` lie
-- in the panel `Pi(b)`, `pt(a)` on the meet line `M subseteq Pi(b)`),
--
--     L_b subseteq R_1   <=>   Delta := det[ C(b,u), C(u,w2), C(w2,w3),
--                                           C(w3,w4), C(w4,x), C(b,a) ] = 0,
--
-- a single 6x6 Plueckerian determinant in SEVEN points.  So the far object is
-- gone and the statement is a non-vanishing on the LOCAL frame -- exactly
-- section 5.3's boundary, and the first time in this arc that a `lambda`-side
-- statement lands inside it.
--
-- WHAT THIS DRIVER COMPUTES.
--
--   (M0) THE CONVENTION PIN (mandatory, `README.md` convention 3: an M2
--        driver cannot import a Python primitive, so every re-derivation is a
--        divergence candidate).  `wedge2` here is `exactcore.wedge2` in the
--        `exactcore.PL` index order [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], and
--        `klein` is `pitch.klein`; both are pinned against numbers computed by
--        the Python side on a fixed rational instance.
--
--   (M1) Delta, on the gauge-sliced local frame, is NOT the zero polynomial.
--        Hence at the generic point of that frame `L_b subseteq.not R_1`, so
--        (OUT)'s first disjunct is available -- an identity over the function
--        field, not 38 rational witnesses.
--
--   (M2) Delta FACTORS, and its factorization is the geometry:
--            Delta = (the in-panel collinearity bracket [a, u, b])
--                  * (a form LINEAR in pt(b)),
--        the second factor being the CLOSED FORM of the bad line `C_0` of
--        (OC-13) -- the locus of `pt(b)` inside `Pi(b)` at which
--        `L_b subseteq R_1` and `lambda_1` vanishes identically in `pt(x_1)`.
--        The first factor is the degenerate case in which `C(b,u)` and
--        `C(b,a)` fail to span `L_b` at all, i.e. `pt(a)`, `pt(u)`, `pt(b)`
--        collinear, which no chart point of the class satisfies (it is a
--        coincident hinge line at `b`, `repin.star_generic`'s second clause).
--
--   (M3) The two DEGENERATIONS that would break the reduction are checked to
--        be proper: the five chain lines are independent at the generic point
--        (some 5x5 minor is nonzero), and `Delta` is genuinely of degree 1 in
--        `pt(b)` after the collinearity factor is removed -- so the bad locus
--        is a LINE of the panel and not the whole panel.
--
-- THE GAUGE SLICE, and why it is legitimate (`notes/Pencil-strategy.md`
-- section 5.3's measured boundary: the ungauged whole-frame expansion is a
-- 600 s kill; budget for the local frame).  The datum is: two distinct planes
-- `Pi(b)`, `Pi(c)` of `P^3`; a point `pt(b) in Pi(b)`; a point `pt(c) in
-- Pi(c)`; a point `pt(a)` on `M = Pi(b) cap Pi(c)`; a point `pt(u) in Pi(b)`;
-- a point `pt(w4) in Pi(c)`; and two FREE points `pt(w2)`, `pt(w3)` (the chain
-- interiors with no hub neighbour, which `widened.place_pencil_general` samples
-- from all of space).  `PGL(4)` acts, and it is transitive on
-- (ordered pair of distinct planes, a point of the second off the meet line, a
-- point of the meet line): so
--     Pi(b) = {x4 = 0},  Pi(c) = {x3 = 0},  M = <e1, e2>,
--     pt(c) = (0,0,0,1),  pt(a) = (1,0,0,0)
-- may be imposed with no loss, and `Delta`'s vanishing is `PGL(4)`-invariant
-- (it is a determinant of Pluecker coordinates, so it scales).  `pt(b)` is
-- LEFT FREE inside `Pi(b)`, because (M2)'s whole point is the locus of `pt(b)`.
--
-- STATUS OF THIS OUTPUT (`README.md` convention 1).  Evidence for the
-- workbook, at the same standing as the exact-Q numerics -- NEVER a substitute
-- for Lean, and no blueprint node may take `\leanok` on the strength of an M2
-- run.  What it establishes is a statement about the LOCAL FRAME; carrying it
-- to a class shape needs the chart-to-frame map to be dominant, which is
-- NOT computed here and is named as the residue in the workbook.
--
--   M2 --script notes/scripts/m2/outerwide.m2

print "== (K-out) Step O11: the (OC-8) clause at a length-5-chain end ==";
print("Macaulay2 version " | version#"VERSION");
print "randomness: none";

-- ---------------- (M0) the convention pin ---------------------------------
-- `exactcore.wedge2`, in `exactcore.PL` order, and `pitch.klein` = det4 on
-- decomposable arguments.  Pinned against the Python side on the fixed
-- rational instance p,q,r,s below (computed by
--   python3 -c "... from exactcore import wedge2; from w4.pitch import klein"
-- and recorded here as literals, per README convention 3).

wedge2 = (P, Q) -> (
    idx := {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
    apply(idx, ij -> P#(ij#0) * Q#(ij#1) - P#(ij#1) * Q#(ij#0)));

Rpin = QQ;
ppin = {1,2,3,1}; qpin = {0,1,-1,2}; rpin = {2,0,1,1}; spin = {-1,3,0,1};
w1pin = wedge2(ppin, qpin);
w2pin = wedge2(rpin, spin);
assert(w1pin == {1,-1,2,-5,3,7});          -- exactcore.wedge2(p,q)
assert(w2pin == {6,1,3,-3,-3,1});          -- exactcore.wedge2(r,s)
detpin = det matrix{ppin, qpin, rpin, spin};
assert(detpin == 16);                      -- pitch.det4 == pitch.klein here
print "(M0) OK: wedge2 index order and the bracket/Klein identification agree";
print "     with exactcore.PL / pitch.klein on the pinned rational instance.";

-- ---------------- the gauge-sliced local frame ----------------------------

R = QQ[b1,b2,b3, u1,u2,u3, p1,p2,p3,p4, q1,q2,q3,q4, v1,v2,v4];

ptb = {b1, b2, b3, 0_R};        -- pt(b) in Pi(b) = {x4 = 0}, LEFT FREE
ptc = {0_R, 0_R, 0_R, 1_R};    -- pt(c) in Pi(c) = {x3 = 0}, gauged
pta = {1_R, 0_R, 0_R, 0_R};    -- pt(a) on M = <e1,e2>, gauged
ptu = {u1, u2, u3, 0_R};       -- pt(u) in Pi(b)
ptw2 = {p1, p2, p3, p4};       -- free in space (no hub neighbour)
ptw3 = {q1, q2, q3, q4};       -- free in space
ptw4 = {v1, v2, 0_R, v4};      -- pt(w4) in Pi(c)

C1 = wedge2(ptb, ptu);         -- the chain: b - u - w2 - w3 - w4 - c
C2 = wedge2(ptu, ptw2);
C3 = wedge2(ptw2, ptw3);
C4 = wedge2(ptw3, ptw4);
C5 = wedge2(ptw4, ptc);
Ca = wedge2(ptb, pta);         -- the second generator of the pencil L_b

chain = matrix{C1, C2, C3, C4, C5};
Delta = det matrix{C1, C2, C3, C4, C5, Ca};

-- ---------------- (M3) the two degenerations are proper -------------------

minors5 = flatten entries gens minors(5, chain);
assert(any(minors5, m -> m != 0));
print "(M3a) OK: the five chain hinge lines are independent at the generic";
print "      point (a 5x5 minor of the chain matrix is a nonzero polynomial),";
print "      so R_1 IS their span and dim R_1 = 5 there.";

-- ---------------- (M1) Delta is not identically zero ---------------------

assert(Delta != 0);
print("(M1) OK: Delta != 0 as a polynomial.  deg Delta = " | toString(
        first degree Delta) | ", #terms = " | toString(#terms Delta));
print "     So at the GENERIC POINT of the local frame L_b is NOT contained in";
print "     R_1: (OUT)'s first disjunct is available, as an identity over the";
print "     function field rather than at finitely many rational frames.";

-- ---------------- (M2) the factorization, and C_0's closed form ----------

fac = factor Delta;
print("(M2) the factorization of Delta:");
print("     " | toString fac);
nontriv = select(toList fac, f -> first degree (f#0) > 0);
print("     number of non-unit irreducible factors: " | toString(#nontriv) |
      "  (multiplicities " | toString(apply(nontriv, f -> f#1)) | ")");
assert(#nontriv == 2);
assert(all(nontriv, f -> f#1 == 1));
print "     EXACTLY TWO, each simple: so {Delta = 0} is a union of exactly two";
print "     irreducible hypersurfaces, and (with (M2b) below) exactly two";
print "     distinct lines of the panel.  This is the sentence `the bad locus";
print "     is ONE line plus the degenerate line', tested as itself.";

-- the degenerate factor: pt(a), pt(u), pt(b) collinear INSIDE Pi(b).  In the
-- panel's coordinates (first three homogeneous coordinates, since Pi(b) =
-- {x4 = 0}) that is the 3x3 bracket [a, u, b].
coll = det matrix{{1_R, 0_R, 0_R}, {u1, u2, u3}, {b1, b2, b3}};
assert(coll != 0);
assert(Delta % coll == 0);
print "     the in-panel collinearity bracket [a, u, b] = u2*b3 - u3*b2 DIVIDES";
print "     Delta -- the degenerate factor, at which C(b,u) and C(b,a) fail to";
print "     span L_b at all (a coincident hinge line at b, which";
print "     repin.star_generic rejects).";

C0eq = Delta // coll;
assert(C0eq != 0);
degb = max apply(flatten entries monomials C0eq,
                 m -> (degree(b1, m) + degree(b2, m) + degree(b3, m)));
print("     the complementary factor has degree " | toString degb |
      " in pt(b):");
assert(degb == 1);
print "     LINEAR.  So {Delta = 0} cuts Pi(b) in the collinearity line";
print "     [a,u,b] = 0 together with ONE further line -- and that further";
print "     line IS (OC-13)'s bad locus C_0, now in closed form:";
print("       C_0 :  " | toString C0eq);
print "     (a form linear in pt(b) whose COEFFICIENTS involve only pt(u),";
print "     pt(w2), pt(w3), pt(w4) -- never pt(b) and never pt(x_1).  That is";
print "     (OC-13)'s `T_u and beta_b do not see pt(b)` read symbolically, and";
print "     it is what makes the hub slide of `outerwide.py --slide` legal.)";

-- the two lines are distinct: C_0 is not a multiple of the collinearity line
assert(C0eq % coll != 0);

-- two geometric probes on C_0, both cheap and both informative: does the bad
-- line pass through pt(u) (the other hinge's far end) or through pt(a)?
probeU = sub(C0eq, {b1 => u1, b2 => u2, b3 => u3});
probeA = sub(C0eq, {b1 => 1_R, b2 => 0_R, b3 => 0_R});
print("     C_0 passes through pt(u): " | toString(probeU == 0) |
      ";  through pt(a): " | toString(probeA == 0));
print "(M2b) OK: C_0 and the collinearity line are DISTINCT lines of the panel,";
print "      so the bad locus is a proper line and a generic pt(b) of Pi(b)";
print "      satisfies neither.";

print "";
print "VERDICT.  At a length-5-chain companion end, `L_b subseteq R_1` is the";
print "vanishing of ONE bracket form LINEAR in pt(b) whose coefficients are";
print "far-side brackets: the (OC-8) clause is a local-frame non-vanishing,";
print "generically true, with an explicit bad line C_0.  What this does NOT";
print "establish is the dominance of the chart-to-frame map at an arbitrary";
print "class shape -- named as the residue (OC-16) in the workbook.";
print "OUTERWIDE OK";
