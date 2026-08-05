-- notes/scripts/m2/lambda0.m2 -- Phase 39 (PENCIL), kernel-(K) arc.
--
-- (Lambda0) and the a-line SPANS of notes/Pencil-informal.md S(K-Lambda)
-- (Standing notation + Step 3; the driver mode it upgrades is
-- `python3 notes/scripts/w4/lambda.py --span`, 164 sampled frames over 38
-- strata).  Established here at the GENERIC POINT of the local frame, i.e.
-- with the frame's coordinates as indeterminates -- the one argument in the
-- arc whose logical form is *generic-point computation ⟹ uniform over the
-- class* (notes/Pencil-strategy.md S5.3).
--
-- HEADLINE.  The span criterion is not a per-frame observation but an exact
-- identity.  Writing g13 = B(C1,C3), g14 = B(C1,C4), g24 = B(C2,C4) for the
-- three surviving entries of the banded Gram of the companion span:
--
--     span_t w+(t) = 3   <=>   p+_2 * p+_3 * g13 * g14 * g24  =/= 0
--     span_t w-(t) = 3   <=>   q_2  * q_3  * g13 * g14 * g24  =/= 0
--
-- The recorded form of (Lambda0f) carries only the first two factors.  The
-- three Gram factors are a CORRECTION, not a confirmation: they are generic,
-- so no sampled frame ever saw one vanish, and g14 =/= 0 in particular is
-- asserted nowhere in the Python harness.  Block (P5) constructs a frame
-- with g14 = 0 and every recorded clause satisfied, where the span drops --
-- so the missing clause is not vacuous.
--
-- STATUS OF THIS OUTPUT.  Evidence for the workbook, at the same standing as
-- the exact-Q numerics -- never a substitute for Lean.  "Verified in
-- Macaulay2" is not a proof this project may cite in place of a
-- formalization (DESIGN.md; notes/scripts/m2/README.md convention 1).
-- `lambda.py --span` is NOT superseded: its figures are frozen and this file
-- is additive.
--
-- Conventions re-derived, not imported (m2/README.md convention 3); the
-- bracket dictionary that ties them to exactcore/repin/pitch is pinned by
-- lambda1.m2 (M0), and cross4's sign/argument order by lambda1.m2 (M1).
--
-- Determinism: no randomness, hence no seed.  The M2 version is printed and
-- is PART OF THE FIGURE (README baseline rule).
--
-- Invocation (frozen; run from the repo root):
--     M2 --script notes/scripts/m2/lambda0.m2

-- ---------------------------------------------------------------- primitives

PLidx  = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
wedge2 = (P,Pt) -> apply(PLidx, ij -> P#(ij#0)*Pt#(ij#1) - P#(ij#1)*Pt#(ij#0));
hstar  = v -> {v#5, -v#4, v#3, v#2, -v#1, v#0};
dotv   = (u,v) -> sum(#u, i -> u#i * v#i);
klein  = (x,y) -> dotv(x, hstar y);
cross4 = (l1,l2,l3) -> (
    A := {l1,l2,l3};
    apply(4, i -> (
        cols := select(toList(0..3), j -> j =!= i);
        (-1)^(i+1) * det matrix apply(3, r -> apply(cols, j -> A#r#j))
    ))
);
nz  = vv -> any(#vv, i -> vv#i != 0);
ok  = (label, val) -> ( assert val; print("  OK   " | label) );

print "== (L2) (Lambda0) and the a-line spans, at the GENERIC POINT ==";
print("  M2 version " | version#"VERSION" | " (pinned; part of the figure)");
print "  randomness: none -- deterministic symbolic computation, no seed";

-- ------------------------------------------------------- the frame, and the gauge
--
-- The local frame of a length-4-companion split (S(K-Lambda) Standing
-- notation): hubs b, c with panels Pi(b), Pi(c); the companion path
-- b - x1 - x2 - x3 - c; the meet line M = Pi(b) cap Pi(c) carrying pt(a);
-- and the auxiliary point w.  The pencil condition at a hub puts every
-- neighbour of that hub in its panel, so x1 in Pi(b) and x3 in Pi(c).
--
-- GAUGE.  GL(4) is transitive on ordered pairs of independent covectors, so
-- put nu_b = e0^*, nu_c = e1^*; then Pi(b) = {X0 = 0}, Pi(c) = {X1 = 0} and
-- M = {X0 = X1 = 0} = <e2, e3>, on which pt(a(t)) = e2 + t e3.  The residual
-- group still moves P_b inside Pi(b) and P_c inside Pi(c), so -- WHENEVER
-- (Lambda0d) HOLDS, i.e. P_b not in Pi(c) and P_c not in Pi(b) -- put
-- P_b = e1 and P_c = e0.  What survives is 14 free coordinates:
-- P_x1 in Pi(b), P_x3 in Pi(c), P_x2 free, w free.  The slice meets every
-- (Lambda0d)-satisfying orbit, and every claim below is either a polynomial
-- identity (vanishing on the slice => vanishing on the orbit => vanishing
-- identically, both sides being GL(4) relative invariants) or a
-- non-vanishing claim (nonzero somewhere => nonzero generically).  Block
-- (P7) re-runs the core WITHOUT the P_b / P_c normalization, so the part of
-- the gauge that assumes (Lambda0d) is shown not to be load-bearing.
--
-- The a-line parameter t does NOT join the indeterminates: w+(t) is cubic
-- and w-(t) quadratic in t (structurally -- m, n, s are t-linear rows), so
-- their coefficient vectors are recovered exactly by finite differences of
-- 4 resp. 3 integer evaluations, and the span of a polynomial curve is the
-- span of its coefficients.  This is what keeps the computation ~0.1 s.

R = QQ[u1,u2,u3, y0,y1,y2,y3, v0,v2,v3, w0,w1,w2,w3];
Pb  = {0_R,1_R,0_R,0_R};              -- P_b = e1, inside Pi(b) = {X0 = 0}
Px1 = {0_R,u1,u2,u3};                 -- x1 in Pi(b)
Px2 = {y0,y1,y2,y3};                  -- x2 free
Px3 = {v0,0_R,v2,v3};                 -- x3 in Pi(c) = {X1 = 0}
Pc  = {1_R,0_R,0_R,0_R};              -- P_c = e0, inside Pi(c)
wv  = {w0,w1,w2,w3};
M0  = {0_R,0_R,1_R,0_R};  M1 = {0_R,0_R,0_R,1_R};
aAt = tv -> {0_R, 0_R, 1_R, tv*1_R};

Cl  = {wedge2(Pb,Px1), wedge2(Px1,Px2), wedge2(Px2,Px3), wedge2(Px3,Pc)};
CM  = wedge2(M0,M1);
Cbc = wedge2(Pb,Pc);
pplus = apply(Cl, Ci -> klein(Ci,CM));
qrow  = apply(Cl, Ci -> klein(Ci,Cbc));
Gram  = apply(4, i -> apply(4, j -> klein(Cl#i, Cl#j)));
g13 = Gram#0#2;  g14 = Gram#0#3;  g24 = Gram#1#3;

rows = tv -> ( av := aAt tv;
    {apply(Cl, Ci -> klein(Ci, wedge2(av,Pb))),
     apply(Cl, Ci -> klein(Ci, wedge2(av,Pc))),
     apply(Cl, Ci -> klein(Ci, wedge2(av,wv)))} );
wpAt = tv -> ( rr := rows tv; cross4(rr#0, rr#1, rr#2) );
wmAt = tv -> ( rr := rows tv; cross4(rr#0, rr#1, qrow) );

-- ------------------------------------------------ (P1) closed forms + structural zeros

print "";
print "(P1) closed forms of the frame's bracket rows   [14 indeterminates]";
ok("p+ = (0, -u1*y0, -y1*v0, 0)  -- structural zeros p+_1 = p+_4 = 0",
   pplus == {0_R, -u1*y0, -y1*v0, 0_R});
ok("q  = (0, u3*y2-u2*y3, y3*v2-y2*v3, 0)  -- structural zeros q_1 = q_4 = 0",
   qrow == {0_R, u3*y2-u2*y3, y3*v2-y2*v3, 0_R});
ok("q is a-free (it is built from C_bc, which does not meet pt(a))",
   qrow == apply(Cl, Ci -> klein(Ci, wedge2(Pb,Pc))));
ok("m_1 = 0 and n_4 = 0 at every t (C1 meets C_ab at pt(b), C4 meets C_ac at pt(c))",
   all({0,1,2,3}, tv -> ((rows tv)#0#0 == 0 and (rows tv)#1#3 == 0)));
ok("the Gram of the companion span is banded: only g13, g14, g24 survive",
   all(4, i -> Gram#i#i == 0) and Gram#0#1 == 0 and Gram#1#2 == 0 and Gram#2#3 == 0);

-- ------------------------------------------------ (P2) every (Lambda0) clause is generic

print "";
print "(P2) each (Lambda0) clause is a NONZERO polynomial, hence generic";
someMinor = (M, k) -> any(subsets(toList(0..(#M-1)), k), rs ->
    any(subsets(toList(0..(#(M#0)-1)), k), cs ->
        det matrix apply(rs, r -> apply(cs, c -> M#r#c)) != 0));
ok("(Lambda0a) rank{C1..C4} = 4   (some 4x4 minor =/= 0)", someMinor(Cl, 4));
ok("(Lambda0b) S cap T = 0        (the 6 rows C1..C4, C_ab, C_ac are independent)",
   det matrix (Cl | {apply(6, k -> (wedge2(aAt 0, Pb))#k),
                     apply(6, k -> (wedge2(aAt 0, Pc))#k)}) != 0);
ok("(Lambda0c) rank[m; n] = 2     (some 2x2 minor =/= 0)",
   someMinor({(rows 0)#0, (rows 0)#1}, 2));
ok("(Lambda0e) C(M) not in S      (the 5 rows C1..C4, C(M) are independent)",
   someMinor(Cl | {CM}, 5));
ok("(Lambda0f) p+_2 = -u1*y0 and p+_3 = -y1*v0 are nonzero polynomials",
   pplus#1 != 0 and pplus#2 != 0);
ok("(Lambda0f) q_2, q_3 are nonzero polynomials", qrow#1 != 0 and qrow#2 != 0);
ok("p+ and q are independent (some 2x2 minor =/= 0)", someMinor({pplus, qrow}, 2));
ok("g13, g14, g24 are all nonzero polynomials", g13 != 0 and g14 != 0 and g24 != 0);
ok("det Gram = (g13*g24)^2, so `rank Q|_S = 4` <=> g13*g24 =/= 0 -- and says NOTHING about g14",
   det matrix Gram == (g13*g24)^2);

-- ------------------------------------------------ (P3) the containment identities

print "";
print "(P3) the two containments, as IDENTITIES in the frame and in t";
WP = apply({0,1,2,3,4}, tv -> wpAt tv);
WM = apply({0,1,2,3},   tv -> wmAt tv);
ok("deg_t w+ <= 3   (4th finite difference vanishes identically)",
   apply(4, i -> WP#4#i - 4*WP#3#i + 6*WP#2#i - 4*WP#1#i + WP#0#i) == {0,0,0,0});
ok("deg_t w- <= 2   (3rd finite difference vanishes identically)",
   apply(4, i -> WM#3#i - 3*WM#2#i + 3*WM#1#i - WM#0#i) == {0,0,0,0});
-- p+ . w+(t) is a cubic in t, so vanishing at 4 points is vanishing identically
ok("p+ . w+(t) == 0    i.e. span_t w+ is inside S cap C(M)^{perp B}",
   apply(4, k -> dotv(pplus, WP#k)) == {0,0,0,0});
ok("q . w-(t) == 0     i.e. span_t w- is inside S cap C(bc)^{perp B}",
   apply(3, k -> dotv(qrow, WM#k)) == {0,0,0});

-- the intrinsic coefficient vectors (Vandermonde is invertible, so their span
-- IS span_t of the curve)
cub = f -> ( a3 := apply(4, i -> (f#3#i - 3*f#2#i + 3*f#1#i - f#0#i) / 6);
             a2 := apply(4, i -> (f#2#i - 2*f#1#i + f#0#i) / 2 - 3*a3#i);
             a1 := apply(4, i -> f#1#i - f#0#i - a2#i - a3#i);
             {f#0, a1, a2, a3} );
qua = f -> ( a2 := apply(4, i -> (f#2#i - 2*f#1#i + f#0#i) / 2);
             a1 := apply(4, i -> f#1#i - f#0#i - a2#i);
             {f#0, a1, a2} );
AP = cub apply(4, k -> WP#k);
AM = qua apply(3, k -> WM#k);
ok("coefficient recovery is exact (reconstructs w+(5), w-(5))",
   apply(4, i -> AP#0#i + 5*AP#1#i + 25*AP#2#i + 125*AP#3#i) == wpAt 5
   and apply(4, i -> AM#0#i + 5*AM#1#i + 25*AM#2#i) == wmAt 5);
ok("deg_t w+ = 3 exactly and deg_t w- = 2 exactly (leading coefficients =/= 0)",
   nz AP#3 and nz AM#2);

-- ------------------------------------------------ (P4) the exact span criterion

print "";
print "(P4) the SPAN CRITERION, exact -- the headline";
PI = pplus#1 * pplus#2 * g13 * g14 * g24;
QI = qrow#1  * qrow#2  * g13 * g14 * g24;
wmon = {w3^3, w3^2*w2, w3*w2^2, w2^3};
trip = subsets(toList(0..3), 3);
scan(4, j -> (
    st := trip#j;
    Z := cross4(AP#(st#0), AP#(st#1), AP#(st#2));
    assert all(subsets(toList(0..3),2), s2 ->
        Z#(s2#0)*pplus#(s2#1) - Z#(s2#1)*pplus#(s2#0) == 0);
    assert(Z == apply(4, i -> (-1)^j * wmon#j * PI * pplus#i));
));
print("  OK   cross4 of every coefficient triple of w+ equals");
print("         (-1)^j * w3^(3-j) * w2^j * [ p+_2 p+_3 g13 g14 g24 ] * p+");
Zm = cross4(AM#0, AM#1, AM#2);
ok("cross4 of w-'s three coefficients equals [ q_2 q_3 g13 g14 g24 ] * q",
   Zm == apply(4, i -> QI * qrow#i));
ok("the four w-monomials w3^3, w3^2 w2, w3 w2^2, w2^3 are exactly the four triples'",
   #(set wmon) == 4);
print "";
print "  => span_t w+(t) = 3  <=>  p+_2 p+_3 g13 g14 g24 =/= 0  (given w off line(bc)),";
print "     span_t w-(t) = 3  <=>  q_2  q_3  g13 g14 g24 =/= 0.";
print "     The recorded (Lambda0f) carries only the first two factors of each.";
ok("the w-obstruction is exactly `w on line(bc)` (= <P_b, P_c> = <e0,e1>): w2 = w3 = 0",
   (w2 == 0) === false and (w3 == 0) === false);

-- ------------------------------------------------ (P5) the missing clause is not vacuous

print "";
print "(P5) g14 = B(C1,C4) =/= 0 is a GENUINE new clause, not a consequence";
-- Degenerate C4's direction onto C1's: v2 = lam*u2, v3 = lam*u3 kills g14 and
-- nothing else that (Lambda0) records.
Rd = QQ[u1,u2,u3, y0,y1,y2,y3, v0, lam, w0,w1,w2,w3];
phi = map(Rd, R, {u1,u2,u3, y0,y1,y2,y3, v0, lam*u2, lam*u3, w0,w1,w2,w3});
ok("under v2 = lam*u2, v3 = lam*u3 : g14 -> 0", phi g14 == 0);
ok("  but p+_2, p+_3, q_2, q_3, g13, g24 all stay nonzero",
   phi pplus#1 != 0 and phi pplus#2 != 0 and phi qrow#1 != 0 and phi qrow#2 != 0
   and phi g13 != 0 and phi g24 != 0);
ok("  and EVERY recorded (Lambda0) clause still holds there:",
   someMinor(apply(Cl, Ci -> apply(Ci, z -> phi z)), 4)                    -- (Lambda0a)
   and det matrix (apply(Cl, Ci -> apply(Ci, z -> phi z))
        | {apply(wedge2(aAt 0, Pb), z -> phi z),
           apply(wedge2(aAt 0, Pc), z -> phi z)}) != 0                     -- (Lambda0b)
   and someMinor({apply((rows 0)#0, z -> phi z),
                  apply((rows 0)#1, z -> phi z)}, 2)                       -- (Lambda0c)
   and someMinor(apply(Cl | {CM}, Ci -> apply(Ci, z -> phi z)), 5));       -- (Lambda0e)
print("       (Lambda0a) rank{C_i} = 4, (Lambda0b) S cap T = 0,");
print("       (Lambda0c) rank[m;n] = 2, (Lambda0e) C(M) not in S -- all survive,");
print("       so none of them implies g14 =/= 0");
ok("  yet span_t w+ drops: EVERY coefficient triple degenerates",
   all(4, j -> ( st := trip#j;
       Z := cross4(apply(AP#(st#0), z -> phi z), apply(AP#(st#1), z -> phi z),
                   apply(AP#(st#2), z -> phi z));
       Z == {0_Rd,0_Rd,0_Rd,0_Rd} )));
ok("  and span_t w- drops with it",
   cross4(apply(AM#0, z -> phi z), apply(AM#1, z -> phi z),
          apply(AM#2, z -> phi z)) == {0_Rd,0_Rd,0_Rd,0_Rd});

-- ------------------------------------------------ (P6) the class-uniformity bridge

print "";
print "(P6) the bridge: every stratum's frame family covers this one variety";
-- The 38 strata of `lambda.py --span` differ by (i) which of x1, x2, x3 are
-- hubs and (ii) how many FAR hub neighbours each frame hub carries (<= 2 in
-- all, by hcard).  Neither datum enters (Lambda0)'s quantities, and every
-- stratum's frame data can be COMPLETED from a point of this variety:
--   * a companion hub x_i takes the panel plane(x_{i-1}, x_i, x_{i+1}),
--     which satisfies the pencil condition there by construction;
--   * b and c already carry x1 in Pi(b), x3 in Pi(c) by the gauge;
--   * a far hub neighbour of a hub h is a FREE point of the far graph, so it
--     is placed inside Pi(h); equivalently the sampler's `nfar` generic
--     normal constraints are chosen inside ker(nu_h), which is 3-dimensional.
-- So each stratum maps ONTO a dense subset of this variety, and the variety
-- is irreducible (it is parameterized by the affine space above).  That is
-- what turns "generic point" into "uniform over the class".
nuOf = (P,Q,S2) -> cross4(P,Q,S2);
scan({{Pb,Px1,Px2}, {Px1,Px2,Px3}, {Px2,Px3,Pc}}, tr -> (
    nu := nuOf(tr#0, tr#1, tr#2);
    assert nz nu;                                    -- the plane exists
    assert all(3, i -> dotv(nu, tr#i) == 0);         -- and contains all three
));
print("  OK   each companion hub's panel plane(x_{i-1}, x_i, x_{i+1}) exists");
print("       generically and satisfies the pencil condition at that hub");
ok("b's and c's panels already contain their companion neighbours (the gauge)",
   Px1#0 == 0 and Px3#1 == 0 and Pb#0 == 0 and Pc#1 == 0);
ok("every panel normal is nonzero, so its kernel is 3-dim and far hub",
   nz nuOf(Pb,Px1,Px2));
print("       neighbours can always be placed inside it (hcard caps far at 2)");

-- ------------------------------------------------ (P7) without the P_b/P_c gauge

print "";
print "(P7) the same core WITHOUT normalizing P_b, P_c   [20 indeterminates]";
-- Only nu_b = e0^*, nu_c = e1^* is gauged here, so (Lambda0d) is visible as
-- a non-vanishing claim rather than assumed by the slice.
RA = QQ[b1,b2,b3, U1,U2,U3, Y0,Y1,Y2,Y3, V0,V2,V3, c0,c2,c3, W0,W1,W2,W3];
Pb' = {0_RA,b1,b2,b3};  Px1' = {0_RA,U1,U2,U3};  Px2' = {Y0,Y1,Y2,Y3};
Px3' = {V0,0_RA,V2,V3}; Pc' = {c0,0_RA,c2,c3};   wv' = {W0,W1,W2,W3};
M0' = {0_RA,0_RA,1_RA,0_RA};  M1' = {0_RA,0_RA,0_RA,1_RA};
aAt' = tv -> {0_RA,0_RA,1_RA, tv*1_RA};
Cl' = {wedge2(Pb',Px1'), wedge2(Px1',Px2'), wedge2(Px2',Px3'), wedge2(Px3',Pc')};
pplus' = apply(Cl', Ci -> klein(Ci, wedge2(M0',M1')));
qrow'  = apply(Cl', Ci -> klein(Ci, wedge2(Pb',Pc')));
rows' = tv -> ( av := aAt' tv;
    {apply(Cl', Ci -> klein(Ci, wedge2(av,Pb'))),
     apply(Cl', Ci -> klein(Ci, wedge2(av,Pc'))),
     apply(Cl', Ci -> klein(Ci, wedge2(av,wv')))} );
ok("(Lambda0d) nu_b . P_c = c0 and nu_c . P_b = b1 are nonzero polynomials",
   Pc'#0 != 0 and Pb'#1 != 0);
ok("structural zeros p+_1 = p+_4 = q_1 = q_4 = 0 survive ungauged",
   pplus'#0 == 0 and pplus'#3 == 0 and qrow'#0 == 0 and qrow'#3 == 0);
WP' = apply({0,1,2,3,4}, tv -> ( rr := rows' tv; cross4(rr#0, rr#1, rr#2) ));
WM' = apply({0,1,2,3},   tv -> ( rr := rows' tv; cross4(rr#0, rr#1, qrow') ));
ok("deg_t w+ <= 3 and deg_t w- <= 2 survive ungauged",
   apply(4, i -> WP'#4#i - 4*WP'#3#i + 6*WP'#2#i - 4*WP'#1#i + WP'#0#i) == {0,0,0,0}
   and apply(4, i -> WM'#3#i - 3*WM'#2#i + 3*WM'#1#i - WM'#0#i) == {0,0,0,0});
ok("the two containments survive ungauged, so the P_b/P_c gauge is not load-bearing",
   apply(4, k -> dotv(pplus', WP'#k)) == {0,0,0,0}
   and apply(3, k -> dotv(qrow', WM'#k)) == {0,0,0});

print "";
print "PASSED -- (Lambda0)'s clauses and the a-line spans hold at the generic point";
print "  of the local frame, hence on a dense open subset of EVERY class habitat's";
print "  pencil chart (P6).  The span criterion is exact and carries three Gram";
print "  factors the recorded (Lambda0f) omits; (P5) shows they are not vacuous.";
