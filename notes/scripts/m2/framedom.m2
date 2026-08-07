-- Phase 39, kernel-(K) FOURTH fan-out direction J -- section (K-frame): the
-- RULING-LINE DETERMINANT LAW at sigma-fixed grid configurations,
-- established as an IDENTITY over the function field.
--
-- Workbook section: `(K-frame)`, claims `(FR-2)`/`(FR-3)`; driver blocks
-- `(FR-M0)`-`(FR-M3)` (the reserved direction-J namespace,
-- `notes/Pencil-labels.md` 2026-08-06 E/J table; the block prefix appends a
-- letter per that file's sanctioned form).
--
-- Read `notes/scripts/m2/README.md` FIRST: the four conventions of this
-- layer bind.  Convention 1 in particular -- an M2 verdict is EVIDENCE for
-- the workbook at exactly the standing of the exact-Q numerics, never a
-- substitute for a Lean proof -- and convention 3, the divergence pin: every
-- primitive re-derived here names its canonical Python home and is pinned by
-- an in-driver check, which is (FR-M0).
--
-- THE OBJECT.  At a sigma-fixed grid configuration (section (K-clos)
-- (AC-2)) every hinge line is a RULING LINE of the fixed quadric
-- {x . x = 0}.  The two ruling families span complementary 3-spaces of
-- Lambda^2 K^4, each family a Veronese conic in its own 3-space, so a 6x6
-- hinge-line determinant -- in particular BOTH chart-to-frame bad divisors,
-- section (K-ann) (ANH-14)'s `C` and section (K-out) (OC-16)'s `Delta` --
-- is nonzero at a grid point IFF its six edges are coloured 3-3 between
-- the families with the three lines in each family pairwise distinct.
-- This driver proves the algebra behind that criterion generically:
--
--   (FR-M0) the convention pin: grid_point and wedge2 (Pluecker order
--           PL = (01,02,03,12,13,23)) re-derived; the generic grid point is
--           isotropic, a same-ruling pair is conjugate; and the FIXED
--           rational instance det[A(2);A(3);A(5);B(2);B(3);B(5)] = 4608 --
--           the number `framedom.py --validate` prints and asserts from the
--           Python side.  Canonical Python homes: closure.grid_point,
--           closure.ruling_A_line / ruling_B_line, exactcore.wedge2 /
--           exactcore.PL.
--   (FR-M1) the determinant law, 6 free parameters:
--             det[A(s1);A(s2);A(s3);B(u1);B(u2);B(u3)]
--                 = 128 * Vdm(s1,s2,s3) * Vdm(u1,u2,u3)
--           identically over QQ(i)[s,u] -- nonzero iff the three parameters
--           in each family are pairwise distinct.
--   (FR-M2) any four ruling-A lines are dependent: rank 3 over the function
--           field (the family's Plueckers span a fixed 3-space).
--   (FR-M3) complementarity: [A(s1..s3) | B(u1..u3)] has rank 6 over the
--           function field (W_A (+) W_B = Lambda^2 K^4).
--
-- randomness: none.  Deterministic; no `random`, no probabilistic shortcuts.
-- Reproduce:  M2 --script notes/scripts/m2/framedom.m2   (from the repo root)

print "== framedom.m2 -- the ruling-line determinant law, generically ==";
print("M2 version: " | version#"VERSION");
print "randomness: none";
print "";

kk = toField(QQ[im]/(im^2+1));
jj = im;   -- the imaginary unit of kk (M2 reserves `ii` for CC)

-- Pluecker order (canonical Python home: exactcore.PL / exactcore.wedge2):
PL = {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)};

------------------------------------------------------------------ (FR-M0) --
-- grid_point (canonical Python home: closure.grid_point):
--   p((s:t),(u:v)) = [s*u+t*v, -i(s*u-t*v), s*v-t*u, -i(s*v+t*u)]
R0 = kk[s,t,u,v,u2];
gp0 = (a,b,c,d) -> {a*c+b*d, -jj*(a*c-b*d), a*d-b*c, -jj*(a*d+b*c)};
dot0 = (x,y) -> sum(4, k -> x#k * y#k);
p = gp0(s,t,u,v);
q = gp0(s,t,u2,1_R0);              -- same ruling-A parameter (s:t)
assert(dot0(p,p) == 0);
assert(dot0(p,q) == 0);
print "OK (FR-M0a) generic grid point isotropic; a same-ruling pair is conjugate";

wedgeK = (P,Q) -> apply(PL, ij -> P#(ij#0)*Q#(ij#1) - P#(ij#1)*Q#(ij#0));
gpK = (a,b,c,d) -> {a*c+b*d, -jj*(a*c-b*d), a*d-b*c, -jj*(a*d+b*c)};
-- ruling lines (canonical Python homes: closure.ruling_A_line / _B_line):
rulAk = s -> wedgeK(gpK(1_kk,s,1_kk,0_kk), gpK(1_kk,s,0_kk,1_kk));
rulBk = w -> wedgeK(gpK(1_kk,0_kk,1_kk,w), gpK(0_kk,1_kk,1_kk,w));
inst = matrix {rulAk 2_kk, rulAk 3_kk, rulAk 5_kk,
               rulBk 2_kk, rulBk 3_kk, rulBk 5_kk};
assert(det inst == 4608_kk);
print "OK (FR-M0b) pinned instance det[A(2);A(3);A(5);B(2);B(3);B(5)] = 4608";

------------------------------------------------------------------ (FR-M1) --
R = kk[x1,x2,x3,y1,y2,y3];
gpR = (a,b,c,d) -> {a*c+b*d, -jj*(a*c-b*d), a*d-b*c, -jj*(a*d+b*c)};
wedgeR = (P,Q) -> apply(PL, ij -> P#(ij#0)*Q#(ij#1) - P#(ij#1)*Q#(ij#0));
rulA = s -> wedgeR(gpR(1_R,s,1_R,0_R), gpR(1_R,s,0_R,1_R));
rulB = w -> wedgeR(gpR(1_R,0_R,1_R,w), gpR(0_R,1_R,1_R,w));
M = matrix {rulA x1, rulA x2, rulA x3, rulB y1, rulB y2, rulB y3};
Vdm = (a,b,c) -> (a-b)*(a-c)*(b-c);
assert(det M == 128_R * Vdm(x1,x2,x3) * Vdm(y1,y2,y3));
print "OK (FR-M1) det[A(s1);A(s2);A(s3);B(u1);B(u2);B(u3)] = 128*Vdm(s)*Vdm(u), identically";

------------------------------------------------------------------ (FR-M2) --
R2 = kk[z1,z2,z3,z4];
gp2 = (a,b,c,d) -> {a*c+b*d, -jj*(a*c-b*d), a*d-b*c, -jj*(a*d+b*c)};
wedge2b = (P,Q) -> apply(PL, ij -> P#(ij#0)*Q#(ij#1) - P#(ij#1)*Q#(ij#0));
rulA2 = s -> wedge2b(gp2(1_R2,s,1_R2,0_R2), gp2(1_R2,s,0_R2,1_R2));
M4 = matrix {rulA2 z1, rulA2 z2, rulA2 z3, rulA2 z4};
assert(rank M4 == 3);
print "OK (FR-M2) four generic ruling-A lines have rank 3 (a fixed 3-space)";

------------------------------------------------------------------ (FR-M3) --
assert(rank M == 6);
print "OK (FR-M3) [A(s1..s3) | B(u1..u3)] has rank 6 over the function field";

print "";
print "PASSED";
