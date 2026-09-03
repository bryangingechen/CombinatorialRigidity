"""
Phase 39, strategy board option C2 -- THE SATISFIABILITY TRACE.

`notes/Pencil-strategy.md` section 8.2 carries **C2** -- *carry `V_bc` general
position as a motive conjunct* -- as **live and unpriced**, and the row names
what must happen first: *"a stronger motive can be UNSATISFIABLE -- needs a
satisfiability trace first (the L6b/F10 precedent)."*  This driver is that
trace.  It answers ONE question:

    is the strengthened motive -- `IsNondegPencilRealization`'s four landed
    conjuncts PLUS `V_bc` general position -- satisfiable at the objects the
    induction's consumer actually hands it?

WHAT THE CONSUMER HANDS THE MOTIVE (read off the landed Lean, not off prose).
`Molecule/Pencil/Escape.lean`'s `pencilPair_of_splitOff_of_habitat` feeds
kernel (K)'s carried `hK` the hypothesis
`HasGenericPencilRealization K 3 (G.splitOff v a b e0)` -- i.e. the motive at
the SPLIT-OFF graph `G' := G - v + ab`, supplied by the induction hypothesis.
So the conjunct would have to hold of a pencil realization of `G'`, and
`V_bc` there is the relative twist system of `H := G' - a` ((T1),
section (K-pitch) Step 1) -- a VERTEX-DELETED SUBGRAPH of the motive's own
object.  `G'` does not know which of its vertices was the split partner, so a
CARRIED conjunct must quantify over an index set of its own; pinning that set
is half the trace.  (`Motive.lean:110-115` is the four-conjunct definition;
`pencil_reduction` (`Induction/ForestSurgery/Reduction.lean:850`) concludes
`forall G, V(G).Nonempty -> P G`, so the motive is universally quantified over
graphs and the conjunct gets no free habitat hypothesis.)

THE THREE READINGS OF "GENERAL POSITION", WHICH ARE NOT EQUIVALENT.
  ESC   `V_bc cap alpha(a) = V_bc cap Lambda^2 pi-hat = 0` -- exactly the
        (PC-Z) escape condition (section (K-pure) Step P3).  This is the
        reading `hK` consumes.
  GEN   `V_bc` a GENERAL point of `Gr(3,6)`, which in particular needs
        `det Gram_B(V_bc) != 0`, i.e. `rank Q|_{V_bc} = 3`.
  IDX   which `(a, b, c)` the conjunct quantifies over.
Modes `--gen` and `--index` decide GEN and IDX; `--gate` and `--sim` decide
ESC.  A trace that silently picks one reading and reports for all three is
the defect this file exists to avoid.

THE MECHANISM THE TRACE FOUND, stated up front because it is what decides the
answer.  At a DEGREE-2 vertex `a` with `N(a) = {b, c}`, every motion of
`H` that welds `b` to `c` extends to a motion of `G'` by `m(a) := m(b)`
(both hinge conditions at `a` become `0 in <C>`), and the extension is
injective, so `dim mot(H/bc) <= dim mot(G')`.  With
`dim V_bc = dim mot(H) - dim mot(H/bc)` (definitional) and
`dim mot(H) >= 6 + def_3(H)` (deficiency is a partition-count lower bound on
the flex count at EVERY realization), this gives, at any realization of `G'`
at the rank target,

    dim V_bc  =  dim mot(G' - a) - dim mot(G')  >=  def_3(G' - a) - def_3(G').

`dim V_bc >= 4` then forces `dim(V_bc cap S) >= 4 + 3 - 6 = 1 > 0` for BOTH
3-dimensional isotropic spaces, so the conjunct at `a` is **unsatisfiable** --
UNSAT PROVED, realization-free, off a purely combinatorial trigger.  The
trigger `def_3(G' - a) - def_3(G') >= 4` FIRES at both (K-res) habitats and
at neither of the five class habitats (`--gate`).

CAPS -- read `notes/scripts/README.md` section 4 convention 8 and
`RESEARCH-ARC.md` section 5 before quoting anything below.  Three caps bind
every figure here, and NONE of them is a proof of nonexistence:
  (i)  the HABITAT SET is the seven of section (K-dom) *Step D4*, not a sweep;
  (ii) SEEDS are the first `n` integers in `1..400` accepted by
       `dominance.base_seed` (its composite `repin.star_generic` gate), so
       every "holds at every seed" is "at every seed drawn";
  (iii) `simple_paths` runs to a length bound, so a reported companion length
       `k` is `None` when no path is that short.
The ONE claim here that does not depend on a cap is the `--gate` inequality
above: it is an argument, and the driver asserts it rather than sampling it.
Everything else, including every "SAT" verdict, is a WITNESS claim (existence)
and is reported as such -- "a witness exists at seed s", never "the conjunct
holds".

HARNESS HAZARDS NAVIGATED (`notes/scripts/README.md` *Harness debt*).  This
file imports **no** `bimage`, `bwin` or `binduc` device, so none of the three
recorded silent hazards is reachable from it: `bimage.pt_in`'s `Lambda^2`->`K^4`
truncation, `bimage.span`'s width-6-only full-rank case, and `bwin.dehom`'s
list-vs-tuple guard defeat.  Every subspace here is built by
`repin.span_basis` / `repin.lambda2_through` / `exactcore.nullspace` and
carries a dimension assert.

Drivers (foreground, one at a time; exact rational arithmetic, no floating
point anywhere; no new source of randomness -- every configuration is
`dominance.base_seed(edges, v, s)` at a printed integer `s`):

    python3 notes/scripts/w4/dsat.py --index      # IDX: the index-set pin
    python3 notes/scripts/w4/dsat.py --gate       # the identity + UNSAT gate
    python3 notes/scripts/w4/dsat.py --sim        # ESC, simultaneously
    python3 notes/scripts/w4/dsat.py --gen        # GEN: the Klein Gram rank
    python3 notes/scripts/w4/dsat.py --validate   # the machinery + a guard
"""
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, nullspace, neighbors, wedge2, hat
from repin import span_basis, lambda2_through, star_generic
from pitch import klein, Q, H_motions_vbc
from pencil_escape import build_rigidity
from nogood_subdiv import deficiency
from kbare_common import verts_of
# Sideways imports into `dominance`'s split-seed / habitat device set.  Only
# `simple_paths` is catalogued in README section 1; `HABITATS`, `seeds_for`,
# `path_span`, `bad_locus_meets` and `class_status` are not, and `outer`/`annih`
# already consume `HABITATS`/`seeds_for`/`simple_paths` -- so this importer
# trips section 2 rule 2's move-down trigger.  Rule 2 forbids a dispatch from
# making the move; the debt item naming every consumer is recorded instead.
# (`seeds_for` reaches `dominance.base_seed`, which is where the composite
# `repin.star_generic` acceptance gate lives; `seeds_at` below re-asserts it.)
from dominance import (HABITATS, seeds_for, simple_paths,
                       path_span, bad_locus_meets, class_status)

# Seed caps (convention 8: disclosed here, and re-printed by every mode).
NSEED_INDEX = 2      # `--index` walks every triple, so it is the expensive one
NSEED_D2 = 3         # `--gate` / `--sim` walk degree-2 triples only
NSEED_GEN = 6        # `--gen` needs a DEEPER sweep: its claim is a max over
                     # seeds, so the cap is the whole strength of the claim
PATHCAP = 9          # `simple_paths` length bound when reporting `k`


# ---------------- the objects a triple names --------------------------------

def triples_of(Gpe, deg=None):
    """Every `(a, b, c, deg a)` with `b < c` in `N_{G'}(a)`, optionally
    filtered to one degree.  This enumerates the conjunct's candidate index
    set exhaustively at the given graph (no cap)."""
    nb = neighbors(Gpe)
    out = []
    for a in sorted(nb, key=str):
        star = sorted(nb[a], key=str)
        if deg is not None and len(star) != deg:
            continue
        for i in range(len(star)):
            for j in range(i + 1, len(star)):
                out.append((a, star[i], star[j], len(star)))
    return out


def motions_of(edges, placed):
    """(motion basis, vertex->index) for a body-hinge framework, via the
    canonical `pencil_escape.build_rigidity`."""
    V = sorted(verts_of(edges), key=str)
    rows, er, C, idx, n = build_rigidity({'edges': edges, 'V': V, 'pt': placed})
    return nullspace(rows), idx


def vbc_of(motions, idx, b, c):
    """`V_bc = span{m(b) - m(c) : m a motion}` -- (T1), section (K-pitch)
    Step 1.  `span_basis` is the canonical spanner."""
    ib, ic = 6 * idx[b], 6 * idx[c]
    return span_basis([[m[ib + k] - m[ic + k] for k in range(6)]
                       for m in motions])


def alpha_at(placed, a):
    """`alpha(a) = {pt(a) ^ x}` -- the lines through `pt(a)`, one of (PC-Z)'s
    two maximal isotropic 3-spaces.  Built by the canonical
    `repin.lambda2_through`, so no third-point perturbation is needed."""
    A = lambda2_through(hat(placed[a]))
    assert len(A) == 3, "alpha(a) is not 3-dimensional"
    return A


def pihat_at(placed, a, b, c):
    """`Lambda^2 pi-hat = <C_ab, C_ac, C_bc>` -- (PC-Z)'s second maximal
    isotropic 3-space.  3-dimensional exactly when `pt a, pt b, pt c` are
    independent, which at a degree-2 `a` is `IsNondegPencilRealization`'s
    FOURTH conjunct (`repin.star_span_ranks`' own docstring says so) and is
    therefore already enforced by `base_seed`'s `star_generic` gate.  Returns
    the basis; the caller asserts its dimension."""
    ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
    return span_basis([wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)])


def hinge_span_at(Gpe, placed, a):
    """`span{C_ax : x in N(a)}` -- the space (T1)/(PC-Z) call `T` when it is
    the 2-dimensional pencil at a degree-2 body."""
    ah = hat(placed[a])
    return span_basis([wedge2(ah, hat(placed[x]))
                       for x in sorted(neighbors(Gpe)[a], key=str)])


def meet_dim(U, S):
    """`dim(U cap S)` by `dim U + dim S - dim(U + S)`; only the dimension is
    needed, so no intersection basis is built.  Same device as
    `dominance.bad_locus_meets`, which `--validate` cross-checks against."""
    return len(U) + len(S) - len(span_basis(list(U) + list(S)))


def escape_at(placed, V, a, b, c):
    """(dim(V cap alpha(a)), dim(V cap Lambda^2 pi-hat)) -- reading ESC holds
    at the triple iff both are 0."""
    A = alpha_at(placed, a)
    B = pihat_at(placed, a, b, c)
    assert len(B) == 3, \
        "Lambda^2 pi-hat degenerate: pt(a), pt(b), pt(c) collinear"
    return meet_dim(V, A), meet_dim(V, B)


def welded_dim(Hed, placed, b, c):
    """`dim mot(H/bc) = dim {m in mot(H) : m(b) = m(c)}`, computed DIRECTLY by
    appending the six welding rows -- so (DM-6)'s extension argument is tested,
    never assumed."""
    VH = sorted(verts_of(Hed), key=str)
    rows, er, C, idx, n = build_rigidity(
        {'edges': Hed, 'V': VH, 'pt': placed})
    ib, ic = 6 * idx[b], 6 * idx[c]
    Delta = []
    for k in range(6):
        row = [F(0)] * (6 * len(VH))
        row[ib + k], row[ic + k] = F(1), F(-1)
        Delta.append(row)
    return len(nullspace(rows + Delta))


def merge_at(edges, b, c):
    """`H/bc`: identify `c` with `b`, dropping the resulting loops.  Used only
    for the combinatorial diagnostic `def_3(H/bc)`."""
    out = []
    for (u, w) in edges:
        u2, w2 = (b if u == c else u), (b if w == c else w)
        if u2 != w2:
            out.append((u2, w2))
    return out


def companion_len(Hed, b, c, placed):
    """(shortest `b`-`c` path length `k` in `H`, `dim S_P`, one shortest path),
    or `(None, None, None)` beyond the `PATHCAP` length bound -- the cap is
    disclosed by every caller."""
    ps = simple_paths(Hed, b, c, maxlen=PATHCAP)
    if not ps:
        return None, None, None
    k = min(len(P) - 1 for P in ps)
    short = [P for P in ps if len(P) - 1 == k]
    dims = [len(path_span(P, placed)) for P in short]
    i = min(range(len(short)), key=lambda j: dims[j])
    return k, dims[i], short[i]


def chain_gram(path, placed):
    """The Klein Gram of the ORDERED chain basis `(C_{P0P1}, ..., C_{P_{k-1}P_k})`
    of `S_P`.  The basis matters: (D1)'s corollary is a statement about the
    chain basis, and `span_basis`' RREF basis of the same space has a
    different (though equally rank-2) Gram."""
    C = [wedge2(hat(placed[path[i]]), hat(placed[path[i + 1]]))
         for i in range(len(path) - 1)]
    return C, [[klein(x, y) for y in C] for x in C]


def d2_row(Gpe, placed, a, b, c, want_paths=True):
    """One degree-2 triple, fully measured.  Everything a mode needs, in one
    pass over the single expensive object (`mot(H)`)."""
    Hed = [e for e in Gpe if a not in e]
    mot, idx = motions_of(Hed, placed)
    V = vbc_of(mot, idx, b, c)
    ma, mb = escape_at(placed, V, a, b, c)
    gram = [[klein(x, y) for y in V] for x in V]
    k, dimSP, short = (companion_len(Hed, b, c, placed) if want_paths
                       else (None, None, None))
    return {'a': a, 'b': b, 'c': c, 'Hed': Hed, 'mot': len(mot), 'idx': idx,
            'V': V, 'dimV': len(V), 'meets': (ma, mb), 'rkQ': rank(gram),
            'gram': gram, 'k': k, 'dimSP': dimSP, 'path': short,
            'defH': deficiency(Hed),
            'defHbc': deficiency(merge_at(Hed, b, c))}


def seeds_at(name, E, v, want):
    ds = seeds_for(E, v, want)
    assert ds, f"{name}: no valid seed in dominance.base_seed's 1..400 range"
    for d in ds:
        # `base_seed` already gated on `repin.star_generic`; re-assert it here
        # so this file's own acceptance gate is explicit (convention 1).
        assert star_generic(d['Gp'], d['placed']), \
            f"{name} seed {d['seed']}: star_generic must hold at an accepted seed"
    return ds


def cap_banner(nseed):
    print(f"   CAPS: 7 habitats (section (K-dom) *Step D4*), {nseed} seed(s)"
          f" per habitat from dominance.base_seed's 1..400 range,"
          f" simple_paths length bound {PATHCAP}.")
    print("   An exhausted cap is NOT a proof of nonexistence"
          " (README section 4 convention 8).\n")


# ---------------- mode: IDX, the index-set pin ------------------------------

def mode_index():
    print("== (DM-5) IDX: the conjunct is well-posed ONLY at degree-2 `a` ==")
    print("   Three reasons, and the FIRST ONE THIS DRIVER FIRST GOT WRONG.")
    print("   NOT a reason: `dim T`.  `T = span{C_ax : x in N(a)}` is")
    print("   2-dimensional at EVERY body of a pencil realization whatever its")
    print("   degree -- concurrency plus coplanarity IS the pencil pin -- so")
    print("   the local hinge data cannot see the two-hinge hypothesis at all.")
    print("   Asserted below at every triple, `deg(a)` = 2, 3 and 4.")
    print("   REASON 1, structural: (T1)'s two-port derivation uses")
    print("   `deg_{G'}(a) = 2` in BOTH directions -- the stress restriction")
    print("   has exactly two deleted fibres, and the converse extends an")
    print("   `H`-motion by `m(a) := m(b) - w1 C_ab = m(c) + w2 C_ac`, which")
    print("   at a third neighbour `d` must also satisfy `m(a) - m(d) in")
    print("   <C_ad>` and does not.  Measured consequence, asserted below:")
    print("   `dim mot(H/bc) > dim mot(G')` at every `deg(a) >= 3` triple, so")
    print("   (DM-6)'s identity FAILS there.")
    print("   REASON 2, measured: `dim V_bc >= 4` at MOST `deg(a) >= 3`")
    print("   triples -- not all, and the census is printed -- and `4 + 3 > 6`")
    print("   then FORCES a nonzero meet with both isotropic 3-spaces.  Every")
    print("   habitat probed carries at least one such triple, so the")
    print("   UNRESTRICTED conjunct is UNSAT at every habitat probed, while")
    print("   the restricted one is decided by `--gate`.\n")
    cap_banner(NSEED_INDEX)
    tot = hi = hi_forced = lo = lo_bad = 0
    for name, E, v, pm, note in HABITATS:
        ds = seeds_at(name, E, v, NSEED_INDEX)
        st = class_status(ds[0], pm)
        print(f"-- {name}  [{st}]  ({note})")
        for d in ds:
            Gp, placed = d['Gp'], d['placed']
            trs = triples_of(Gp)
            motGp, _ = motions_of(Gp, placed)
            byv = {}
            for (a, b, c, deg) in trs:
                if a not in byv:
                    Hed = [e for e in Gp if a not in e]
                    byv[a] = motions_of(Hed, placed)
                # the pencil pin, at EVERY body: all hinges at `a` are
                # concurrent (at `pt a`) and coplanar (in the panel), so
                # their span is 2-dimensional however large `deg(a)` is.
                T = hinge_span_at(Gp, placed, a)
                assert len(T) == 2, \
                    (f"{name} a={a} deg={deg}: dim span{{C_ax}} = {len(T)},"
                     " not 2 -- the pencil pin does not hold at this body")
            n_hi = n_hi_forced = n_lo = n_lo_bad = 0
            dimshi = set()
            for (a, b, c, deg) in trs:
                mot, idx = byv[a]
                V = vbc_of(mot, idx, b, c)
                ma, mb = escape_at(placed, V, a, b, c)
                tot += 1
                if deg == 2:
                    n_lo += 1
                    lo += 1
                    if (ma, mb) != (0, 0):
                        n_lo_bad += 1
                        lo_bad += 1
                else:
                    n_hi += 1
                    hi += 1
                    dimshi.add(len(V))
                    Hed = [e for e in Gp if a not in e]
                    dw = welded_dim(Hed, placed, b, c)
                    assert dw > len(motGp), \
                        (f"{name} a={a} deg={deg}: dim mot(H/bc) = {dw} <="
                         f" dim mot(G') = {len(motGp)} -- (DM-6)'s identity"
                         " would extend past degree 2 after all, which would"
                         " be the FINDING")
                    if len(V) >= 4:
                        assert ma >= 1 and mb >= 1, \
                            "dim V_bc >= 4 without a forced meet -- Grassmann"
                        n_hi_forced += 1
                        hi_forced += 1
                    else:
                        assert len(V) == 3, \
                            f"{name} a={a}: dim V_bc = {len(V)} < 3"
            assert n_hi_forced >= 1, \
                (f"{name} seed {d['seed']}: no forced-bad deg >= 3 triple, so"
                 " the UNRESTRICTED conjunct is not shown UNSAT here")
            print(f"   seed {d['seed']:>3}: {len(trs):>3} triples ="
                  f" {n_lo} at deg 2 + {n_hi} at deg >= 3;"
                  f"  deg >= 3 forced-bad {n_hi_forced}/{n_hi}"
                  f" (dim V_bc in {sorted(dimshi)});"
                  f"  deg 2 bad {n_lo_bad}/{n_lo}")
    print(f"\nINDEX OK: {tot} triples enumerated exhaustively per (graph, seed)."
          " `dim span{C_ax} = 2` at every one of them, degree 2, 3 and 4"
          " alike -- so the local hinge data is BLIND to the index"
          " restriction."
          f"  At deg(a) >= 3: {hi_forced}/{hi} FORCED bad (dim V_bc >= 4,"
          " both meets nonzero every time -- 0 exceptions to the Grassmann"
          " implication), and `dim mot(H/bc) > dim mot(G')` at ALL of them, so"
          " (DM-6)'s identity does not reach degree >= 3 at all;  every"
          " (habitat, seed) carries at least one such triple, asserted, so"
          " the UNRESTRICTED conjunct is UNSAT at every habitat probed."
          "  At deg(a) = 2:"
          f" {lo_bad}/{lo} bad -- so the degree-2 restriction is NOT cosmetic"
          " and is NOT sufficient either; `--gate` decides which degree-2"
          " triples are forced.")
    print("   The pinned index set `{(a, b, c) : deg a = 2, N(a) = {b, c}}` is"
          " a set of ADJACENT EDGE PAIRS, hence derived from `E(G)`: the"
          " GROWING-GROUND-SET filter (strategy section 4.6) is PASSED.  What"
          " is not local is the conjunct's VALUE at an index -- `V_bc` is a"
          " global object of `G - a` -- which is the honest form of the C2"
          " row's first stated problem.")


# ---------------- mode: the dimension identity and the UNSAT gate ----------

def mode_gate():
    print("== (DM-6)/(DM-7) the dimension identity, and the UNSAT gate ==")
    print("   (DM-6)  At a degree-2 `a` with `N(a) = {b, c}`, at ANY pencil")
    print("   realization of `G'` at the rank target:")
    print("       dim V_bc = dim mot(G' - a) - dim mot(G')")
    print("                >= def_3(G' - a) - def_3(G').")
    print("   Proof: `m in mot(H)` with `m(b) = m(c)` extends to `mot(G')` by")
    print("   `m(a) := m(b)` (both hinge conditions at `a` read `0 in <C>`),")
    print("   injectively, so `dim mot(H/bc) <= dim mot(G')`; the reverse")
    print("   inequality is the 6 trivial motions when `G'` is rigid.  And")
    print("   `dim mot(H) >= 6 + def_3(H)` at every realization, deficiency")
    print("   being a partition-count lower bound on the flex count.")
    print("   (DM-7)  Hence `def_3(G' - a) - def_3(G') >= 4` makes the C2")
    print("   conjunct at `a` UNSATISFIABLE: `dim V_bc >= 4` and `4 + 3 > 6`")
    print("   force a nonzero meet with BOTH isotropic 3-spaces, at every")
    print("   realization.  This is UNSAT PROVED, not a failed search.\n")
    cap_banner(NSEED_D2)
    tot = fired = fired_bad = 0
    census = {}
    for name, E, v, pm, note in HABITATS:
        ds = seeds_at(name, E, v, NSEED_D2)
        st = class_status(ds[0], pm)
        dG = deficiency(ds[0]['edges'])
        dGp = deficiency(ds[0]['Gp'])
        print(f"-- {name}  [{st}]  def(G) = {dG}, def(G') = {dGp}")
        for d in ds:
            Gp, placed = d['Gp'], d['placed']
            motGp, _ = motions_of(Gp, placed)
            assert len(motGp) == 6 + dGp, \
                (f"{name} seed {d['seed']}: dim mot(G') = {len(motGp)} !="
                 f" 6 + def(G') = {6 + dGp} -- not a rank-target seed")
            rows = []
            for (a, b, c, deg) in triples_of(Gp, deg=2):
                r = d2_row(Gp, placed, a, b, c, want_paths=False)
                # the welded space, computed DIRECTLY (six welding rows and
                # an independent nullspace), so the extension argument of
                # (DM-6) step 2 is TESTED rather than assumed
                dw = welded_dim(r['Hed'], placed, b, c)
                assert r['dimV'] == r['mot'] - dw, \
                    f"{name}: dim V_bc != dim mot(H) - dim mot(H/bc)"
                assert dw == len(motGp), \
                    (f"{name} a={a}: dim mot(H/bc) = {dw} !="
                     f" dim mot(G') = {len(motGp)} -- (DM-6) FAILS")
                assert r['mot'] >= 6 + r['defH'], \
                    f"{name} a={a}: dim mot(H) < 6 + def(H)"
                gap = r['defH'] - dGp
                assert r['dimV'] >= gap, \
                    f"{name} a={a}: dim V_bc = {r['dimV']} < {gap} = the bound"
                census[gap] = census.get(gap, 0) + 1
                tot += 1
                if gap >= 4:
                    fired += 1
                    assert r['meets'][0] >= 1 and r['meets'][1] >= 1, \
                        (f"{name} a={a}: gate fired at gap {gap} but the"
                         " meets are zero -- (DM-7) FAILS")
                    fired_bad += 1
                rows.append((a, b, c, r))
            nfire = sum(1 for _, _, _, r in rows if r['defH'] - dGp >= 4)
            gaps = sorted({r['defH'] - dGp for _, _, _, r in rows})
            print(f"   seed {d['seed']:>3}: {len(rows):>2} degree-2 triples;"
                  f" def(G'-a) - def(G') in {gaps};"
                  f" gate FIRES at {nfire}/{len(rows)};"
                  f" dim V_bc in {sorted({r['dimV'] for _,_,_,r in rows})}")
            if nfire:
                bad = [str(a) for a, _, _, r in rows if r['defH'] - dGp >= 4]
                print(f"        UNSAT at a in {{{', '.join(bad)}}}")
    print(f"\nGATE OK: {tot} degree-2 triples; the identity"
          " `dim V_bc = dim mot(G'-a) - dim mot(G')` holds at ALL of them"
          " (0 violations, the welded space computed independently each time);"
          f" the gate fires at {fired} of them and every one of those"
          f" {fired_bad} has BOTH meets nonzero, as (DM-7) requires.")
    print(f"   Census of `def(G'-a) - def(G')`: "
          + ", ".join(f"{g}: {n}" for g, n in sorted(census.items())))
    print("   Reading: the conjunct's own stratifying invariant is"
          " `def_3(G - a)`, NOT the companion length `k` of (D3).  This mode"
          " does not compute `k` (it does not need paths); `--gen` does, and"
          " reports the `k` of every degree-2 triple including these.")


# ---------------- mode: ESC, simultaneously across the index set -----------

def mode_sim():
    print("== (DM-8)/(DM-9) reading ESC: is it satisfiable, SIMULTANEOUSLY? ==")
    print("   The conjunct must hold at EVERY index of one realization.  Every")
    print("   landed measurement is per-(shape, split): section (K-dom) *Step")
    print("   D4* measures one split per habitat, section (K-flank) *Step F2*")
    print("   measures 16 splits with a per-split seed.  A CARRIED conjunct")
    print("   needs one seed good at all of them at once, which is what this")
    print("   mode tests.  A `SAT` line is an EXISTENCE claim: a witness at a")
    print("   named seed, never a statement that the conjunct holds.\n")
    cap_banner(NSEED_D2)
    verdicts = []
    for name, E, v, pm, note in HABITATS:
        ds = seeds_at(name, E, v, NSEED_D2)
        st = class_status(ds[0], pm)
        dGp = deficiency(ds[0]['Gp'])
        print(f"-- {name}  [{st}]")
        best = None
        for d in ds:
            Gp, placed = d['Gp'], d['placed']
            good = badl = 0
            forced = 0
            for (a, b, c, deg) in triples_of(Gp, deg=2):
                r = d2_row(Gp, placed, a, b, c, want_paths=False)
                if r['defH'] - dGp >= 4:
                    forced += 1
                if r['meets'] == (0, 0):
                    good += 1
                else:
                    badl += 1
            n = good + badl
            print(f"   seed {d['seed']:>3}: escape holds at {good}/{n}"
                  f" degree-2 triples; {forced} of the {badl} failures are"
                  " FORCED by (DM-7)")
            if best is None or good > best[1]:
                best = (d['seed'], good, n, forced)
        seed, good, n, forced = best
        if good == n:
            verdicts.append((name, st, 'SAT', f"seed {seed}, {n}/{n}"))
        elif forced:
            verdicts.append((name, st, 'UNSAT (proved)',
                             f"{forced} forced triples"))
        else:
            verdicts.append((name, st, 'no witness under cap',
                             f"best {good}/{n} at seed {seed}"))
    print("\nSIM verdicts, one line per habitat:")
    for name, st, verdict, why in verdicts:
        print(f"   {name:>18}  [{st:>7}]  {verdict:<20} ({why})")
    sat = [v for v in verdicts if v[2] == 'SAT']
    uns = [v for v in verdicts if v[2].startswith('UNSAT')]
    nof = [v for v in verdicts if v[2].startswith('no witness')]
    print(f"\nSIM OK: SAT at {len(sat)} habitats"
          f" ({', '.join(n for n, _, _, _ in sat)}) -- an explicit exact-Q"
          " witness at each, so simultaneity across the whole index set is"
          " ACHIEVED there, not merely per-split;"
          f" UNSAT-proved at {len(uns)}"
          f" ({', '.join(n for n, _, _, _ in uns)});"
          f" no witness under cap at {len(nof)}.")
    assert all(st == 'class' for _, st, vv, _ in verdicts if vv == 'SAT'), \
        "a SAT habitat that is not on the pinned class"
    assert all(st == '(K-res)' for _, st, vv, _ in verdicts
               if vv.startswith('UNSAT')), \
        "an UNSAT habitat on the pinned class -- that would be the FINDING"
    print("   And the split is EXACTLY class vs (K-res), asserted: the"
          " uniform conjunct is satisfiable on the pinned `hK` class and"
          " UNSATISFIABLE on the (K-res) half that `hK` also carries (the"
          " 2026-08-02 route-3(b) adjudication).  That is the same"
          " class/(K-res) split (D1) produced for C1, so the option board's"
          " *\"nothing in `(K-dom)` bears on C2\"* is REFUTED.")


# ---------------- mode: GEN, the Klein Gram rank ---------------------------

def mode_gen():
    print("== (DM-10) reading GEN: `V_bc` a GENERAL point of `Gr(3,6)` ==")
    print("   GEN needs `det Gram_B(V_bc) != 0`, i.e. `rank Q|_{V_bc} = 3`.")
    print("   `rank` is lower semicontinuous in the realization, so the MAX")
    print("   over seeds is a lower bound for the generic rank: a triple whose")
    print("   max is 2 has `V_bc` inside the discriminant hypersurface of")
    print("   `Gr(3,6)` at every seed drawn, and GEN is unsatisfiable there.")
    print("   At `k = 3` that is a THEOREM, not a measurement -- (D1)'s")
    print("   basis-free corollary: `V_bc = S_P` is a 3-chain of lines, whose")
    print("   Gram has zero diagonal and only `B(C_1, C_3)` off it.\n")
    cap_banner(NSEED_GEN)
    tot = deg2 = kill = k3 = 0
    for name, E, v, pm, note in HABITATS:
        ds = seeds_at(name, E, v, NSEED_GEN)
        st = class_status(ds[0], pm)
        acc = {}
        for d in ds:
            Gp, placed = d['Gp'], d['placed']
            for (a, b, c, deg) in triples_of(Gp, deg=2):
                r = d2_row(Gp, placed, a, b, c)
                assert r['rkQ'] <= r['dimV'], "Gram rank exceeds dim V_bc"
                if r['k'] == 3:
                    assert r['dimSP'] == 3 and r['dimV'] == 3, \
                        f"{name} a={a}: k = 3 without dim V_bc = dim S_P = 3"
                    # (D1)'s corollary, tested through the Gram SHAPE in the
                    # ORDERED CHAIN basis -- and first, that the chain really
                    # is a basis of `V_bc` (path-sum containment at k = 3 is
                    # an EQUALITY of 3-spaces, (T1)(a) + Step D1).
                    C, g = chain_gram(r['path'], placed)
                    assert len(C) == 3 and len(span_basis(C)) == 3, \
                        f"{name} a={a}: the 3-chain does not span a 3-space"
                    assert span_basis(C + r['V']) == span_basis(r['V']), \
                        f"{name} a={a}: V_bc != S_P at k = 3"
                    assert all(g[i][i] == 0 for i in range(3)), \
                        "a chain Gram has nonzero diagonal (lines not lines?)"
                    nz = [(i, j) for i in range(3) for j in range(3)
                          if i < j and g[i][j] != 0]
                    assert nz == [(0, 2)], \
                        ("the k = 3 chain Gram's only nonzero off-diagonal"
                         f" entry should be B(C_1, C_3); got {nz}")
                    assert rank(g) == 2 and r['rkQ'] == 2, \
                        f"{name} a={a}: k = 3 but rank Q|V_bc = {r['rkQ']}"
                key = (a, b, c)
                prev = acc.get(key)
                acc[key] = (max(prev[0], r['rkQ']) if prev else r['rkQ'],
                            r['k'], r['dimV'])
        n2 = len(acc)
        nk = sum(1 for v_ in acc.values() if v_[0] == 2)
        nk3 = sum(1 for v_ in acc.values() if v_[1] == 3)
        deg2 += n2
        kill += nk
        k3 += nk3
        tot += 1
        ks = sorted({v_[1] for v_ in acc.values()}, key=lambda x: (x is None, x))
        print(f"-- {name:>18} [{st:>7}]: {nk}/{n2} degree-2 triples have"
              f" max-over-seeds rank Q|V_bc = 2 (GEN unsatisfiable);"
              f" {nk3} of them by the k = 3 THEOREM;  k in {ks}")
    print(f"\nGEN OK: {kill} of {deg2} degree-2 triples over {tot} habitats"
          " have `V_bc` in the discriminant hypersurface at every seed drawn"
          f" -- {k3} of them by (D1)'s k = 3 corollary (a theorem, asserted"
          " through the Gram SHAPE, not merely its rank).  Reading GEN is"
          " therefore unsatisfiable at every habitat where that count is"
          " nonzero, INCLUDING the class exemplar theta(3,4,5); the only"
          " survivable reading of *\"general position\"* is ESC, the (PC-Z)"
          " escape.  Cap: a `0` count is `no witness of failure under cap`,"
          " never a proof that GEN is satisfiable there.")


# ---------------- mode: the machinery, and one adversarial guard -----------

def mode_validate():
    print("== the machinery, and the guard that has to reject something ==\n")
    cap_banner(NSEED_D2)
    print("-- (1) `vbc_of` agrees with `pitch.H_motions_vbc` at the split"
          " triple, at every habitat (two independent call paths)")
    for name, E, v, pm, note in HABITATS:
        d = seeds_at(name, E, v, 1)[0]
        Gp, placed, a, b, c = d['Gp'], d['placed'], d['a'], d['b'], d['c']
        ref, dimMot, nVH = H_motions_vbc(E, v, a, b, c, placed)
        Hed = [e for e in Gp if a not in e]
        mot, idx = motions_of(Hed, placed)
        got = vbc_of(mot, idx, b, c)
        assert span_basis(ref) == got, f"{name}: V_bc models disagree"
        assert len(mot) == dimMot, f"{name}: dim mot(H) disagrees"
        print(f"   {name:>18}: dim V_bc = {len(got)},"
              f" dim mot(H) = {dimMot}  AGREE")

    print("\n-- (2) `escape_at` reproduces `dominance.bad_locus_meets` at the"
          " split triple (a different alpha(a) construction: `lambda2_through`"
          " here, a perturbed third point there)")
    for name, E, v, pm, note in HABITATS:
        d = seeds_at(name, E, v, 1)[0]
        Gp, placed, a, b, c = d['Gp'], d['placed'], d['a'], d['b'], d['c']
        Hed = [e for e in Gp if a not in e]
        mot, idx = motions_of(Hed, placed)
        V = vbc_of(mot, idx, b, c)
        mine = escape_at(placed, V, a, b, c)
        theirs = bad_locus_meets(d)
        assert mine == theirs, f"{name}: {mine} != {theirs}"
        print(f"   {name:>18}: meets {mine}  AGREE")

    print("\n-- (3) `meet_dim` agrees with a brute-force intersection basis")
    d = seeds_at(*HABITATS[2][:3], 1)[0]
    placed, a, b, c = d['placed'], d['a'], d['b'], d['c']
    A, B = alpha_at(placed, a), pihat_at(placed, a, b, c)
    for U, S in ((A, B), (B, A), (A, A)):
        # brute force: solve  sum x_i U_i = sum y_j S_j  and read the rank of
        # the resulting U-side vectors
        M = [[U[i][k] for i in range(len(U))] + [-S[j][k] for j in range(len(S))]
             for k in range(6)]
        ker = nullspace(M)
        vecs = [[sum((t[i] * U[i][k] for i in range(len(U))), F(0))
                 for k in range(6)] for t in ker]
        brute = len(span_basis(vecs)) if vecs else 0
        assert meet_dim(U, S) == brute, "meet_dim disagrees with brute force"
    print("   3/3 pairs AGREE (alpha cap pihat, pihat cap alpha, alpha cap"
          " alpha = 3)")

    print("\n-- (4) both (PC-Z) spaces are maximal TOTALLY ISOTROPIC 3-spaces")
    for name, E, v, pm, note in HABITATS:
        d = seeds_at(name, E, v, 1)[0]
        placed, a, b, c = d['placed'], d['a'], d['b'], d['c']
        for S in (alpha_at(placed, a), pihat_at(placed, a, b, c)):
            assert len(S) == 3, f"{name}: not 3-dimensional"
            for x in S:
                assert Q(x) == 0, f"{name}: not isotropic"
                for y in S:
                    assert klein(x, y) == 0, f"{name}: not TOTALLY isotropic"
    print(f"   {len(HABITATS)}/{len(HABITATS)} habitats: alpha(a) and"
          " Lambda^2 pi-hat both 3-dim with `B` identically zero on them")

    print("\n-- (5) `IsNondegPencilRealization`'s FOURTH conjunct is what"
          " makes `Lambda^2 pi-hat` 3-dimensional at a degree-2 `a`, and it"
          " is already enforced by `base_seed`'s `star_generic` gate")
    n = 0
    for name, E, v, pm, note in HABITATS:
        d = seeds_at(name, E, v, 1)[0]
        Gp, placed = d['Gp'], d['placed']
        for (a, b, c, deg) in triples_of(Gp, deg=2):
            r3 = rank([hat(placed[a]), hat(placed[b]), hat(placed[c])])
            assert r3 == 3, f"{name} a={a}: conjunct 4 FAILS at an accepted seed"
            assert len(pihat_at(placed, a, b, c)) == 3
            n += 1
    print(f"   {n}/{n} degree-2 triples: rank[pt a, pt b, pt c] = 3 and"
          " `dim Lambda^2 pi-hat` = 3")

    print("\n-- (6) THE ADVERSARIAL WITNESS the guard must reject (README"
          " section 4 convention 6: a guard observed only passing is"
          " untested).  A CONSTRUCTED collinear triple, not a sampled one.")
    pa = [F(0), F(0), F(0)]
    pb = [F(1), F(2), F(3)]
    pc = [F(2), F(4), F(6)]          # pc = 2*pb: collinear with pa, pb
    pl = {'a': pa, 'b': pb, 'c': pc}
    r3 = rank([hat(pa), hat(pb), hat(pc)])
    assert r3 == 2, f"the constructed witness is not collinear (rank {r3})"
    S = pihat_at(pl, 'a', 'b', 'c')
    # three collinear points span only a 2-space of `K^4`, and `Lambda^2` of a
    # 2-space is 1-dimensional -- so the degeneration is worse than a rank
    # drop by one, which is the point of constructing it rather than sampling.
    assert len(S) == 1, f"collinear pt(a,b,c) but dim Lambda^2 pi-hat = {len(S)}"
    print(f"   REJECTED: rank[pt a, pt b, pt c] = {r3} (conjunct 4 fails) and"
          f" `dim Lambda^2 pi-hat` = {len(S)} < 3, so `escape_at`'s own assert"
          " fires rather than returning a meaningless meet.")
    fired = False
    try:
        escape_at(pl, [[F(1)] + [F(0)] * 5], 'a', 'b', 'c')
    except AssertionError:
        fired = True
    assert fired, "escape_at accepted a degenerate pi-hat"
    print("   PINNED COUNTER-FACT: `repin.star_span_ranks` would report rank"
          " 2 here too -- this is the ONE degeneracy the landed guard does"
          " catch by itself, unlike the free-rotor half of the `plane_basis`"
          " artifact ((OC-7), *Harness debt* item 4), which is why"
          " `base_seed`'s composite `star_generic` is the gate this file"
          " re-asserts rather than a star-rank test.")
    pc2 = [F(2), F(4), F(7)]         # NEGATIVE CONTROL: not collinear
    pl2 = {'a': pa, 'b': pb, 'c': pc2}
    assert rank([hat(pa), hat(pb), hat(pc2)]) == 3
    assert len(pihat_at(pl2, 'a', 'b', 'c')) == 3
    print("   NEGATIVE CONTROL: perturbing pt(c) by one coordinate restores"
          " rank 3 and `dim Lambda^2 pi-hat = 3` -- the guard is not"
          " rejecting everything.")

    print("\n-- (7) the combinatorial diagnostic `def_3(H) - def_3(H/bc)`"
          " predicts `dim V_bc` at every degree-2 triple (the GENERIC value"
          " of (DM-6)'s identity)")
    agree = disagree = 0
    for name, E, v, pm, note in HABITATS:
        d = seeds_at(name, E, v, 1)[0]
        Gp, placed = d['Gp'], d['placed']
        for (a, b, c, deg) in triples_of(Gp, deg=2):
            r = d2_row(Gp, placed, a, b, c, want_paths=False)
            if r['dimV'] == r['defH'] - r['defHbc']:
                agree += 1
            else:
                disagree += 1
    print(f"   {agree} agree, {disagree} disagree -- so at these seeds the"
          " realization is generic for BOTH `H` and `H/bc`, and (DM-6)'s"
          " inequality is an EQUALITY with the combinatorial prediction.")
    assert disagree == 0, "the combinatorial prediction failed somewhere"

    print("\nVALIDATE OK: seven checks, two independent `V_bc` call paths, two"
          " independent `alpha(a)` constructions, a brute-force intersection"
          " cross-check, a constructed adversarial witness with its pinned"
          " counter-fact and negative control, and the combinatorial"
          " prediction of `dim V_bc` at every degree-2 triple.")


# ---------------- main ------------------------------------------------------

MODES = {'--index': mode_index, '--gate': mode_gate, '--sim': mode_sim,
         '--gen': mode_gen, '--validate': mode_validate}


def main():
    args = [a for a in sys.argv[1:] if a in MODES]
    if not args:
        print(__doc__)
        print("modes: " + "  ".join(sorted(MODES)))
        return
    for a in args:
        MODES[a]()
        print()


if __name__ == '__main__':
    main()
