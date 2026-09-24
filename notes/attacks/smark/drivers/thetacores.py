#!/usr/bin/env python3
"""thetacores.py -- the smallest genuine Case-2 cores, run through the existing drivers (smark review 6, 2026-09-23).

A Case-2 core (S27(vi)) is a 2-core with a vertex of degree >= 3.  On a connected core the strict count
5|E| <= 6|V| - 7 gives sum_v (deg v - 2) = 2|E| - 2|V| <= (2|V| - 14)/5, an even number, so a core with at most 16
vertices has at most two vertices of degree >= 3 and hence at most two big vertices: its only degenerate big-point
strata are coincidences (S25 far, S26 distance 2 and adjacent).  The three thetas below are the smallest such cores:

    theta(l1, l2, l3): branch vertices b1, b2 joined by internally disjoint paths of lengths l1, l2, l3; EVERY vertex
    marked, no connectors, so Big = {b1, b2}; 12 vertices, 13 edges, 5|E| = 65 = 6|V| - 7 (tight on the whole graph).
      TH166  theta(1,6,6)  b1 ~ b2             girth 7   (S26's adjacent coincidence)
      TH256  theta(2,5,6)  dist(b1, b2) = 2     girth 7   (S26's distance-2 coincidence)
      TH445  theta(4,4,5)  dist(b1, b2) = 4     girth 8   (S25's far coincidence)
      TH346  theta(3,4,6)  dist(b1, b2) = 3     girth 7   (S25)      -- with the three above, every all-marked theta on
      TH355  theta(3,5,5)  dist(b1, b2) = 3     girth 8   (S25)         12 vertices with girth >= 7 (l1 + l2 + l3 = 13)

The graphs are registered in case2m2.CASES IN MEMORY ONLY: the landed table, and the no-argument case2m2.py run that
iterates over it (drivers/README.md), are untouched.  The rest of the command line goes to the named driver unchanged:

    cd <repo>
    timeout 60   python3 notes/attacks/smark/drivers/thetacores.py check
    timeout 600  python3 -u notes/attacks/smark/drivers/thetacores.py dmgmax --graph TH166 --relations "b2=b1"
    timeout 900  python3 -u notes/attacks/smark/drivers/thetacores.py case2deg --graph TH166 --pair b1 b2 --budget 850
    timeout 1000 python3 -u notes/attacks/smark/drivers/thetacores.py case2m2 --case TH166 --jumpdims --timeout 900
"""
import sys, os, itertools

REPO = os.environ.get("CR_REPO", os.getcwd())
DRV = os.path.join(REPO, "notes", "attacks", "smark", "drivers")
if not os.path.isfile(os.path.join(DRV, "case2m2.py")):
    sys.exit("run from the repository root (or set CR_REPO): case2m2.py not found under notes/attacks/smark/drivers")
sys.path.insert(0, DRV)
import case2m2                           # noqa: E402


def theta(lengths, letters="pqr"):
    """Z, edges for theta(l1, l2, l3); path i's interior vertices are letters[i] + 1 .. letters[i] + (l_i - 1)."""
    Z, E = ["b1", "b2"], []
    for l, x in zip(lengths, letters):
        path = ["b1"] + [f"{x}{j}" for j in range(1, l)] + ["b2"]
        Z += path[1:-1]
        E += list(zip(path, path[1:]))
    return Z, E


THETAS = {
    "TH166": ((1, 6, 6), "theta(1,6,6): big b1 ~ b2 (S26 adjacent coincidence); all 12 vertices marked"),
    "TH256": ((2, 5, 6), "theta(2,5,6): big b1, b2 at distance 2 (S26 distance-2 coincidence); all 12 vertices marked"),
    "TH445": ((4, 4, 5), "theta(4,4,5): big b1, b2 at distance 4 (S25 far coincidence); all 12 vertices marked"),
    # the rest of the 12-vertex habitat-legal thetas (S42(vi): S27(vi)(c)'s list of smallest thetas was incomplete)
    "TH346": ((3, 4, 6), "theta(3,4,6): big b1, b2 at distance 3 (S25 far coincidence); all 12 vertices marked"),
    "TH355": ((3, 5, 5), "theta(3,5,5): big b1, b2 at distance 3 (S25 far coincidence); all 12 vertices marked"),
}
for key, (ls, comment) in THETAS.items():
    Z, E = theta(ls)
    case2m2.CASES[key] = (Z, E, [], comment)


def check():
    """girth, the strict count on every connected vertex subset (exhaustive; induced edges, which is the worst case),
    Big, and dist(b1, b2) -- the facts the docstring asserts."""
    for key in THETAS:
        Z, E, _, comment = case2m2.CASES[key]
        adj = {z: set() for z in Z}
        for a, b in E:
            adj[a].add(b); adj[b].add(a)
        def bfs(src, banned=None):
            d, fr = {src: 0}, [src]
            while fr:
                nx = []
                for x in fr:
                    for y in adj[x]:
                        if y not in d and (x, y) != banned and (y, x) != banned:
                            d[y] = d[x] + 1; nx.append(y)
                fr = nx
            return d
        girth = min(bfs(a, (a, b)).get(b, 10 ** 9) + 1 for a, b in E)
        minslack, nsub = None, 0
        for r in range(2, len(Z) + 1):
            for S in itertools.combinations(Z, r):
                Ss = set(S)
                seen, st = {S[0]}, [S[0]]
                while st:
                    x = st.pop()
                    for y in adj[x] & Ss:
                        if y not in seen:
                            seen.add(y); st.append(y)
                if len(seen) != r:
                    continue
                e = sum(1 for a, b in E if a in Ss and b in Ss)
                if e == 0:
                    continue
                nsub += 1
                sl = 6 * r - 7 - 5 * e
                minslack = sl if minslack is None else min(minslack, sl)
        big = sorted(z for z in Z if len(adj[z]) >= 3)
        print(f"{key}: |V|={len(Z)} |E|={len(E)} girth={girth} Big={big} dist(b1,b2)={bfs('b1')['b2']} "
              f"strict-count min slack={minslack} over {nsub} connected subsets  -- {comment}")


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ("check", "dmgmax", "case2deg", "case2m2"):
        sys.exit("usage: thetacores.py check | dmgmax ARGS | case2deg ARGS | case2m2 ARGS")
    which = sys.argv[1]
    if which == "check":
        return check()
    sys.argv = [f"{which}.py"] + sys.argv[2:]
    if which == "dmgmax":
        import dmgmax as D
    elif which == "case2deg":
        import case2deg as D
    else:
        D = case2m2
    D.main()


if __name__ == "__main__":
    main()
