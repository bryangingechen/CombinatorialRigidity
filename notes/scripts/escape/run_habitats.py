import random, sys
from pencil_escape import (sample_pencil_split, escape_test, double_subdivide,
                           build_rigidity, rank)

def K4():
    vs = [0,1,2,3]
    return [(i,j) for i in vs for j in vs if i<j]

def wheel(n):
    """W_n: hub 0, rim 1..n in a cycle."""
    E = []
    for i in range(1, n+1):
        E.append((0, i))
    for i in range(1, n+1):
        j = i+1 if i < n else 1
        E.append((min(i,j), max(i,j)))
    return E

def K5_minus_matching():
    vs=[0,1,2,3,4]
    E=[(i,j) for i in vs for j in vs if i<j]
    E.remove((0,1)); E.remove((2,3))
    return E

def prism_plus_diag():
    # triangular prism: 0-1-2 top, 3-4-5 bottom, verticals 0-3,1-4,2-5
    E=[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]
    E.append((0,4))  # one diagonal -> m=10 = 2*6-2
    return [(min(a,b),max(a,b)) for a,b in E]

def check_full_rank(name, base_edges):
    edges, hubs, chains, allverts = double_subdivide(base_edges)
    # fully generic (not pencil) sanity: place all vertices generic
    import pencil_escape as pe
    rng = random.Random(12345)
    pt = {v: pe.rvec3(rng) for v in allverts}
    data = {'edges': edges, 'V': allverts, 'pt': pt}
    rows, er, C, idx, n = build_rigidity(data)
    rk = rank(rows)
    print(f"  [{name}] full double-subdiv: |V|={len(allverts)} |E|={len(edges)} "
          f"generic rank={rk} target={6*(len(allverts)-1)} tight?={5*len(edges)==6*(len(allverts)-1)}")

def run(name, base_edges, chain_idx=0, nsamples=5, seed0=1000):
    print(f"\n===== HABITAT: {name}  (split chain #{chain_idx}) =====")
    edges, hubs, chains, allverts = double_subdivide(base_edges)
    (u,x,y,w) = chains[chain_idx]
    # degree of hub ends in the double-subdivision = base degree
    from collections import Counter
    deg = Counter()
    for a,bb in edges:
        deg[a]+=1; deg[bb]+=1
    print(f"  base |V0|={len(hubs)} |E0|={len(base_edges)}  chain b={u}(deg{deg[u]}) - v={x} - a={y} - c={w}(deg{deg[w]})")
    check_full_rank(name, base_edges)
    rows_summary = []
    for s in range(nsamples):
        rng = random.Random(seed0 + s)
        data = sample_pencil_split(base_edges, chain_idx, rng)
        res = escape_test(data)
        if not res['ok']:
            print(f"  sample {s}: NOT nullity-1: rank={res['rank']} target={res['target']} "
                  f"nullity={res['nullity']} (skip)")
            rows_summary.append(res)
            continue
        print(f"  sample {s}: rank={res['rank']}=target nullity=1  eq644={res['eq644']} "
              f"r!=0={not res['r_zero']} r.Cab=0:{res['r_perp_Cab']} r.Cac=0:{res['r_perp_Cac']} "
              f"| dimS={res['dimS']}(L2a{res['dim_L2a']}+penb{res['dim_penb']}+penc{res['dim_penc']}) "
              f"| M1={res['M1_works']} M2={res['M2_works']} M3={res['M3_works']} "
              f"r_in_Sperp={res['r_in_Sperp']}")
        rows_summary.append(res)
    return rows_summary

def chain_end_degs(base_edges, chain_idx):
    edges, hubs, chains, allverts = double_subdivide(base_edges)
    from collections import Counter
    deg = Counter()
    for a,bb in edges:
        deg[a]+=1; deg[bb]+=1
    (u,x,y,w) = chains[chain_idx]
    return deg[u], deg[w]

if __name__ == '__main__':
    run("H1 double-subdivided K4 (N2 reproduce)", K4(), chain_idx=0, nsamples=5)

    # W4: hub 0 deg4, rim 1..4 deg3.  chain 0 is a spoke (0-1): b=center deg4, c=rim deg3
    print("\n### W4 chains and their end-degrees:")
    for ci in range(len(wheel(4))):
        print("   chain", ci, "end-degs", chain_end_degs(wheel(4), ci))
    run("H2 double-subdivided W4, SPOKE chain (deg4 hub end)", wheel(4), chain_idx=0, nsamples=5)
    run("H2b double-subdivided W4, RIM chain (deg3/deg3)", wheel(4), chain_idx=4, nsamples=4)

    print("\n### W5 chains and their end-degrees:")
    for ci in range(len(wheel(5))):
        print("   chain", ci, "end-degs", chain_end_degs(wheel(5), ci))
    run("H3 double-subdivided W5, SPOKE chain (deg5 hub end)", wheel(5), chain_idx=0, nsamples=5)

    print("\n### K5-minus-matching chains and their end-degrees:")
    for ci in range(len(K5_minus_matching())):
        print("   chain", ci, "end-degs", chain_end_degs(K5_minus_matching(), ci))
    run("H4 double-subdivided (K5 - matching)", K5_minus_matching(), chain_idx=0, nsamples=4)

    print("\n### prism+diagonal chains and their end-degrees:")
    for ci in range(len(prism_plus_diag())):
        print("   chain", ci, "end-degs", chain_end_degs(prism_plus_diag(), ci))
    run("H5 double-subdivided prism+diagonal", prism_plus_diag(), chain_idx=9, nsamples=4)
