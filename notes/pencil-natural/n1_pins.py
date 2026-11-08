"""PENCIL-NATURAL recon, track R1 (N1): blueprint nodes pinned to dead declarations, N1b.

`R1` and `R2` are the project declarations that `N1Spike.lean`'s kernel closure walk found
unused by restructures R1 and R2 (the planning note's N1a and N1c), transcribed from its
output. `R1p` is `R2` less `keep`, the declarations R1' (N1b) keeps: the loop, base and cut
cases. Prints each node of `blueprint/src/chapter/*.tex` with a pin in `R1p`, its line span
and its other pins, the total lines of such nodes per chapter, and the dead declarations no
node pins. Reads the tree at the working directory, so its figures are for that commit
(`notes/PencilNatural.md` §3 N1).

  python3 notes/pencil-natural/n1_pins.py
"""
import re, sys, glob
R1 = """cross₃_smul_thd Graph.exists_closedEar_two_of_triangle Graph.IsX0Graph.exists_oneEar_or_pendantTriangle
Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero pointJoin_ne_zero extensorThroughPoint_pointJoin
extensorInPanel_pointJoin pencilPair_of_IH hasGenericPencilRealization_of_IH exists_mem_perp_pair_linearIndependent
Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization Graph.IsOpenEar.hasGenericPencilRealization_of_one
exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hasPencilRealization_of_generic hasGenericPencilRealization_of_closedEar_two
pencilPair_of_simple_ncard_eq_three not_pencilHub_of_closedEar_two isLink_cases_of_closedEar_two linearIndependent_pointJoin_triangle
hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization""".split()
R2extra = """exists_reposition_cross_incidences_avoiding finrank_span_pair_le extensorInPanel_screwEquivOfLinearEquiv
extensorThroughPoint_screwEquivOfLinearEquiv le_finrank_toDualPerp_inf hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv
HasPencilPanelRealization.restrict exists_hasPencilPanelRealization_glue finrank_span_triple_le
exists_common_seed_pencilRow_and_polynomials exists_polynomial_ne_zero_of_linearIndependent_pencilRow pencilAnnihRowPoly_eval pencilRow
nbrSlotPointPoly_eval_funext pencilPointJoinPoly_eval pencilPointJoinPoly pencilAnnihRowPoly nbrSlotPointPoly pencilChartNormalPoly
nbrSlotPointPoly_eval pencilChartNormalPoly_eval exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal
hasPencilRealization_of_isLoopAt hasPencilRealization_of_not_twoEdgeConnected hasPencilRealization_of_ncard_le_two
hasDistinctPencilRealization_of_not_twoEdgeConnected pencilDotPoly_eval exists_isNondegPencilRealization_steer pencilDotPoly
ncard_closedNbhd_eq_three_of_demoted IsFin3SelectorOf.isSome_of_ncard_eq_three pencilPair_of_X0 pencil_realization_theorem_of_X0
hasPencilRealization_of_not_simple pencilPair_loop_base_cut pencilPair_of_arms hasGenericPencilRealization_pendant_of_IH
hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI pencilPair_of_not_twoEdgeConnected
extensor_pair_smul pencilRow_mem_rigidityRows_of_mem_edgeSet exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed
span_rigidityRows_pencilChartFramework_eq_of_reseed pencilChartFramework_congr pencilRow_eq_panelRow_pencilChartFramework
pencilChartNormal_congr linearIndepOn_pencilChartNormal_congr exists_independent_pencilRow_subfamily_at_toCoord_of_reseed
finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow not_simple_of_parallel Graph.degree_induce_eq_of_ne
not_pencilNondegFeasible_of_isLoopAt IsNondegPencilRealization.mapExtensor_screwEquivOfLinearEquiv Graph.degree_eq_degree_induce_succ
hasDistinctPencilRealization_of_generic hasPencilRealization_of_distinct exists_smul_eq_extensor_of_extensorThroughPoint_pair
exists_linearIndependent_extensor_pair_through_point pencilPair_of_isLoopAt hlb_induce_of_isNondegPencilRealization_induce_union_singleton
pencilPair_of_ncard_le_two hasGenericPencilRealization_of_ncard_le_two hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton
exists_subset_pair_of_ncard_le_two hasGenericPencilRealization_of_cutEdges_eq_empty""".split()
R2 = R1 + R2extra
print(len(R1), len(R2))
def norm(n):
    return n.replace('CombinatorialRigidity.Molecular.', '')
nodes = []
for f in sorted(glob.glob('blueprint/src/chapter/*.tex')):
    lines = open(f).read().split('\n')
    # find environments with label and lean
    i = 0
    begin_re = re.compile(r'\\begin\{(theorem|lemma|definition|corollary|proposition|remark)\}')
    while i < len(lines):
        m = begin_re.search(lines[i])
        if m:
            env = m.group(1)
            j = i
            while j < len(lines) and ('\\end{%s}' % env) not in lines[j]:
                j += 1
            # include following proof
            k = j + 1
            while k < len(lines) and lines[k].strip() == '' : k += 1
            end = j
            if k < len(lines) and '\\begin{proof}' in lines[k]:
                e = k
                while e < len(lines) and '\\end{proof}' not in lines[e]: e += 1
                end = e
            block = '\n'.join(lines[i:j+1])
            lab = re.search(r'\\label\{([^}]*)\}', block)
            lean = re.search(r'\\lean\{([^}]*)\}', block, re.S)
            pins = [norm(x.strip()) for x in lean.group(1).split(',')] if lean else []
            nodes.append((f.split('/')[-1], lab.group(1) if lab else None, i+1, end+1, pins))
            i = j + 1
        else:
            i += 1
keep = set('pencilPair_of_isLoopAt pencilPair_of_ncard_le_two hasGenericPencilRealization_of_ncard_le_two hasPencilRealization_of_isLoopAt hasPencilRealization_of_not_twoEdgeConnected hasPencilRealization_of_ncard_le_two hasDistinctPencilRealization_of_not_twoEdgeConnected hasPencilRealization_of_not_simple not_simple_of_parallel not_pencilNondegFeasible_of_isLoopAt hasDistinctPencilRealization_of_generic hasPencilRealization_of_distinct exists_linearIndependent_extensor_pair_through_point'.split())
R1p = [x for x in R2 if x not in keep]
print('R1p', len(R1p))
for name, S in [('R1p', R1p)]:
    Sset = set(S)
    print('=====', name)
    tot = 0
    hit = {}
    for (f, lab, a, b, pins) in nodes:
        dead = [p for p in pins if p in Sset]
        if dead:
            alive = [p for p in pins if p not in Sset]
            print(f'{f}:{a}-{b} {lab} ({b-a+1} lines) dead pins {dead}; other pins {alive}')
            tot += b - a + 1
            hit[f] = hit.get(f, 0) + (b - a + 1)
    print('total lines of nodes with a dead pin', tot, hit)
    pinned = {p for (_, _, _, _, pins) in nodes for p in pins}
    print('unpinned dead decls:', [s for s in S if s not in pinned])
