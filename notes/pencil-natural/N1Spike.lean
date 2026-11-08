import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Statements
-- for the consumer analysis only: the two modules outside the closure above that import a
-- `Pencil` module (`Nonvacuity` and `Grade.Stable`)
import CombinatorialRigidity.Nonvacuity
import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Stable

/-!
# PENCIL-NATURAL recon, track R1 (N1): spike

Read-only recon spike (`notes/PencilNatural.md` §3 N1, §4). Not for landing as is. Banked
2026-11-07 in Phase 43a (READS, `notes/Phase43a.md`; the PI's D4), byte-identical but for
this paragraph. Run from the repo root: `lake lean notes/pencil-natural/N1Spike.lean`.
Restructures R1, R1' and R2 below are the planning note's N1a, N1b and N1c. Extended at Phase
43b's open (2026-11-08) by the last section, item 5 (`notes/Phase43b.md`); the output before it is
unchanged.

1. The `d = 3` generic conjunct from the `d ≥ 4` machinery at its bottom rung
   (`liftAttains_of_simple 0`), with the `lem:pencil-d-nondegenerate-three` bridges.
2. `X0Gen` from it, and the pencil realization theorem's statement through
   `pencil_realization_theorem_of_X0` (the minimal restructure).
3. The conditioned pair at every nonempty graph with no `d = 3` induction at all: the bare and
   adjacent-distinct conjuncts from `Graph.graded_pencil_realization_theorem` at `m = 1`, the
   generic one from (1) (the A, B, C shape of `cor:pencil-d-conditioned-pair` at `d = 3`).
4. A kernel-level closure walk over `ConstantInfo` values (`getUsedConstantsAsSet`),
   restricted to constants of `CombinatorialRigidity.*` modules (a mathlib or `Matroid`
   constant cannot name a project constant, so the pruning loses nothing).
5. Phase 43b's slice plan: every constant of the `d = 3` modules tagged by the first restructure
   that kills it, and the three slices' deletion sets checked for surviving users and orphans.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

namespace PencilNaturalSpike

/-- (1a) **C at `d = 3`**: the general lift at `r = 0` attains, and an attaining lift is a
generic realization in dimension `0 + 3`; the bridge `hasGradedGenericPencilRealization_two_iff`
turns the graded `k = 2`, `n = 3` form into `HasGenericPencilRealization K 3`. -/
theorem hasGenericPencilRealization_of_simple [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) (hne : V(G).Nonempty) (hfeas : PencilNondegFeasible K G) :
    HasGenericPencilRealization K 3 G :=
  (hasGradedGenericPencilRealization_two_iff 3 G).1
    (liftAttains_of_simple 0 hS hne hfeas).hasGradedGenericPencilRealization

/-- (1b) The same through the graded wrapper `hasGradedGenericPencilRealization_of_simple` at
`m = 1`, with both `lem:pencil-d-nondegenerate-three` bridges. -/
theorem hasGenericPencilRealization_of_simple' [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) (hne : V(G).Nonempty) (hfeas : PencilNondegFeasible K G) :
    HasGenericPencilRealization K 3 G :=
  (hasGradedGenericPencilRealization_two_iff 3 G).1
    (hasGradedGenericPencilRealization_of_simple (m := 1) le_rfl hS hne
      ((gradedPencilNondegFeasible_two_iff G).2 hfeas))

/-- (1c) **`X0Gen` from C**, statement `X0Gen K α β` byte-identical to `x0Gen`'s. -/
theorem x0Gen [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun _ hS hV _ hfeas =>
    hasGenericPencilRealization_of_simple hS (Set.nonempty_of_ncard_ne_zero (by omega)) hfeas

/-- (2) **The minimal restructure**: `pencil_realization_theorem`'s statement, through the
existing `pencil_realization_theorem_of_X0` with `x0Gen` from C. A keeps its `PencilPair`
motive; its cut-edge arm still uses the generic conjunct of `hIH` at the pieces. -/
theorem pencil_realization_theorem [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencil_realization_theorem_of_X0 x0Dist x0Gen G hspan

/-- (3) **The conditioned pair at every nonempty graph, with no `d = 3` induction**: the bare
and adjacent-distinct conjuncts are `Graph.graded_pencil_realization_theorem` at `m = 1`
(`d = 3`), through `hasGradedPencilRealization_two_iff` and
`hasGradedDistinctPencilRealization_two_iff`; the generic conjunct is C at every graph. -/
theorem pencilPair_of_nonempty [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G := by
  obtain ⟨hbare, hdist⟩ := Graph.graded_pencil_realization_theorem (K := K) (m := 1) le_rfl hne
  exact ⟨fun hS hfeas => hasGenericPencilRealization_of_simple hS hne hfeas,
    fun hS => (hasGradedDistinctPencilRealization_two_iff 3 G).1 (hdist hS),
    (hasGradedPencilRealization_two_iff 3 G).1 hbare⟩

/-- (3') `pencil_realization_theorem`'s statement from (3). -/
theorem pencil_realization_theorem' [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencilPair_of_nonempty G (hspan ▸ Set.univ_nonempty)

/-- (3'') `x0Gen` from (3), as `x0Gen` is now proved. -/
theorem x0Gen' [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun G _ hV _ hfeas =>
    (pencilPair_of_nonempty G (Set.nonempty_of_ncard_ne_zero (by omega))).1 ‹_› hfeas

/-- (R1) `pencilPair_of_nonempty`'s statement under the minimal restructure: A
(`pencilPair_of_arms`, `PencilPair` motive) with `pencilPair_of_X0` at `x0Dist` and the `x0Gen`
of C in place of `pencilPair_of_IH`. -/
theorem pencilPair_of_nonempty_R1 [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G :=
  pencilPair_of_arms (fun G hloop hV _ hIH => pencilPair_of_X0 x0Dist x0Gen G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => pencilPair_of_X0 x0Dist x0Gen G hloop hV hIH) G hne

/-- (R1') A keeps its `d = 3` objects and its `PencilPair` motive, but no case reads the generic
conjunct of `hIH`: the generic conjunct at `G` itself is C (directly at a cut edge, through
`x0Gen` at a simple two-edge-connected `G`). The loop and base cases are as landed
(`pencilPair_of_isLoopAt`, `pencilPair_of_ncard_le_two`, the latter non-inductive). The three
cases on at least three bodies are `pencilPair_of_X0`'s split written out, as `pencilPair_of_X0`
names `pencilPair_of_not_twoEdgeConnected` and so its generic glue; the cut case keeps the landed
bare and adjacent-distinct arms (`hasPencilRealization_of_not_twoEdgeConnected` and its distinct
form). -/
theorem pencilPair_of_nonempty_R1' [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G := by
  classical
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have step : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
      PencilPair K 3 G := by
    intro G hloop hV hIH
    by_cases h2ec : G.TwoEdgeConnected
    · by_cases hs : G.Simple
      · have hd := x0Dist (K := K) G hs hV h2ec
        exact ⟨fun _ hf => x0Gen G hs hV h2ec hf, fun _ => hd, hasPencilRealization_of_distinct hd⟩
      · exact ⟨fun h => absurd h hs, fun h => absurd h hs,
          hasPencilRealization_of_not_simple G hloop hV hs hIH⟩
    · exact ⟨fun hS hfeas => hasGenericPencilRealization_of_simple hS
          (Set.nonempty_of_ncard_ne_zero (by omega)) hfeas,
        fun hS => hasDistinctPencilRealization_of_not_twoEdgeConnected hn h2ec
          (fun G' hle' hne' hlt' => (hIH G' hne' hlt').2.1 (hS.mono hle')),
        hasPencilRealization_of_not_twoEdgeConnected hn h2ec
          (fun G' hne' hlt' => (hIH G' hne' hlt').2.2)⟩
  refine Graph.pencil_reduction (n := 3) (Graph.six_le_bodyBarDim (by norm_num)) ?_
    (fun G hloop hne hV2 => pencilPair_of_ncard_le_two hloop hne hV2)
    (fun G hloop hV _ hIH => step G hloop hV hIH) (fun G hloop hV _ hIH => step G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => step G hloop hV hIH) G hne
  rintro G ⟨e, x, hloopAt⟩ IH
  refine pencilPair_of_isLoopAt hloopAt (IH (G ＼ ({e} : Set β)) ?_ (Or.inr ⟨?_, ?_⟩))
  · rw [Graph.vertexSet_deleteEdges]; exact ⟨x, hloopAt.left_mem⟩
  · rw [Graph.vertexSet_deleteEdges]
  · rw [Graph.edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_lt_of_mem hloopAt.edge_mem

/-- (R1') `pencil_realization_theorem`'s statement from (R1'). -/
theorem pencil_realization_theorem_R1' [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencilPair_of_nonempty_R1' G (hspan ▸ Set.univ_nonempty)

/-- (R2) `pencilPair_of_nonempty`'s statement as the `m = 1` instance of
`Graph.graded_pencil_conditioned_pair` (`cor:pencil-d-conditioned-pair`), through the three
`d = 3` bridges and `gradedPencilNondegFeasible_two_iff`. -/
theorem pencilPair_of_nonempty_R2 [Finite α] [Finite β] [Infinite K] (G : Graph α β)
    (hne : V(G).Nonempty) : PencilPair K 3 G := by
  obtain ⟨hbare, hdist, hgen⟩ := Graph.graded_pencil_conditioned_pair (K := K) (m := 1) le_rfl hne
  exact ⟨fun hS hfeas => (hasGradedGenericPencilRealization_two_iff 3 G).1
      (hgen hS ((gradedPencilNondegFeasible_two_iff G).2 hfeas)),
    fun hS => (hasGradedDistinctPencilRealization_two_iff 3 G).1 (hdist hS),
    (hasGradedPencilRealization_two_iff 3 G).1 hbare⟩

/-- (R2) `pencil_realization_theorem`'s statement from (R2). -/
theorem pencil_realization_theorem_R2 [Nonempty α] [Finite α] [Finite β] [Infinite K]
    (G : Graph α β) (hspan : V(G) = Set.univ) : PencilPair K 3 G :=
  pencilPair_of_nonempty_R2 G (hspan ▸ Set.univ_nonempty)

/-- (R2) `x0Gen`'s statement from (R2). -/
theorem x0Gen_R2 [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun G hS hV _ hfeas =>
    (pencilPair_of_nonempty_R2 G (Set.nonempty_of_ncard_ne_zero (by omega))).1 hS hfeas

end PencilNaturalSpike

end CombinatorialRigidity.Molecular

/-! ## The closure walk -/

open Lean Meta Elab Command

/-- The module of a constant, or `none` for one declared in this file. -/
def spikeModuleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Whether a constant is the project's (or this file's). -/
def spikeIsProj (env : Environment) (n : Name) : Bool :=
  match spikeModuleOf env n with
  | some m => m.getRoot == `CombinatorialRigidity
  | none => true

/-- The transitive closure of `root` over `ConstantInfo.getUsedConstantsAsSet` (type and value),
expanded only through project constants. Also counts the project theorems whose value was not
available (a `thmInfo` replaced by an axiom-like stub would show here). -/
def spikeClosure (env : Environment) (root : Name) : NameSet × Nat := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut noValue := 0
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => noValue := noValue + 1
    | some ci =>
      if ci.isAxiom then noValue := noValue + 1
      for m in ci.getUsedConstantsAsSet do
        if !seen.contains m && spikeIsProj env m then stack := stack.push m
  return (seen, noValue)

/-- The names checked: every `d = 3` main-component or reduction statement and step. -/
def spikeWatch : List String :=
  ["pencilPair_of_nonempty", "pencilPair_of_IH", "pencilPair_of_arms",
    "hasGenericPencilRealization_of_IH", "x0Gen", "x0Dist", "X0Gen", "X0Dist",
    "pencil_realization_theorem", "pencil_realization_theorem_of_X0", "pencilPair_of_X0",
    "PencilPair", "pencilPair_loop_base_cut", "pencilPair_of_not_twoEdgeConnected",
    "pencilPair_of_isLoopAt", "pencilPair_of_ncard_le_two",
    "hasPencilRealization_of_not_simple", "Graph.pencil_reduction",
    "hasGenericPencilRealization_pendant_of_IH",
    "hasGenericPencilRealization_of_cutEdges_eq_empty",
    "hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton",
    "hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI",
    "hasGenericPencilRealization_of_ncard_le_two",
    "Graph.IsX0Graph.exists_oneEar_or_pendantTriangle",
    "Graph.IsOpenEar.hasGenericPencilRealization_of_one",
    "hasGenericPencilRealization_of_closedEar_two",
    "hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization",
    "Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero",
    "pencilPair_of_simple_ncard_eq_three",
    "exists_isNondegPencilRealization_steer",
    "exists_isNondegPencilRealization_restrict_of_demoted",
    "Graph.X0Attains.of_twoEdgeConnected", "Graph.IsX0Graph.x0Attains",
    "Graph.graded_pencil_realization_theorem", "liftAttains_of_simple",
    "PencilNaturalSpike.hasGenericPencilRealization_of_simple"]

/-- `n` is the watched project name `pat` (a spike constant matches only a pattern naming the
spike's namespace, so a spike `x0Gen` is not reported as the landed one). -/
def spikeMatches (n : Name) (pat : String) : Bool :=
  let s := n.toString
  let spike := (s.splitOn "PencilNaturalSpike").length > 1
  let patSpike := (pat.splitOn "PencilNaturalSpike").length > 1
  (spike == patSpike) && (s == pat || s.endsWith ("." ++ pat))

/-- Report, for `root`: the closure size, the theorems with no value, the watched names present
and absent, and the closure's members in the given modules. -/
def spikeReport (root : Name) (mods : List Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do throwError "unknown {root}"
  let (cl, nv) := spikeClosure env root
  let present := spikeWatch.filter fun p => cl.toList.any fun n => spikeMatches n p
  let absent := spikeWatch.filter fun p => !(cl.toList.any fun n => spikeMatches n p)
  logInfo m!"ROOT {root}: {cl.size} project constants in closure; {nv} without a value\n\
    PRESENT: {present}\nABSENT: {absent}"
  for md in mods do
    let mem := cl.toList.filter fun n =>
      spikeModuleOf env n == some md && !n.isInternalDetail
    logInfo m!"  in {md}: {mem.length}: {mem}"

elab "#spike_report " root:ident mods:ident* : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  spikeReport n (mods.toList.map (·.getId))

-- positive control: the current `x0Gen` must reach `hasGenericPencilRealization_of_IH`
#spike_report CombinatorialRigidity.Molecular.x0Gen

-- (1a): C at d = 3
open CombinatorialRigidity.Molecular in
#spike_report PencilNaturalSpike.hasGenericPencilRealization_of_simple
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2
  CombinatorialRigidity.Molecular.Molecule.Pencil.X0
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericBase
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericSteer
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericEar
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericTriangle
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GoodEar
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Statements

-- (1b), (1c)
open CombinatorialRigidity.Molecular in
#spike_report PencilNaturalSpike.hasGenericPencilRealization_of_simple'
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen

-- (2): the minimal restructure
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2

-- (3): no d = 3 induction
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem'
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2
  CombinatorialRigidity.Molecular.Molecule.Pencil.X0
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen'

-- the current `d ≥ 3` graded A (bare and distinct conjuncts)
#spike_report Graph.graded_pencil_realization_theorem
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2
  CombinatorialRigidity.Molecular.Molecule.Pencil.X0

open CombinatorialRigidity.Molecular in
#print axioms PencilNaturalSpike.hasGenericPencilRealization_of_simple
#print axioms CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen
#print axioms CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem
#print axioms CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem'

/-! ## The consumer analysis

`D` is the set of modules under `Pencil` but not `Pencil.Grade` (the `d = 3` chapter's own
modules). The roots are every project constant outside `D` (all of `Pencil.Grade`, `Nonvacuity`,
the rest of the project) together with the main results: before, the landed `x0Dist`, `x0Gen`,
`pencilPair_of_nonempty`, `pencil_realization_theorem`; after a restructure, `x0Dist` and the
spike's replacements. A constant of `D` is consumed when reachable from the roots. Reported: the
public constants of `D` reachable before and not after (newly dead), by module, with their
declaration line spans. -/

/-- Whether `n` is in a `d = 3` chapter module (`D`). -/
def spikeInD (env : Environment) (n : Name) : Bool :=
  match spikeModuleOf env n with
  | some m =>
    (`CombinatorialRigidity.Molecular.Molecule.Pencil).isPrefixOf m &&
      !(`CombinatorialRigidity.Molecular.Molecule.Pencil.Grade).isPrefixOf m
  | none => false

/-- Reachability from `roots` through project constants. A constant with an entry in `subst`
is read with its replacement's body: the restructure keeps its name and statement and changes its
proof, so its consumers (e.g. `Nonvacuity`) keep consuming it. -/
def spikeReach (env : Environment) (roots : Array Name) (subst : List (Name × Name) := []) :
    NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let src := (subst.lookup n).getD n
    if let some ci := env.find? src then
      for m in ci.getUsedConstantsAsSet do
        if !seen.contains m && spikeIsProj env m then stack := stack.push m
  return seen

def spikeLandedMain : List Name :=
  [`CombinatorialRigidity.Molecular.x0Dist, `CombinatorialRigidity.Molecular.x0Gen,
    `CombinatorialRigidity.Molecular.pencilPair_of_nonempty,
    `CombinatorialRigidity.Molecular.pencil_realization_theorem]

/-- `after` lists the replacements of `x0Gen`, `pencilPair_of_nonempty` and
`pencil_realization_theorem`, in that order. -/
def spikeDeadReport (label : String) (after : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let outside := env.constants.fold (init := #[]) fun acc n _ =>
    if (spikeModuleOf env n).isSome && spikeIsProj env n && !spikeInD env n then acc.push n
    else acc
  let before := spikeReach env (outside ++ spikeLandedMain.toArray)
  let subst := spikeLandedMain.tail.zip after
  let afterR := spikeReach env (outside ++ spikeLandedMain.toArray) subst
  let dead := before.toList.filter fun n =>
    spikeInD env n && !afterR.contains n && !n.isInternalDetail
  let mut byMod : Std.HashMap Name (Array (Name × Nat)) := {}
  for n in dead do
    let some m := spikeModuleOf env n | continue
    let rng ← liftCoreM (findDeclarationRanges? n)
    let lines : Nat := match rng with
      | some r => r.range.endPos.line + 1 - r.range.pos.line
      | none => 0
    byMod := byMod.insert m ((byMod.getD m #[]).push (n, lines))
  let total := dead.length
  let totLines := byMod.fold (init := (0 : Nat)) fun acc _ a =>
    acc + a.foldl (fun (s : Nat) p => s + p.2) 0
  logInfo m!"{label}: {total} constants of D newly dead, {totLines} declaration lines"
  for (m, a) in byMod.toList do
    let ls := a.foldl (fun (s : Nat) p => s + p.2) 0
    logInfo m!"  {m}: {a.size} decls, {ls} lines: {a.toList.map fun p => m!"{p.1} ({p.2})"}"

elab "#spike_dead " label:str after:ident* : command => do
  let ns ← after.toList.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  spikeDeadReport label.getString ns

-- sanity: the landed main results as the "after" roots must give no newly dead constant
#spike_dead "control" CombinatorialRigidity.Molecular.x0Gen
  CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  CombinatorialRigidity.Molecular.pencil_realization_theorem

-- (R1) the minimal restructure
#spike_dead "R1" CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem

-- (R1') A keeps its d = 3 objects, with no generic conjunct read from hIH
#spike_dead "R1'" CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1'
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem_R1'

-- (R2) d = 3 as the m = 1 instance
#spike_dead "R2" CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen_R2
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R2
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem_R2

#print axioms CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1
#print axioms CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R2
#print axioms CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1'

-- closure of the R1 and R2 forms of the general theorem
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R2
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2
  CombinatorialRigidity.Molecular.Molecule.Pencil.X0
  CombinatorialRigidity.Molecular.Molecule.Pencil.ArmsAssembly
  CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Statements

/-! ## Statement identity: each replacement's type is the landed declaration's, syntactically
(after renaming universe parameters positionally) -/

def spikeSameType (landed spike : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some a := env.find? landed | throwError "unknown {landed}"
  let some b := env.find? spike | throwError "unknown {spike}"
  let ok := a.levelParams.length == b.levelParams.length &&
    a.type == b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param)
  logInfo m!"SAME TYPE {landed} ~ {spike}: {ok}"

elab "#spike_same " a:ident b:ident : command => do
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  spikeSameType na nb

#spike_same CombinatorialRigidity.Molecular.x0Gen
  CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen
#spike_same CombinatorialRigidity.Molecular.x0Gen
  CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen_R2
#spike_same CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1
#spike_same CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1'
#spike_same CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R2
#spike_same CombinatorialRigidity.Molecular.pencil_realization_theorem
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem
#spike_same CombinatorialRigidity.Molecular.pencil_realization_theorem
  CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem_R2

-- closure of the R1' form
#spike_report CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1'
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair
  CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2
  CombinatorialRigidity.Molecular.Molecule.Pencil.X0

/-! ## The slice plan of Phase 43b (LIFT3), added at its open (2026-11-08)

`notes/Phase43b.md` slices N1c into three Lean commits: N1a (`x0Gen` from C), then N1b's deletions
with `pencilPair_of_nonempty` rerouted to R2's form, then the rest of N1c's. Two reports, appended
here so that the earlier output above is unchanged.

* `#n1_liveness`: every public constant of `D` (as above), tagged by the first restructure under
  which it is dead (`R1`, then `R1'`, then `R2`), `UNREACHED` if no root reaches it even at HEAD,
  or `LIVE` if R2 still uses it; per module, the counts and the non-`LIVE` constants with their
  lines.
* `#n1_slices`: the slices' deletion sets (`n1Slice1` … `n1Slice3`, cumulative). For each, (a)
  the surviving constants that use a deleted one (a slice must restate those, or delete them),
  and (b) its orphans, project constants of any module whose every user is deleted, to a fixpoint
  (auxiliary declarations followed but not reported). Read against the environment at HEAD: a
  slice's new proofs are not in it, so an orphan the slice's own new proof uses (R2's form uses
  the three `d = 3` bridges) is reported and is not one. -/

/-- The first restructure under which each constant of `D` is dead. -/
def n1LiveAfter (env : Environment) (after : List Name) : NameSet :=
  let outside := env.constants.fold (init := #[]) fun acc n _ =>
    if (spikeModuleOf env n).isSome && spikeIsProj env n && !spikeInD env n then acc.push n
    else acc
  spikeReach env (outside ++ spikeLandedMain.toArray) (spikeLandedMain.tail.zip after)

elab "#n1_liveness" : command => do
  let env ← getEnv
  let landed : List Name := [`CombinatorialRigidity.Molecular.x0Gen,
    `CombinatorialRigidity.Molecular.pencilPair_of_nonempty,
    `CombinatorialRigidity.Molecular.pencil_realization_theorem]
  let r1 : List Name := [`CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen,
    `CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1,
    `CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem]
  let r1p : List Name := [`CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen,
    `CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R1',
    `CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem_R1']
  let r2 : List Name := [`CombinatorialRigidity.Molecular.PencilNaturalSpike.x0Gen_R2,
    `CombinatorialRigidity.Molecular.PencilNaturalSpike.pencilPair_of_nonempty_R2,
    `CombinatorialRigidity.Molecular.PencilNaturalSpike.pencil_realization_theorem_R2]
  let before := n1LiveAfter env landed
  let a1 := n1LiveAfter env r1
  let a1p := n1LiveAfter env r1p
  let a2 := n1LiveAfter env r2
  let mut byMod : Std.HashMap Name (Array String) := {}
  for (n, _) in env.constants.toList do
    unless spikeInD env n do continue
    if n.isInternalDetail then continue
    let some rng ← liftCoreM (findDeclarationRanges? n) | continue
    let some m := spikeModuleOf env n | continue
    let tag :=
      if !before.contains n then "UNREACHED"
      else if !a1.contains n then "R1"
      else if !a1p.contains n then "R1'"
      else if !a2.contains n then "R2"
      else "LIVE"
    byMod := byMod.insert m ((byMod.getD m #[]).push s!"{tag} {rng.range.pos.line} {n}")
  let mods := byMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (m, a) in mods do
    let cnt (t : String) := (a.filter fun s => s.startsWith (t ++ " ")).size
    let shown := (a.filter fun s => !s.startsWith "LIVE ").qsort (· < ·)
    logInfo m!"MODULE {m}: {a.size} constants; UNREACHED {cnt "UNREACHED"}, R1 {cnt "R1"}, \
      R1' {cnt "R1'"}, R2 {cnt "R2"}, LIVE {cnt "LIVE"}\n{"\n".intercalate shown.toList}"

#n1_liveness

set_option linter.style.longLine false in
/-- Slice 1 (N1a): `R1`'s twenty. -/
def n1Slice1 : List Name :=
  [`CombinatorialRigidity.Molecular.cross₃_smul_thd,
   `Graph.exists_closedEar_two_of_triangle, `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle,
   `Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero,
   `CombinatorialRigidity.Molecular.pointJoin_ne_zero,
   `CombinatorialRigidity.Molecular.extensorThroughPoint_pointJoin,
   `CombinatorialRigidity.Molecular.extensorInPanel_pointJoin,
   `CombinatorialRigidity.Molecular.pencilPair_of_IH,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_IH,
   `CombinatorialRigidity.Molecular.exists_mem_perp_pair_linearIndependent,
   `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization,
   `Graph.IsOpenEar.hasGenericPencilRealization_of_one,
   `CombinatorialRigidity.Molecular.exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero,
   `CombinatorialRigidity.Molecular.hasPencilRealization_of_generic,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two,
   `CombinatorialRigidity.Molecular.pencilPair_of_simple_ncard_eq_three,
   `CombinatorialRigidity.Molecular.not_pencilHub_of_closedEar_two,
   `CombinatorialRigidity.Molecular.isLink_cases_of_closedEar_two,
   `CombinatorialRigidity.Molecular.linearIndependent_pointJoin_triangle,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization]

set_option linter.style.longLine false in
/-- Slice 2: `R1'`'s fifty-two less the three of `lem:pencil-projective-transport`. -/
def n1Slice2 : List Name :=
  [`CombinatorialRigidity.Molecular.HasPencilPanelRealization.restrict,
   `CombinatorialRigidity.Molecular.IsFin3SelectorOf.isSome_of_ncard_eq_three,
   `CombinatorialRigidity.Molecular.IsNondegPencilRealization.mapExtensor_screwEquivOfLinearEquiv,
   `CombinatorialRigidity.Molecular.exists_common_seed_pencilRow_and_polynomials,
   `CombinatorialRigidity.Molecular.exists_hasPencilPanelRealization_glue,
   `CombinatorialRigidity.Molecular.exists_independent_pencilRow_subfamily_at_toCoord_of_reseed,
   `CombinatorialRigidity.Molecular.exists_isNondegPencilRealization_steer,
   `CombinatorialRigidity.Molecular.exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal,
   `CombinatorialRigidity.Molecular.exists_polynomial_ne_zero_of_linearIndependent_pencilRow,
   `CombinatorialRigidity.Molecular.exists_reposition_cross_incidences_avoiding,
   `CombinatorialRigidity.Molecular.exists_smul_eq_extensor_of_extensorThroughPoint_pair,
   `CombinatorialRigidity.Molecular.exists_smul_supportExtensor_eq_pencilChartFramework_of_reseed,
   `CombinatorialRigidity.Molecular.exists_subset_pair_of_ncard_le_two,
   `CombinatorialRigidity.Molecular.extensor_pair_smul,
   `CombinatorialRigidity.Molecular.finrank_span_pair_le,
   `CombinatorialRigidity.Molecular.finrank_span_rigidityRows_pencilChartFramework_eq_of_independent_pencilRow,
   `CombinatorialRigidity.Molecular.finrank_span_triple_le,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_cutEdges_eq_empty,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_pendant_of_IH,
   `CombinatorialRigidity.Molecular.hlb_induce_of_isNondegPencilRealization_induce_union_singleton,
   `CombinatorialRigidity.Molecular.le_finrank_toDualPerp_inf,
   `CombinatorialRigidity.Molecular.linearIndepOn_pencilChartNormal_congr,
   `CombinatorialRigidity.Molecular.nbrSlotPointPoly,
   `CombinatorialRigidity.Molecular.nbrSlotPointPoly_eval,
   `CombinatorialRigidity.Molecular.nbrSlotPointPoly_eval_funext,
   `CombinatorialRigidity.Molecular.ncard_closedNbhd_eq_three_of_demoted,
   `CombinatorialRigidity.Molecular.pencilAnnihRowPoly,
   `CombinatorialRigidity.Molecular.pencilAnnihRowPoly_eval,
   `CombinatorialRigidity.Molecular.pencilChartFramework_congr,
   `CombinatorialRigidity.Molecular.pencilChartNormalPoly,
   `CombinatorialRigidity.Molecular.pencilChartNormalPoly_eval,
   `CombinatorialRigidity.Molecular.pencilChartNormal_congr,
   `CombinatorialRigidity.Molecular.pencilDotPoly,
   `CombinatorialRigidity.Molecular.pencilDotPoly_eval,
   `CombinatorialRigidity.Molecular.pencilPair_loop_base_cut,
   `CombinatorialRigidity.Molecular.pencilPair_of_X0,
   `CombinatorialRigidity.Molecular.pencilPair_of_arms,
   `CombinatorialRigidity.Molecular.pencilPair_of_not_twoEdgeConnected,
   `CombinatorialRigidity.Molecular.pencilPointJoinPoly,
   `CombinatorialRigidity.Molecular.pencilPointJoinPoly_eval,
   `CombinatorialRigidity.Molecular.pencilRow,
   `CombinatorialRigidity.Molecular.pencilRow_eq_panelRow_pencilChartFramework,
   `CombinatorialRigidity.Molecular.pencilRow_mem_rigidityRows_of_mem_edgeSet,
   `CombinatorialRigidity.Molecular.pencil_realization_theorem_of_X0,
   `CombinatorialRigidity.Molecular.span_rigidityRows_pencilChartFramework_eq_of_reseed,
   `Graph.degree_eq_degree_induce_succ,
   `Graph.degree_induce_eq_of_ne]

set_option linter.style.longLine false in
/-- Slice 3: `R2`'s thirteen and the three of `lem:pencil-projective-transport`. -/
def n1Slice3 : List Name :=
  [`CombinatorialRigidity.Molecular.exists_linearIndependent_extensor_pair_through_point,
   `CombinatorialRigidity.Molecular.hasDistinctPencilRealization_of_generic,
   `CombinatorialRigidity.Molecular.hasDistinctPencilRealization_of_not_twoEdgeConnected,
   `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_ncard_le_two,
   `CombinatorialRigidity.Molecular.hasPencilRealization_of_distinct,
   `CombinatorialRigidity.Molecular.hasPencilRealization_of_isLoopAt,
   `CombinatorialRigidity.Molecular.hasPencilRealization_of_ncard_le_two,
   `CombinatorialRigidity.Molecular.hasPencilRealization_of_not_simple,
   `CombinatorialRigidity.Molecular.hasPencilRealization_of_not_twoEdgeConnected,
   `CombinatorialRigidity.Molecular.not_pencilNondegFeasible_of_isLoopAt,
   `CombinatorialRigidity.Molecular.not_simple_of_parallel,
   `CombinatorialRigidity.Molecular.pencilPair_of_isLoopAt,
   `CombinatorialRigidity.Molecular.pencilPair_of_ncard_le_two,
   `CombinatorialRigidity.Molecular.extensorInPanel_screwEquivOfLinearEquiv,
   `CombinatorialRigidity.Molecular.extensorThroughPoint_screwEquivOfLinearEquiv,
   `CombinatorialRigidity.Molecular.hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv]

/-- The declaration a constant belongs to: a private name read as its user name. -/
def n1Base (n : Name) : Name := (privateToUserName? n).getD n

/-- `u` is in `D` or one of its auxiliary declarations (a prefix of `u`'s base name is in `D`). -/
partial def n1Covered (D : NameSet) (u : Name) : Bool :=
  let rec go (x : Name) : Bool :=
    D.contains x || match x with
      | .str p _ => go p
      | .num p _ => go p
      | .anonymous => false
  D.contains u || go (n1Base u)

/-- An auxiliary declaration (a proof, a `simp` lemma, a match or an equation lemma). -/
def n1IsAux (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
      s.startsWith "eq_"
  | _ => true

elab "#n1_slices" : command => do
  let env ← getEnv
  let proj := env.constants.fold (init := #[]) fun acc n _ =>
    if (spikeModuleOf env n).isSome && spikeIsProj env n then acc.push n else acc
  let mut users : Std.HashMap Name (Array Name) := {}
  for n in proj do
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        if m != n then users := users.insert m ((users.getD m #[]).push n)
  let mut cum : NameSet := {}
  let mut k : Nat := 0
  for sl in [n1Slice1, n1Slice2, n1Slice3] do
    k := k + 1
    cum := sl.foldl (·.insert ·) cum
    let mut viol : Array MessageData := #[]
    for d in sl do
      for u in users.getD d #[] do
        if !n1Covered cum u then viol := viol.push m!"{d} <- {u}"
    let mut dead := cum
    let mut orph : Array Name := #[]
    let mut changed := true
    while changed do
      changed := false
      for d in dead.toList do
        let some ci := env.find? d | continue
        for m in ci.getUsedConstantsAsSet do
          if dead.contains m || !spikeIsProj env m || (spikeModuleOf env m).isNone then continue
          let us := (users.getD m #[]).filter fun u => !n1Covered dead u && !(m.isPrefixOf u)
          if us.isEmpty then
            dead := dead.insert m; changed := true
            if !n1IsAux m then orph := orph.push m
    logInfo m!"SLICE {k}: {sl.length} deleted, {cum.size} in all; surviving users of a deleted \
      constant: {viol.size}\n{MessageData.joinSep viol.toList "\n"}\nORPHANS ({orph.size}): \
      {orph.toList}"

#n1_slices
