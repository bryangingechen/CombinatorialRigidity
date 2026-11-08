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
Restructures R1, R1' and R2 below are the planning note's N1a, N1b and N1c.

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
