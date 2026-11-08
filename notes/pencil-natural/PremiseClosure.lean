import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Statements

/-!
# Phase 43a premise check: an independent kernel-closure walk of C

Read-only scratch (not for landing). Written from scratch, not from the recon's spike.
Banked 2026-11-07 in Phase 43a (`notes/Phase43a.md`, the premise check's item), unchanged but
for this paragraph. Run from the repo root: `lake lean notes/pencil-natural/PremiseClosure.lean`.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular
namespace PremiseCheck

variable {K : Type*} [Field K] {α β : Type*}

/-- The composition under test: `HasGenericPencilRealization K 3 G` from C at `r = 0`. -/
theorem genericThree [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hS : G.Simple) (hne : V(G).Nonempty) (hfeas : PencilNondegFeasible K G) :
    HasGenericPencilRealization K 3 G :=
  (hasGradedGenericPencilRealization_two_iff 3 G).1
    (liftAttains_of_simple 0 hS hne hfeas).hasGradedGenericPencilRealization

/-- `X0Gen` from it, against the landed statement. -/
theorem x0GenC [Finite α] [Finite β] [Infinite K] : X0Gen K α β :=
  fun _ hS hV _ hfeas => genericThree hS (Set.nonempty_of_ncard_ne_zero (by omega)) hfeas

end PremiseCheck
end CombinatorialRigidity.Molecular

open Lean Meta Elab Command

def pcMod (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def pcProj (env : Environment) (n : Name) : Bool :=
  match pcMod env n with
  | some m => m.getRoot == `CombinatorialRigidity
  | none => true

/-- Closure over `getUsedConstantsAsSet` (type and value), through project constants only;
also the count of constants with no `ConstantInfo` or an axiom. -/
def pcClosure (env : Environment) (roots : Array Name) : NameSet × Nat × Nat := Id.run do
  let mut seen : NameSet := {}
  let mut st := roots
  let mut missing := 0
  let mut axioms := 0
  while !st.isEmpty do
    let n := st.back!
    st := st.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => missing := missing + 1
    | some ci =>
      if ci.isAxiom then axioms := axioms + 1
      for m in ci.getUsedConstantsAsSet do
        if !seen.contains m && pcProj env m then st := st.push m
  return (seen, missing, axioms)

def pcPencil : Name := `CombinatorialRigidity.Molecular.Molecule.Pencil
def pcGrade : Name := `CombinatorialRigidity.Molecular.Molecule.Pencil.Grade

/-- The d = 3 statement constants: a type naming one of these is a d = 3 generic or pair
statement (or a bridge to one). -/
def pcD3Heads : List Name :=
  [`CombinatorialRigidity.Molecular.HasGenericPencilRealization,
   `CombinatorialRigidity.Molecular.PencilPair,
   `CombinatorialRigidity.Molecular.X0Gen]

def pcReport (label : String) (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for r in roots do
    unless env.contains r do throwError "unknown {r}"
  let (cl, miss, ax) := pcClosure env roots
  logInfo m!"== {label}: {cl.size} project constants; {miss} not found; {ax} axioms"
  -- per-module counts for non-Grade Pencil modules
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for n in cl.toList do
    if let some m := pcMod env n then
      if pcPencil.isPrefixOf m && !pcGrade.isPrefixOf m then
        byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let mods := byMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (m, ns) in mods do
    let pub := ns.filter (fun n => !n.isInternalDetail)
    logInfo m!"  [{m}] {ns.size} constants ({pub.size} public): {pub.toList}"
  -- constants whose type names a d = 3 generic/pair head
  let mut hits : Array (Name × Option Name) := #[]
  for n in cl.toList do
    if let some ci := env.find? n then
      let used := ci.type.getUsedConstants
      if pcD3Heads.any (used.contains ·) then hits := hits.push (n, pcMod env n)
  logInfo m!"  TYPE names HasGenericPencilRealization / PencilPair / X0Gen: {hits.size}: {hits.toList}"

elab "#pc_report " lbl:str roots:ident* : command => do
  let ns ← roots.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  pcReport lbl.getString ns

-- positive control: the landed x0Gen must reach the d = 3 generic step
#pc_report "CONTROL x0Gen" CombinatorialRigidity.Molecular.x0Gen

-- the three roots the brief names, separately and together
#pc_report "liftAttains_of_simple" CombinatorialRigidity.Molecular.liftAttains_of_simple
#pc_report "LiftAttains.hasGradedGenericPencilRealization"
  CombinatorialRigidity.Molecular.LiftAttains.hasGradedGenericPencilRealization
#pc_report "hasGradedGenericPencilRealization_two_iff"
  CombinatorialRigidity.Molecular.hasGradedGenericPencilRealization_two_iff
#pc_report "the composition genericThree"
  CombinatorialRigidity.Molecular.PremiseCheck.genericThree
#pc_report "x0GenC" CombinatorialRigidity.Molecular.PremiseCheck.x0GenC
-- C's other headline pins
#pc_report "C headlines: hasGradedGenericPencilRealization_of_simple, graded_pencil_conditioned_pair"
  CombinatorialRigidity.Molecular.hasGradedGenericPencilRealization_of_simple
  Graph.graded_pencil_conditioned_pair

/-- Membership of specific watched constants in the closure of the composition. -/
def pcWatch (roots : Array Name) (watch : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let (cl, _, _) := pcClosure env roots
  for w in watch do
    unless env.contains w do logInfo m!"  (not in env) {w}"; continue
    logInfo m!"  {if cl.contains w then "IN " else "out"} {w}"

elab "#pc_watch " roots:ident* " ; " ws:ident* : command => do
  let rs ← roots.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  let ws ← ws.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  pcWatch rs ws.toList

#pc_watch CombinatorialRigidity.Molecular.PremiseCheck.genericThree ;
  CombinatorialRigidity.Molecular.x0Gen
  CombinatorialRigidity.Molecular.pencilPair_of_nonempty
  CombinatorialRigidity.Molecular.pencilPair_of_IH
  CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_IH
  CombinatorialRigidity.Molecular.pencil_realization_theorem
  CombinatorialRigidity.Molecular.pencilPair_of_arms
  CombinatorialRigidity.Molecular.exists_isNondegPencilRealization_steer
  CombinatorialRigidity.Molecular.exists_isNondegPencilRealization_restrict_of_demoted
  CombinatorialRigidity.Molecular.exists_pencilSeed_of_nondeg_of_selectors
  Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero
  Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization
  Graph.IsOpenEar.hasGenericPencilRealization_of_one
  CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two
  CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization
  Graph.IsX0Graph.exists_oneEar_or_pendantTriangle
  Graph.IsX0Graph.exists_minimalRigid_ear_or_pendantTriangle
  Graph.exists_eq_triple_of_minimal
  Graph.exists_closedEar_two_of_triangle
  Graph.closedEar_two_of_triangle
  CombinatorialRigidity.Molecular.PencilNondegFeasible.hub_conditions
  CombinatorialRigidity.Molecular.exists_planes_separate
  CombinatorialRigidity.Molecular.isNondeg_pencilConfig_of_planeDiff
  Graph.addTwoEar
  Graph.IsX0Graph.x0Attains
  Graph.pencil_reduction

#print axioms CombinatorialRigidity.Molecular.PremiseCheck.genericThree
#print axioms CombinatorialRigidity.Molecular.PremiseCheck.x0GenC
