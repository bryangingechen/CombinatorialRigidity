import CombinatorialRigidity
open Lean Elab Command

def cands : List Name := [
  `CombinatorialRigidity.Molecular.planarProj, `CombinatorialRigidity.Molecular.planarProj_apply,
  `CombinatorialRigidity.Molecular.planarProj_pencilConfigPoint,
  `CombinatorialRigidity.Molecular.flatPiForm, `CombinatorialRigidity.Molecular.flatPi,
  `CombinatorialRigidity.Molecular.flatPi_mk_extensor,
  `CombinatorialRigidity.Molecular.flatSigmaForm, `CombinatorialRigidity.Molecular.flatSigma,
  `CombinatorialRigidity.Molecular.flatSigma_mk_extensor, `CombinatorialRigidity.Molecular.flatStdBiv,
  `CombinatorialRigidity.Molecular.flatRebuild, `CombinatorialRigidity.Molecular.flatSigma_flatRebuild,
  `CombinatorialRigidity.Molecular.flatPi_flatRebuild, `CombinatorialRigidity.Molecular.flatScrewEquiv,
  `CombinatorialRigidity.Molecular.flatScrewEquiv_apply,
  `CombinatorialRigidity.Molecular.mem_span_extensor_flat_iff,
  `Graph.linkConstants, `Graph.finrank_linkConstants,
  `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat,
  `Graph.finrank_span_rigidityRows_ofNormals_flat, `Graph.finrank_span_rigidityRows_ofNormals_flat_le,
  `Graph.finrank_span_rigidityRows_ofNormals_flat_eq_iff,
  `Graph.finrank_liftingSpace_eq_three_add_deficiency_three_iff,
  `Graph.x0Attains_of_finrank_liftingSpace_le, `Graph.x0Attains_of_finrank_liftingSpace_eq_three,
  `Graph.x0Attains_of_deficiency_two_eq_three]

partial def depClosure (env : Environment) (n : Name) (seen : NameSet) : NameSet := Id.run do
  if seen.contains n then return seen
  let mut seen := seen.insert n
  if let some ci := env.find? n then
    let used : NameSet := ci.type.getUsedConstantsAsSet.union ((ci.value? (allowOpaque := true)).map (·.getUsedConstantsAsSet) |>.getD {})
    for c in used do
      if (`CombinatorialRigidity).isPrefixOf ((env.getModuleFor? c).getD .anonymous) then
        seen := depClosure env c seen
  return seen

run_cmd do
  let env ← getEnv
  for root in [`Graph.finrank_span_rigidityRows_ofNormals_flat_grade,
      `Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights,
      `Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint,
      `Graph.x0AttainsGrade_of_finrank_liftingSpace_le,
      `Graph.x0AttainsGrade_of_deficiency_two_eq,
      `Graph.exists_mvPolynomial_gluedEnds] do
    let cl : NameSet := depClosure env root {}
    logInfo m!"closure of {root} ({cl.size} project consts) meets candidates: {cands.filter (fun c => cl.contains c)}"
  -- direct users
  for c in cands do
    unless env.contains c do logInfo m!"MISSING {c}"
  let mut users : Std.HashMap Name (Array (Name × Name)) := {}
  for (n, ci) in env.constants.toList do
    let some mod := env.getModuleFor? n | continue
    unless (`CombinatorialRigidity).isPrefixOf mod do continue
    let used : NameSet := ci.type.getUsedConstantsAsSet.union ((ci.value? (allowOpaque := true)).map (·.getUsedConstantsAsSet) |>.getD {})
    for c in cands do
      if used.contains c && !(c.isPrefixOf n) then
        users := users.insert c ((users.getD c #[]).push (n, mod))
  for c in cands do
    let us := (users.getD c #[]).map fun (n, mod) => m!"{n} [{mod.components.getLast!}]"
    logInfo m!"{c} <- {us}"
