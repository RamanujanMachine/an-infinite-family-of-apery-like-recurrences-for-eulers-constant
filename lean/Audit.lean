import Neuschel
import ThisWork
import Lean.Util.CollectAxioms

#print axioms Neuschel.neuschel_theorem_3_1_published
#print axioms ThisWork.equalSlope_mellinBarnes_asymptotics
#print axioms ThisWork.TStar.mellinBarnes_asymptotics
#print axioms ThisWork.OffCutLocalData.normalized_originalMoment_tendsto
#print axioms ThisWork.offCut_noncancellation
#print axioms ThisWork.evenBoundary_zeroCenter_hasLogNormGrowth
#print axioms ThisWork.branch_linearIndependent
#print axioms ThisWork.branch_stronglyRecessive
#print axioms ThisWork.RankThree.equal_normEstimate
#print axioms ThisWork.RankThree.equal_linearIndependent
#print axioms ThisWork.RankThree.equal_stronglyRecessive
#print axioms ThisWork.lemma8
#print axioms ThisWork.lemma8_one
#print axioms ThisWork.lemma8_with_strongRecessiveness

-- Select by defining module, covering generated declarations and private
-- helpers as well as every named theorem in the consolidated development.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let required := #[``Neuschel.neuschel_theorem_3_1_published,
    ``ThisWork.equalSlope_mellinBarnes_asymptotics,
    ``ThisWork.TStar.mellinBarnes_asymptotics,
    ``ThisWork.branch_normEstimate, ``ThisWork.branch_linearIndependent,
    ``ThisWork.branch_stronglyRecessive,
    ``ThisWork.OffCutLocalData.normalized_originalMoment_tendsto,
    ``ThisWork.offCut_noncancellation,
    ``ThisWork.evenBoundary_zeroCenter_hasLogNormGrowth,
    ``ThisWork.RankThree.equal_normEstimate,
    ``ThisWork.RankThree.equal_linearIndependent,
    ``ThisWork.RankThree.equal_stronglyRecessive,
    ``ThisWork.lemma8, ``ThisWork.lemma8_one,
    ``ThisWork.lemma8_with_strongRecessiveness]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if (`Neuschel).isPrefixOf moduleName || (`ThisWork).isPrefixOf moduleName then
      names := names.push name
  for name in required do
    unless names.contains name do
      throwError "Axiom audit did not find required theorem {name}"
  for name in names.qsort Name.lt do
    let dependencies ← Lean.collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
  logInfo m!"Axiom audit passed for all {names.size} project declarations."
