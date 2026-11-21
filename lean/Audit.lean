import Neuschel
import ThisWork
import Lean.Util.CollectAxioms

#print axioms Neuschel.exists_uniform_isolated_zero
#print axioms Neuschel.neuschel_lemma_2_2
#print axioms Neuschel.uniform_exp_tail_bound
#print axioms Neuschel.exists_phase_straightening_of_contour
#print axioms Neuschel.exists_local_phase_from_expansion
#print axioms Neuschel.LocalInverseFamily.laplace_contour_substitution
#print axioms Neuschel.uniform_taylor_remainder
#print axioms Neuschel.laplaceMoment_eq_gamma
#print axioms Neuschel.neuschel_theorem_3_1_published
#print axioms ThisWork.lemma8
#print axioms ThisWork.Analytic.lemma8
#print axioms ThisWork.lemma8_normEstimate
#print axioms ThisWork.lemma8_one
#print axioms ThisWork.Trajectory.equal_normEstimate
#print axioms ThisWork.Trajectory.equal_linearIndependent
#print axioms ThisWork.Trajectory.equal_lemma8
#print axioms ThisWork.Analytic.eventually_noncancellation_of_normalized_moments
#print axioms ThisWork.Analytic.eventually_noncancellation_of_rank_three_moments
#print axioms ThisWork.branchIntegral_noncancellation
#print axioms ThisWork.branchIntegral_separation_bound
#print axioms ThisWork.branchIntegral_stronglyRecessive
#print axioms ThisWork.lemma8_with_strongRecessiveness
#print axioms ThisWork.Trajectory.equal_stronglyRecessive

-- Select by defining module so generated declarations and private helpers are
-- covered along with the named theorems. New project modules need no audit-list edit.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => env.mainModule
    if (`Neuschel).isPrefixOf moduleName || (`ThisWork).isPrefixOf moduleName then
      names := names.push name
  unless names.contains ``Neuschel.neuschel_theorem_3_1_published &&
      names.contains ``ThisWork.lemma8 &&
      names.contains ``ThisWork.lemma8_normEstimate &&
      names.contains ``ThisWork.lemma8_one &&
      names.contains ``ThisWork.Trajectory.equal_normEstimate &&
      names.contains ``ThisWork.Trajectory.equal_linearIndependent &&
      names.contains ``ThisWork.Trajectory.equal_lemma8 &&
      names.contains ``ThisWork.branchIntegral_noncancellation &&
      names.contains ``ThisWork.branchIntegral_stronglyRecessive &&
      names.contains ``ThisWork.lemma8_with_strongRecessiveness &&
      names.contains ``ThisWork.Trajectory.equal_stronglyRecessive do
    throwError "Axiom audit did not find the general-argument and trajectory theorems"
  for name in names.qsort Name.lt do
    let dependencies ← Lean.collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
  logInfo m!"Axiom audit passed for all {names.size} project declarations."
