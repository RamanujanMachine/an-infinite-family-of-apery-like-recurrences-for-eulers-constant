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
#print axioms ThisWork.Trajectory.branchIntegral_linearIndependent
#print axioms ThisWork.Trajectory.SqrtSaddleFamily.eventually_kernel_eq_phase
#print axioms ThisWork.Trajectory.double_normEstimate
#print axioms ThisWork.Trajectory.double_lemma8
#print axioms ThisWork.Trajectory.canonical_normEstimate
#print axioms ThisWork.Trajectory.ReflectedSaddleData.normalizedWindowMoment_tendsto
#print axioms ThisWork.Trajectory.uniform_growing_reflection_error
#print axioms ThisWork.Trajectory.equal_lemma8
#print axioms ThisWork.Trajectory.eventually_exists_exact_sqrt_phase
#print axioms ThisWork.Trajectory.norm_kernel_one_sub_reflected_le
#print axioms ThisWork.Trajectory.elementaryIntegral_eq_reflected
#print axioms ThisWork.Trajectory.uniform_re_exactSqrtEquation_left_lower
#print axioms ThisWork.Trajectory.uniform_integrated_leftMoment_tail
#print axioms ThisWork.Trajectory.uniform_full_canonical_window_remainder

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
      names.contains ``ThisWork.Trajectory.branchIntegral_linearIndependent &&
      names.contains ``ThisWork.Trajectory.SqrtSaddleFamily.eventually_kernel_eq_phase &&
      names.contains ``ThisWork.Trajectory.double_normEstimate &&
      names.contains ``ThisWork.Trajectory.double_lemma8 &&
      names.contains ``ThisWork.Trajectory.canonical_normEstimate &&
      names.contains ``ThisWork.Trajectory.ReflectedSaddleData.normalizedWindowMoment_tendsto &&
      names.contains ``ThisWork.Trajectory.uniform_growing_reflection_error &&
      names.contains ``ThisWork.Trajectory.equal_lemma8 &&
      names.contains ``ThisWork.Trajectory.eventually_exists_exact_sqrt_phase &&
      names.contains ``ThisWork.Trajectory.norm_kernel_one_sub_reflected_le &&
      names.contains ``ThisWork.Trajectory.elementaryIntegral_eq_reflected &&
      names.contains ``ThisWork.Trajectory.uniform_re_exactSqrtEquation_left_lower &&
      names.contains ``ThisWork.Trajectory.uniform_integrated_leftMoment_tail &&
      names.contains ``ThisWork.Trajectory.uniform_full_canonical_window_remainder do
    throwError "Axiom audit did not find the general-argument and trajectory theorems"
  for name in names.qsort Name.lt do
    let dependencies ← Lean.collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
  logInfo m!"Axiom audit passed for all {names.size} project declarations."
