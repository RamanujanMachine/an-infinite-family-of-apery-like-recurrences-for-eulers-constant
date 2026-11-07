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
      names.contains ``ThisWork.lemma8_one do
    throwError "Axiom audit did not find the general-argument final theorems and their z=1 specialization"
  for name in names.qsort Name.lt do
    let dependencies ← Lean.collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
  logInfo m!"Axiom audit passed for all {names.size} project declarations."
