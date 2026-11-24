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
#print axioms ThisWork.HigherRank.branchIntegral_reindex
#print axioms ThisWork.HigherRank.branchIntegral_rank_three
#print axioms ThisWork.HigherRank.positiveTerm_summable
#print axioms ThisWork.HigherRank.PositiveSeries.moment_summable
#print axioms ThisWork.HigherRank.PositiveSeries.ratio_tendsto_at_scale
#print axioms ThisWork.HigherRank.PositiveSeries.tail_sum_le_geometric
#print axioms ThisWork.HigherRank.Phase.gaussian_coefficient_re_neg
#print axioms ThisWork.HigherRank.root_mem_slitPlane_iff
#print axioms ThisWork.HigherRank.logDeriv_kernel
#print axioms ThisWork.HigherRank.even_boundary_kernel_fourier
#print axioms ThisWork.HigherRank.uniform_exactSaddleEquation_region
#print axioms ThisWork.HigherRank.phase_parabolic_strict_max
#print axioms ThisWork.HigherRank.differentiableAt_reflectedKernel
#print axioms ThisWork.HigherRank.exists_exact_saddle_at_angle
#print axioms ThisWork.HigherRank.eventually_exists_exact_local_phase
#print axioms ThisWork.HigherRank.eventually_upper_parabolic_kernel_integral_eq_segment
#print axioms ThisWork.HigherRank.uniform_kernelPhaseError_parabola
#print axioms ThisWork.HigherRank.norm_boundaryKernel_lower_error_le
#print axioms ThisWork.HigherRank.logDeriv_reflectedKernel
#print axioms ThisWork.HigherRank.uniform_kernel_parabolic_gap
#print axioms ThisWork.HigherRank.exists_parabolic_coordinates
#print axioms ThisWork.HigherRank.exists_compactSaddleFamily
#print axioms ThisWork.HigherRank.CompactSaddleFamily.eventually_kernel_eq_phase
#print axioms ThisWork.HigherRank.CompactSaddleFamily.parabolic_quadratic_coefficient
#print axioms Neuschel.LocalContourModel.quadratic_curve_leading_estimate
#print axioms ThisWork.HigherRank.exists_offCutLocalData
#print axioms ThisWork.HigherRank.OffCutLocalData.normalizedLocalMoment_tendsto
#print axioms ThisWork.HigherRank.CompactSaddleFamily.LocalParabolicData.eventually_localKernelMoment_eq_phase
#print axioms ThisWork.HigherRank.weighted_hankel_absolutely_convergent
#print axioms ThisWork.HigherRank.branchIntegral_eq_deformed
#print axioms ThisWork.HigherRank.uniform_integrated_moment_tail_from_endpoint
#print axioms ThisWork.HigherRank.uniform_log_norm_kernel_parabola
#print axioms ThisWork.HigherRank.OffCutLocalData.saddleKernel_growth
#print axioms ThisWork.HigherRank.uniform_reflectedEquation_region
#print axioms ThisWork.HigherRank.reflectedRealPhase_strict_max
#print axioms ThisWork.HigherRank.reflectedKernel_real_pos
#print axioms ThisWork.HigherRank.fixed_boundary_bank_errors_le
#print axioms ThisWork.HigherRank.uniform_upperGamma_fixed_bound
#print axioms ThisWork.HigherRank.linearIndependent_option_of_dominance
#print axioms ThisWork.HigherRank.reflected_lower_bank_eq_real
#print axioms ThisWork.HigherRank.reflectedRealIntegral_lower
#print axioms ThisWork.HigherRank.reflectedRealIntegral_upper
#print axioms ThisWork.HigherRank.boundary_hankel_comparable_real
#print axioms ThisWork.HigherRank.eventually_boundary_hankel_ne_zero
#print axioms ThisWork.HigherRank.boundary_integral_growth
#print axioms ThisWork.HigherRank.OffCutLocalData.normalized_originalMoment_tendsto
#print axioms ThisWork.HigherRank.offCut_normEstimate
#print axioms ThisWork.HigherRank.branchIntegral_change_center
#print axioms ThisWork.HigherRank.boundary_vector_zeroCenter_growth
#print axioms ThisWork.HigherRank.evenBoundary_zeroCenter_hasLogNormGrowth
#print axioms ThisWork.HigherRank.offCut_noncancellation
#print axioms ThisWork.HigherRank.branch_normEstimate
#print axioms ThisWork.HigherRank.branch_linearIndependent
#print axioms ThisWork.HigherRank.branch_stronglyRecessive
#print axioms ThisWork.HigherRank.equalSlope_mellinBarnes_asymptotics
#print axioms ThisWork.HigherRank.TStar.mellinBarnes_asymptotics
#print axioms ThisWork.HigherRank.shifted_hankel_eq_parabolic_with_tails
#print axioms ThisWork.HigherRank.uniform_integrated_cone_moment_tail
#print axioms ThisWork.HigherRank.eventually_branchIntegral_eq_parabolic_with_tails
#print axioms ThisWork.HigherRank.uniform_parabolic_power_tail_bound
#print axioms ThisWork.HigherRank.uniform_parabolic_power_remainder_bound
#print axioms ThisWork.HigherRank.CompactSaddleFamily.LocalParabolicData.eventually_localKernelMoment_eq_parabolic_window

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
      names.contains ``ThisWork.Trajectory.equal_stronglyRecessive &&
      names.contains ``ThisWork.HigherRank.branchIntegral_reindex &&
      names.contains ``ThisWork.HigherRank.branchIntegral_rank_three &&
      names.contains ``ThisWork.HigherRank.positiveTerm_summable &&
      names.contains ``ThisWork.HigherRank.PositiveSeries.ratio_tendsto_at_scale &&
      names.contains ``ThisWork.HigherRank.logDeriv_kernel &&
      names.contains ``ThisWork.Analytic.eventually_noncancellation_of_normalized_moments &&
      names.contains ``ThisWork.HigherRank.even_boundary_kernel_fourier &&
      names.contains ``ThisWork.HigherRank.uniform_exactSaddleEquation_region &&
      names.contains ``ThisWork.HigherRank.phase_parabolic_strict_max &&
      names.contains ``ThisWork.HigherRank.eventually_exists_exact_local_phase &&
      names.contains ``ThisWork.HigherRank.eventually_upper_parabolic_kernel_integral_eq_segment &&
      names.contains ``ThisWork.HigherRank.uniform_kernelPhaseError_parabola &&
      names.contains ``ThisWork.HigherRank.norm_boundaryKernel_lower_error_le &&
      names.contains ``ThisWork.HigherRank.uniform_kernel_parabolic_gap &&
      names.contains ``ThisWork.HigherRank.exists_parabolic_coordinates &&
      names.contains ``ThisWork.HigherRank.exists_compactSaddleFamily &&
      names.contains ``ThisWork.HigherRank.CompactSaddleFamily.parabolic_quadratic_coefficient &&
      names.contains ``ThisWork.HigherRank.exists_offCutLocalData &&
      names.contains ``ThisWork.HigherRank.branchIntegral_eq_deformed &&
      names.contains ``ThisWork.HigherRank.uniform_integrated_moment_tail_from_endpoint &&
      names.contains ``ThisWork.HigherRank.uniform_log_norm_kernel_parabola &&
      names.contains ``ThisWork.HigherRank.OffCutLocalData.saddleKernel_growth &&
      names.contains ``ThisWork.HigherRank.fixed_boundary_bank_errors_le &&
      names.contains ``ThisWork.HigherRank.linearIndependent_option_of_dominance &&
      names.contains ``ThisWork.HigherRank.reflected_lower_bank_eq_real &&
      names.contains ``ThisWork.HigherRank.reflectedRealIntegral_lower &&
      names.contains ``ThisWork.HigherRank.reflectedRealIntegral_upper &&
      names.contains ``ThisWork.HigherRank.boundary_hankel_comparable_real &&
      names.contains ``ThisWork.HigherRank.eventually_boundary_hankel_ne_zero &&
      names.contains ``ThisWork.HigherRank.boundary_integral_growth &&
      names.contains ``ThisWork.HigherRank.OffCutLocalData.normalized_originalMoment_tendsto &&
      names.contains ``ThisWork.HigherRank.offCut_normEstimate &&
      names.contains ``ThisWork.HigherRank.branchIntegral_change_center &&
      names.contains ``ThisWork.HigherRank.boundary_vector_zeroCenter_growth &&
      names.contains ``ThisWork.HigherRank.evenBoundary_zeroCenter_hasLogNormGrowth &&
      names.contains ``ThisWork.HigherRank.offCut_noncancellation &&
      names.contains ``ThisWork.HigherRank.branch_normEstimate &&
      names.contains ``ThisWork.HigherRank.branch_linearIndependent &&
      names.contains ``ThisWork.HigherRank.branch_stronglyRecessive &&
      names.contains ``ThisWork.HigherRank.equalSlope_mellinBarnes_asymptotics &&
      names.contains ``ThisWork.HigherRank.TStar.mellinBarnes_asymptotics &&
      names.contains ``ThisWork.HigherRank.eventually_branchIntegral_eq_parabolic_with_tails &&
      names.contains ``ThisWork.HigherRank.uniform_integrated_cone_moment_tail &&
      names.contains ``ThisWork.HigherRank.uniform_parabolic_power_tail_bound &&
      names.contains ``ThisWork.HigherRank.uniform_parabolic_power_remainder_bound &&
      names.contains ``ThisWork.HigherRank.CompactSaddleFamily.LocalParabolicData.eventually_localKernelMoment_eq_parabolic_window do
    throwError "Axiom audit did not find the general-argument and trajectory theorems"
  for name in names.qsort Name.lt do
    let dependencies ← Lean.collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {name}"
  logInfo m!"Axiom audit passed for all {names.size} project declarations."
