module

public import ThisWork.HigherRank.OffCutCenterGrowth
public import ThisWork.Noncancellation

/-! Independence of any collection of off-cut branches, including collections
with fewer branches than vector components. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter
open scoped Topology

theorem rho_injective_on_principal : Set.InjOn Phase.rho (Ioo (-Real.pi) Real.pi) := by
  intro a ha auxB hb he
  have h := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using ha.1) (by simpa using ha.2.le)
    (by simpa using hb.1) (by simpa using hb.2.le) he
  have hi := congrArg Complex.im h
  simpa using hi

noncomputable def firstPowerMomentTransform {r d : ℕ} (hd : d ≤ r) (n : ℕ) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi (fun k => (LinearMap.proj (k.castLE hd)).comp (powerMomentTransform r n))

theorem offCut_zeroCenter_linearIndependent {r d : ℕ} (hr : 3 ≤ r) (hd : d ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (J : Fin d → ℤ) (θ : Fin d → ℝ) (hθ : ∀ i, θ i ∈ Ioo (-Real.pi) Real.pi)
    (hj : ∀ i, (r : ℝ) * θ i = -2 * Real.pi * J i)
    (hinj : Function.Injective θ) :
    LinearIndependent ℂ (fun i => branchIntegral r 0 A z (J i)) := by
  classical
  let D : ∀ i, OffCutLocalData r A z (J i) (θ i) := fun i =>
    Classical.choice (exists_offCutLocalData hr hA hz (J i) (hθ i) (hj i))
  have hζ : Function.Injective (fun i => (saddleScale r A z : ℂ) * Phase.rho (θ i)) := by
    intro i k hik
    apply hinj
    apply rho_injective_on_principal (hθ i) (hθ k)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (saddleScale_pos hA hz).ne') hik
  apply Analytic.linearIndependent_sequences_of_moment_limits hζ
    (firstPowerMomentTransform hd) (fun n i => (D i).normalizingScalar n)
  · exact Filter.eventually_all.mpr (fun i =>
      (D i).eventually_normalizingScalar_ne_zero (by omega) hA)
  · intro i k
    exact (D i).normalized_originalMoment_tendsto hr hA hz (k.castLE hd)

theorem offCut_linearIndependent {r d : ℕ} (hr : 3 ≤ r) (hd : d ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (J : Fin d → ℤ) (θ : Fin d → ℝ)
    (hθ : ∀ i, θ i ∈ Ioo (-Real.pi) Real.pi)
    (hj : ∀ i, (r : ℝ) * θ i = -2 * Real.pi * J i)
    (hinj : Function.Injective θ) :
    LinearIndependent ℂ (fun i => branchIntegral r b A z (J i)) := by
  let F : (ℕ → Fin r → ℂ) →ₗ[ℂ] (ℕ → Fin r → ℂ) :=
    LinearMap.pi (fun n =>
      Complex.exp ((Real.log z : ℂ) * (-(b : ℂ) * n)) •
        ((translateMomentsLinear r (-(b : ℂ) * n)).comp (LinearMap.proj n)))
  have hF (i : Fin d) : F (branchIntegral r b A z (J i)) = branchIntegral r 0 A z (J i) := by
    funext n
    have h := branchIntegral_change_center (by omega : 0 < r) hA 0 b z (J i) n
    change Complex.exp ((Real.log z : ℂ) * (-(b : ℂ) * n)) •
      translateMoments r (-(b : ℂ) * n) (branchIntegral r b A z (J i) n) = _
    simpa only [Nat.cast_zero, zero_sub] using h.symm
  apply LinearIndependent.of_comp F
  simpa only [Function.comp_def, hF] using
    offCut_zeroCenter_linearIndependent hr hd hA hz J θ hθ hj hinj

end ThisWork.HigherRank
