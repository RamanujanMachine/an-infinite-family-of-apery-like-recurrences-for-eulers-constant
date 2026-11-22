module

public import ThisWork.HigherRank.CenterNoncancellation
public import ThisWork.HigherRank.BranchGrowth
public import ThisWork.HigherRank.RecessiveSubspace

/-! Strong recessiveness against every nontrivial off-cut combination. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter
open scoped Topology

theorem recessive_hasLogNormGrowth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ) :
    HasLogNormGrowth r (commonScale r m A z) (-(r : ℝ) * saddleScale r A z)
      (branchIntegral r m A z 0) := by
  have hθ : (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  simpa only [Phase.rho, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Complex.one_re, mul_one] using offCut_hasLogNormGrowth hr hA hz m 0 hθ (by norm_num)

theorem offCut_stronglyRecessive {r d : ℕ} (hr : 3 ≤ r) (hd : d ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (m : ℕ) (J : Fin d → ℤ) (θ : Fin d → ℝ) (hθ : ∀ i, θ i ∈ Ioo (-Real.pi) Real.pi)
    (hj : ∀ i, (r : ℝ) * θ i = -2 * Real.pi * J i)
    (hinj : Function.Injective θ) (a : Fin d → ℂ) (ha : a ≠ 0)
    (hsupport : ∀ i, a i ≠ 0 → J i ≠ 0) :
    (∀ᶠ n : ℕ in atTop, (∑ i, a i • branchIntegral r m A z (J i) n) ≠ 0) ∧
      ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N *
        (‖branchIntegral r m A z 0 n‖ / ‖∑ i, a i • branchIntegral r m A z (J i) n‖)) atTop (𝓝 0) := by
  classical
  obtain ⟨j, haj⟩ := Function.ne_iff.mp ha
  have hj0 := hsupport j haj
  have hθ0 : θ j ≠ 0 := by
    intro he
    have h := hj j
    rw [he, mul_zero] at h
    have hzj : (J j : ℝ) = 0 := by nlinarith [Real.pi_pos]
    exact hj0 (Int.cast_eq_zero.mp hzj)
  have hrec := recessive_hasLogNormGrowth hr hA hz m
  have hdom := offCut_hasLogNormGrowth hr hA hz m (J j) (hθ j) (hj j)
  have hc : 0 < (r : ℝ) * saddleScale r A z :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (saddleScale_pos hA hz)
  have hrate : -(r : ℝ) * saddleScale r A z <
      -(r : ℝ) * saddleScale r A z * (Phase.rho (θ j)).re := by
    nlinarith [rho_re_lt_one (hθ j) hθ0]
  obtain ⟨K, hK, hb⟩ := offCut_noncancellation hr hd hA hz m J θ hθ hj hinj
  exact separation_of_coefficient_bound (by omega : 1 < r) hrec hdom hrate
    (norm_pos_iff.mpr haj) hK (3 * (r - 1)) (hb.mono (fun _ hn => hn a j))

end ThisWork.HigherRank
