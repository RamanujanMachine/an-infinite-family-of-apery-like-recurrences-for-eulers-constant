module

public import ThisWork.HigherRank.KernelNorm
public import ThisWork.GammaTailBounds
public import ThisWork.HigherRank.ReflectedSaddleEquation

/-! Upper Gamma products on fixed bounded sets grow only polynomially
relative to their common Gamma scale. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_upperGamma_fixed_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℂ, ‖x‖ ≤ M →
      ‖∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)‖ ≤
        gammaScale r A n * Real.exp (C * (1 + Real.log (n : ℝ))) := by
  have hi (i : Fin (r - 1)) : ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      max 4 (M + 1) ≤ A i * n ∧ ∀ x : ℂ, ‖x‖ ≤ M →
        |Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖ -
          Real.log ‖Complex.Gamma ((A i * n + 1 : ℝ) : ℂ)‖ + x.re * Real.log (A i * n)| ≤ C := by
    obtain ⟨C, hC, hb⟩ := Analytic.uniform_Gamma_bounded_shift (by linarith : 0 < M + 1)
    have hAn : Tendsto (fun n : ℕ => A i * n) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop (hA i)
    refine ⟨C, hC, ?_⟩
    filter_upwards [hAn.eventually hb, hAn.eventually (eventually_ge_atTop (max 4 (M + 1)))]
      with n hn hnA
    refine ⟨hnA, fun x hx => ?_⟩
    have h := hn.2 x (hx.trans (by linarith : M ≤ M + 1))
    rw [Complex.ofReal_mul, Complex.ofReal_natCast] at h
    exact h.trans (div_le_self hC (by linarith [(le_max_left 4 (M + 1)).trans hnA] : 1 ≤ A i * n))
  choose C hC hb using hi
  let D := M * (∑ i, |Real.log (A i)|) + ∑ i, C i
  let E := M * ((r : ℝ) - 1)
  have hD : 0 ≤ D := add_nonneg (mul_nonneg hM (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    (Finset.sum_nonneg (fun i _ => hC i))
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hE : 0 ≤ E := mul_nonneg hM (by linarith)
  refine ⟨D + E, add_nonneg hD hE, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1 x hx
  have hre : -M ≤ x.re := by linarith [neg_le_abs x.re, Complex.abs_re_le_norm x]
  have hu (i : Fin (r - 1)) : Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖ ≤
      Real.log ‖Complex.Gamma ((A i * n + 1 : ℝ) : ℂ)‖ + C i + M * Real.log (A i * n) := by
    have h := (abs_le.mp ((hn i).2 x hx)).2
    have ha : 1 ≤ A i * n := by linarith [(le_max_left 4 (M + 1)).trans (hn i).1]
    nlinarith [mul_le_mul_of_nonneg_right hre (Real.log_nonneg ha)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [← log_gammaScale hA n, sum_log_upper_gaps hr hA (by omega)] at hs
  have hlogs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => le_abs_self (Real.log (A i)))
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hbound : (∑ i, Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖) ≤
      Real.log (gammaScale r A n) + (D + E) * (1 + Real.log (n : ℝ)) := by
    dsimp only [D, E] at *
    nlinarith [mul_le_mul_of_nonneg_left hlogs hM, mul_nonneg hD hlogn]
  have hne (i : Fin (r - 1)) : Complex.Gamma ((A i : ℂ) * n - x + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have ha := (le_max_right 4 (M + 1)).trans (hn i).1
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.natCast_re,
      Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re]
    linarith [Complex.re_le_norm x]
  calc
    _ ≤ Real.exp (Real.log ‖∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)‖) := Real.le_exp_log _
    _ = Real.exp (∑ i, Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖) := by
      rw [norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hne i))]
    _ ≤ Real.exp (Real.log (gammaScale r A n) + (D + E) * (1 + Real.log (n : ℝ))) := Real.exp_le_exp.mpr hbound
    _ = _ := by rw [Real.exp_add, Real.exp_log (gammaScale_pos hA n)]

theorem uniform_upperGamma_weighted_fixed_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z M B : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℂ, ‖x‖ ≤ M → ∀ w : ℂ, ‖w‖ ≤ B →
      ‖w * (∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)) *
        Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - x))‖ ≤
        (B * Real.exp (|Real.log z| * M)) * commonScale r b A z n *
          Real.exp (C * (1 + Real.log (n : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := uniform_upperGamma_fixed_bound hr hA hM
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with n hn x hx w hw
  have hxp : -Real.log z * x.re ≤ |Real.log z| * M := by
    have hre : |x.re| ≤ M := (Complex.abs_re_le_norm x).trans hx
    have h := mul_le_mul_of_nonneg_left hre (abs_nonneg (Real.log z))
    have hneg := neg_le_abs (Real.log z * x.re)
    rw [abs_mul] at hneg
    nlinarith
  have he : ‖Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - x))‖ ≤
      z ^ (b * n) * Real.exp (|Real.log z| * M) := by
    rw [Complex.norm_exp]
    have hp : Real.exp (Real.log z * ((b : ℝ) * n)) = z ^ (b * n) := by
      rw [mul_comm, ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hz]
    rw [← hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero]
    nlinarith
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (B * (gammaScale r A n * Real.exp (C * (1 + Real.log (n : ℝ))))) *
        (z ^ (b * n) * Real.exp (|Real.log z| * M)) :=
      mul_le_mul (mul_le_mul hw (hn x hx) (norm_nonneg _) hB) he (norm_nonneg _)
        (mul_nonneg hB (mul_nonneg (gammaScale_pos hA n).le (Real.exp_pos _).le))
    _ = _ := by unfold commonScale; ring

theorem uniform_reflectedKernel_fixed_compact_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (b : ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hleft : ∀ x ∈ K, x.re < 1) :
    ∃ B ≥ 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ K,
      ‖reflectedKernel r b A z n x‖ ≤ B * commonScale r b A z n *
        Real.exp (C * (1 + Real.log (n : ℝ))) := by
  have hc : ContinuousOn (fun x : ℂ => (Complex.Gamma (1 - x))⁻¹ ^ r) K := by
    intro x hx
    have hpos : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hleft x hx]
    exact ((((Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt.comp x
      (show DifferentiableAt ℂ (fun t : ℂ => 1 - t) x by fun_prop)).inv
        (Complex.Gamma_ne_zero_of_re_pos hpos)).pow r).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨C, hC, hb⟩ := uniform_upperGamma_weighted_fixed_bound hr hA hz
    (le_max_left 0 M) (le_max_left 0 B) b
  refine ⟨max 0 B * Real.exp (|Real.log z| * max 0 M), by positivity, C, hC, ?_⟩
  filter_upwards [hb] with n hn x hx
  exact hn x ((hM x hx).trans (le_max_right 0 M)) _ ((hB x hx).trans (le_max_right 0 B))

end ThisWork.HigherRank
