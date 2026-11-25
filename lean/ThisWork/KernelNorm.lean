module

public import ThisWork.HankelTails
public import ThisWork.KernelApproximation

/-! Exact separation of the common Gamma scale, limiting phase, and Gamma
errors. The branch label and positive Meijer G argument remain parameters. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem sum_log_upper_gaps {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) {n : ℕ} (hn : 0 < n) :
    (∑ i, Real.log (A i * n)) = (∑ i, Real.log (A i)) + ((r : ℝ) - 1) * Real.log (n : ℝ) := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    Real.log_mul (hA i).ne' (Nat.cast_ne_zero.mpr hn.ne'))]
  simp [Finset.sum_add_distrib, Nat.cast_sub (by omega : 1 ≤ r)]

theorem scaled_stirlingMain_kernel {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ) {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 0) :
    (r : ℂ) * Analytic.stirlingMain ((largeScale r n : ℂ) * s) -
      ((largeScale r n : ℂ) * s) * (∑ i, (Real.log (A i * n) : ℂ)) +
      (2 * (Real.pi : ℂ) * Complex.I * j) * ((largeScale r n : ℂ) * s) -
      (Real.log z : ℂ) * ((largeScale r n : ℂ) * s) =
        (largeScale r n : ℂ) * limitingPhase r A z j s := by
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hscale : (r : ℂ) * (Real.log (largeScale r n) : ℂ) =
      ((r : ℂ) - 1) * (Real.log (n : ℝ) : ℂ) := by exact_mod_cast log_largeScale hr hn
  have hsum : (∑ i, (Real.log (A i * n) : ℂ)) =
      (∑ i, (Real.log (A i) : ℂ)) + ((r : ℂ) - 1) * (Real.log (n : ℝ) : ℂ) := by
    exact_mod_cast sum_log_upper_gaps hr hA hn
  rw [Analytic.stirlingMain, Complex.log_ofReal_mul hR hs, hsum, limitingPhase, limitingEquation]
  linear_combination (largeScale r n : ℂ) * s * hscale

theorem log_gammaScale {r : ℕ} {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (n : ℕ) :
    Real.log (gammaScale r A n) = ∑ i, Real.log ‖Complex.Gamma ((A i * n + 1 : ℝ) : ℂ)‖ := by
  have hpos (i : Fin (r - 1)) : 0 < Real.Gamma (A i * n + 1) :=
    Real.Gamma_pos_of_pos (by have hi := hA i; positivity)
  rw [gammaScale, Real.log_prod (fun i _ => (hpos i).ne')]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.Gamma_ofReal, Complex.norm_of_nonneg (hpos i).le]

theorem gammaScale_pos {r : ℕ} {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (n : ℕ) :
    0 < gammaScale r A n :=
  Finset.prod_pos (fun i _ => Real.Gamma_pos_of_pos (by have hi := hA i; positivity))

theorem commonScale_pos {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (b n : ℕ) : 0 < commonScale r b A z n :=
  mul_pos (gammaScale_pos hA n) (pow_pos hz _)

theorem log_commonScale {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (b n : ℕ) :
    Real.log (commonScale r b A z n) = Real.log (gammaScale r A n) + Real.log z * ((b : ℝ) * n) := by
  rw [commonScale, Real.log_mul (gammaScale_pos hA n).ne' (pow_pos hz _).ne', Real.log_pow]
  push_cast
  ring

noncomputable def rightGammaNormError (r : ℕ) (α : ℝ) (n : ℕ) (s : ℂ) : ℝ :=
  Real.log ‖Complex.Gamma ((α : ℂ) * n - (largeScale r n : ℂ) * s + 1)‖ -
    Real.log ‖Complex.Gamma ((α * n + 1 : ℝ) : ℂ)‖ + largeScale r n * s.re * Real.log (α * n)

theorem uniform_rightGammaNormError {r : ℕ} (hr : 1 ≤ r) {α M : ℝ} (hα : 0 < α) (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M →
      |rightGammaNormError r α n s| ≤ C * (largeScale r n * smallParameter r n) := by
  let L := (11 + 3 * (2 * M)) / (2 * α)
  refine ⟨M * L, by dsimp only [L]; positivity, ?_⟩
  filter_upwards [eventually_affine_conditions (by omega : 0 < r) hα (2 * M),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 s hs
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have h := Analytic.abs_log_norm_Gamma_affine_sub_le hn.1 hR hM (by nlinarith [hn.2]) hs
  rw [Complex.ofReal_mul, Complex.ofReal_natCast] at h
  apply h.trans
  have hB : 4 / (α * n) + (3 / 2 : ℝ) * ((1 + 2 * largeScale r n * M) / (α * n)) ≤
      L * smallParameter r n := by
    simpa only [L, mul_left_comm, mul_assoc] using affineError_le_smallParameter hr hn1 hα (2 * M)
  calc
    _ ≤ largeScale r n * M * (L * smallParameter r n) :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg hR.le hM.le)
    _ = _ := by ring

theorem log_norm_kernel_error {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) {n : ℕ} (hn : 0 < n)
    {s : ℂ} (hs : s ≠ 0) (hx : (largeScale r n : ℂ) * s ∈ kernelDomain r A n) :
    Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * s)‖ - Real.log (gammaScale r A n) -
      Real.log z * ((b : ℝ) * n) - largeScale r n * (limitingPhase r A z j s).re =
      (r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * s) +
        ∑ i, rightGammaNormError r (A i) n s := by
  have hk := log_norm_kernel b z j n hx
  have hH := log_gammaScale hA n
  have hm := congrArg Complex.re (scaled_stirlingMain_kernel hr hA z j hn hs)
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum, Complex.im_sum,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, mul_zero,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Finset.sum_const_zero,
    mul_one, sub_zero, add_zero, zero_add] at hm hk
  simp only [rightGammaNormError, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, mul_assoc]
  dsimp only [Analytic.gammaNormError]
  nlinarith

end ThisWork
