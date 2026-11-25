module

public import ThisWork.Kernel
public import ThisWork.ImaginaryDigamma
public import ThisWork.Phase
public import ThisWork.AffineDigamma

/-! The exact scaled logarithmic derivative and its limiting equation in
arbitrary rank, keeping the Meijer G argument explicit. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

noncomputable def exactSaddleEquation (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (n : ℕ) (s : ℂ) : ℂ :=
  (r : ℂ) * Complex.digamma ((largeScale r n : ℂ) * s) -
    (∑ i, Complex.digamma ((A i : ℂ) * n - (largeScale r n : ℂ) * s + 1)) +
    2 * (Real.pi : ℂ) * Complex.I * j - (Real.log z : ℂ)

noncomputable def limitingEquation (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (s : ℂ) : ℂ :=
  (r : ℂ) * Complex.log s - (∑ i, (Real.log (A i) : ℂ)) +
    2 * (Real.pi : ℂ) * Complex.I * j - (Real.log z : ℂ)

theorem limitingEquation_eq_phase {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (j : ℤ) {θ : ℝ} (hθ : (r : ℝ) * θ = -2 * Real.pi * j) {s : ℂ} (hs : s ≠ 0) :
    limitingEquation r A z j s = Phase.equation r θ (saddleScale r A z) s := by
  let c := saddleScale r A z
  have hc : 0 < c := saddleScale_pos hA hz
  have hlogc : (r : ℂ) * (Real.log c : ℂ) =
      (∑ i, (Real.log (A i) : ℂ)) + (Real.log z : ℂ) := by
    exact_mod_cast log_saddleScale hr hA hz
  have ht : (r : ℂ) * (θ : ℂ) * Complex.I = - (2 * (Real.pi : ℂ) * Complex.I * j) := by
    have he : (r : ℂ) * (θ : ℂ) = -2 * (Real.pi : ℂ) * j := by exact_mod_cast hθ
    rw [he]
    ring
  have hdiv : Complex.log (s / (c : ℂ)) = Complex.log s - (Real.log c : ℂ) := by
    rw [show s / (c : ℂ) = ((c⁻¹ : ℝ) : ℂ) * s by push_cast; ring,
      Complex.log_ofReal_mul (inv_pos.mpr hc) hs, Real.log_inv, Complex.ofReal_neg]
    ring
  change (r : ℂ) * Complex.log s - (∑ i, (Real.log (A i) : ℂ)) +
      2 * (Real.pi : ℂ) * Complex.I * j - (Real.log z : ℂ) =
    (r : ℂ) * (Complex.log (s / (c : ℂ)) - (θ : ℂ) * Complex.I)
  rw [hdiv]
  linear_combination hlogc + ht

theorem hasDerivAt_limitingEquation (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ)
    {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    HasDerivAt (limitingEquation r A z j) ((r : ℂ) / s) s := by
  convert ((((Complex.hasDerivAt_log hs).const_mul (r : ℂ)).sub_const
    (∑ i, (Real.log (A i) : ℂ))).add_const
    (2 * (Real.pi : ℂ) * Complex.I * j)).sub_const (Real.log z : ℂ) using 1
  · rfl
  · rw [div_eq_mul_inv]

theorem exactSaddleEquation_eq_logDeriv {r : ℕ} {A : Fin (r - 1) → ℝ}
    (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) {s : ℂ}
    (hs : (largeScale r n : ℂ) * s ∈ kernelDomain r A n) :
    exactSaddleEquation r A z j n s =
      logDeriv (kernel r b A z j n) ((largeScale r n : ℂ) * s) :=
  (logDeriv_kernel b z j n hs).symm

theorem differentiableOn_exactSaddleEquation (r : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n : ℕ) :
    DifferentiableOn ℂ (exactSaddleEquation r A z j n)
      {s : ℂ | (largeScale r n : ℂ) * s ∈ kernelDomain r A n} := by
  have hf : DifferentiableOn ℂ (kernel r 1 A z j n) (kernelDomain r A n) :=
    fun x hx => (differentiableAt_kernel 1 z j n hx).differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv (kernel r 1 A z j n)) (kernelDomain r A n) := by
    convert (hf.deriv (isOpen_kernelDomain r A n)).div hf
      (fun x hx => kernel_ne_zero 1 z j n hx) using 1
    rfl
  have h := hlog.comp (show DifferentiableOn ℂ (fun s : ℂ => (largeScale r n : ℂ) * s)
      {s : ℂ | (largeScale r n : ℂ) * s ∈ kernelDomain r A n} by fun_prop)
    (fun s (hs : (largeScale r n : ℂ) * s ∈ kernelDomain r A n) => hs)
  apply h.congr
  intro s hs
  exact exactSaddleEquation_eq_logDeriv 1 z j n hs

theorem exactSaddleEquation_sub_limit {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 0) :
    exactSaddleEquation r A z j n s - limitingEquation r A z j s =
      (r : ℂ) * (Complex.digamma ((largeScale r n : ℂ) * s) -
        Complex.log ((largeScale r n : ℂ) * s)) -
      ∑ i, (Complex.digamma ((A i : ℂ) * n - (largeScale r n : ℂ) * s + 1) -
        Complex.log ((A i * n : ℝ) : ℂ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos hnR _
  have hlogR : (r : ℂ) * (Real.log (largeScale r n) : ℂ) =
      (((r : ℝ) - 1 : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ) := by
    exact_mod_cast log_largeScale hr hn
  have hi (i : Fin (r - 1)) : Complex.log ((A i * n : ℝ) : ℂ) =
      (Real.log (A i) : ℂ) + (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos (hA i) hnR).le,
      Real.log_mul (hA i).ne' hnR.ne', Complex.ofReal_add]
  have hsum : (∑ i, Complex.log ((A i * n : ℝ) : ℂ)) =
      (∑ i, (Real.log (A i) : ℂ)) + ((r - 1 : ℕ) : ℂ) * (Real.log (n : ℝ) : ℂ) := by
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold exactSaddleEquation limitingEquation
  rw [Complex.log_ofReal_mul hR hs, Finset.sum_sub_distrib, hsum]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr.ne'), Nat.cast_one]
  rw [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one] at hlogR
  linear_combination hlogR

theorem norm_exactSaddleEquation_sub_limit_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {n : ℕ} (hn : 0 < n) {M : ℝ} {s : ℂ} (hs : ‖s‖ ≤ M) (hs0 : s ≠ 0)
    (hAn : ∀ i, 4 ≤ A i * n) (hRM : ∀ i, largeScale r n * M ≤ (A i * n) / 4) :
    ‖exactSaddleEquation r A z j n s - limitingEquation r A z j s‖ ≤
      (r : ℝ) * ‖Complex.digamma ((largeScale r n : ℂ) * s) -
        Complex.log ((largeScale r n : ℂ) * s)‖ +
      ∑ i, (4 / (A i * n) + (3 / 2 : ℝ) * ((1 + largeScale r n * M) / (A i * n))) := by
  rw [exactSaddleEquation_sub_limit hr hA z j hn hs0]
  have hR : 0 ≤ largeScale r n := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).le
  calc
    _ ≤ ‖(r : ℂ) * (Complex.digamma ((largeScale r n : ℂ) * s) -
          Complex.log ((largeScale r n : ℂ) * s))‖ +
        ‖∑ i, (Complex.digamma ((A i : ℂ) * n - (largeScale r n : ℂ) * s + 1) -
          Complex.log ((A i * n : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul, Complex.norm_natCast]
      apply add_le_add le_rfl
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
        Analytic.norm_digamma_affine_sub_log_le (hAn i) hR (hRM i) hs

theorem eventually_affine_conditions {r : ℕ} (hr : 0 < r) {A : ℝ} (hA : 0 < A) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ A * n ∧ largeScale r n * M ≤ (A * n) / 4 := by
  have hratio : Tendsto (fun n : ℕ => (largeScale r n / (n : ℝ)) * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (largeScale_div_nat_tendsto hr).mul_const M
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (4 / A)), hratio.eventually_lt_const
      (show (0 : ℝ) < A / 4 by positivity), eventually_gt_atTop (0 : ℕ)] with n hn hsmall hn0
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hA).mp hn, ?_⟩
  rw [div_mul_eq_mul_div] at hsmall
  exact ((div_lt_iff₀ (Nat.cast_pos.mpr hn0)).mp hsmall).le.trans_eq (by ring)

theorem eventually_scaled_slit_in_kernelDomain {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, s.re ≤ M → s ∈ Complex.slitPlane →
      (largeScale r n : ℂ) * s ∈ kernelDomain r A n := by
  have hcond : ∀ᶠ n : ℕ in atTop, ∀ i,
      4 ≤ A i * n ∧ largeScale r n * M ≤ (A i * n) / 4 :=
    Filter.eventually_all.mpr (fun i => eventually_affine_conditions hr (hA i) M)
  filter_upwards [hcond, eventually_gt_atTop (0 : ℕ)] with n hn hn0 s hs hregion
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  refine ⟨?_, fun i => ?_⟩
  · rw [Complex.mem_slitPlane_iff]
    rcases Complex.mem_slitPlane_iff.mp hregion with hre | him
    · left
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        mul_pos hR hre
    · right
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
        mul_ne_zero hR.ne' him
  · have hle := mul_le_mul_of_nonneg_left hs hR.le
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [(hn i).1, (hn i).2]

theorem eventually_scaled_region_in_kernelDomain {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, s.re ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      (largeScale r n : ℂ) * s ∈ kernelDomain r A n := by
  filter_upwards [eventually_scaled_slit_in_kernelDomain hr hA M] with n hn s hs hregion
  apply hn s hs
  rw [Complex.mem_slitPlane_iff]
  exact hregion.elim (fun h => Or.inl (hκ.trans_le h))
    (fun h => Or.inr (abs_pos.mp (hη.trans_le h)))

theorem affineError_le_smallParameter {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    {A : ℝ} (hA : 0 < A) (M : ℝ) :
    4 / (A * n) + (3 / 2 : ℝ) * ((1 + largeScale r n * M) / (A * n)) ≤
      ((11 + 3 * M) / (2 * A)) * smallParameter r n := by
  have he : 4 / (A * n) + (3 / 2 : ℝ) * ((1 + largeScale r n * M) / (A * n)) =
      (11 / (2 * A)) * (1 / (n : ℝ)) + (3 * M / (2 * A)) * (largeScale r n / n) := by
    field_simp
    ring
  rw [he, largeScale_div_nat r (by omega)]
  calc
    _ ≤ (11 / (2 * A)) * smallParameter r n +
        (3 * M / (2 * A)) * smallParameter r n :=
      add_le_add (mul_le_mul_of_nonneg_left (inv_nat_le_smallParameter hr hn)
        (show 0 ≤ 11 / (2 * A) by positivity)) le_rfl
    _ = _ := by ring

/-- Quantitative uniform approximation of the actual saddle equation, including
regions crossing the imaginary axis, for every rank at least three. -/
theorem uniform_exactSaddleEquation_region {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {κ η M : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      ‖exactSaddleEquation r A z j n s - limitingEquation r A z j s‖ ≤ C * smallParameter r n := by
  let D := 2 / κ + 1 + 9 / η + 4 * Real.pi
  let C := (r : ℝ) * D + ∑ i, ((11 + 3 * M) / (2 * A i))
  refine ⟨C, ?_, ?_⟩
  · apply add_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (by dsimp only [D]; positivity)
    · apply Finset.sum_nonneg
      intro i _
      have hi := hA i
      positivity
  · have hcond : ∀ᶠ n : ℕ in atTop, ∀ i,
        4 ≤ A i * n ∧ largeScale r n * M ≤ (A i * n) / 4 :=
      Filter.eventually_all.mpr (fun i => eventually_affine_conditions (by omega : 0 < r) (hA i) M)
    filter_upwards [uniform_scaled_digamma_region_smallParameter hr hκ hη, hcond,
      eventually_ge_atTop (1 : ℕ)] with n hψ hc hn s hs hregion
    have hs0 : s ≠ 0 := by
      intro he
      rw [he, Complex.zero_re, Complex.zero_im, abs_zero] at hregion
      rcases hregion with h | h <;> linarith
    have hb := norm_exactSaddleEquation_sub_limit_le (by omega : 0 < r) hA z j
      (by omega : 0 < n) hs hs0 (fun i => (hc i).1) (fun i => (hc i).2)
    have hl : (r : ℝ) * ‖Complex.digamma ((largeScale r n : ℂ) * s) -
        Complex.log ((largeScale r n : ℂ) * s)‖ ≤ (r : ℝ) * D * smallParameter r n := by
      calc
        _ ≤ (r : ℝ) * (D * smallParameter r n) :=
          mul_le_mul_of_nonneg_left (hψ s hregion) (Nat.cast_nonneg _)
        _ = _ := by ring
    have hu : (∑ i, (4 / (A i * n) + (3 / 2 : ℝ) * ((1 + largeScale r n * M) / (A i * n)))) ≤
        (∑ i, ((11 + 3 * M) / (2 * A i))) * smallParameter r n := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => affineError_le_smallParameter
        (show 1 ≤ r by omega) hn (hA i) M)
    exact hb.trans ((add_le_add hl hu).trans_eq (by dsimp only [C]; ring))

end ThisWork
