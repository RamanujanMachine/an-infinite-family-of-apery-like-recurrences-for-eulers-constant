module

public import ThisWork.HigherRank.Kernel
public import ThisWork.HankelTails

/-! Absolute decay on horizontal Mellin--Barnes tails in arbitrary rank. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem log_norm_kernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (m : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) {x : ℂ} (hx : x ∈ kernelDomain r A n) :
    Real.log ‖kernel r m A z j n x‖ = (r : ℝ) * Real.log ‖Complex.Gamma x‖ +
      (∑ i, Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖) +
      (2 * (Real.pi : ℂ) * Complex.I * j * x).re +
      ((Real.log z : ℂ) * ((m : ℂ) * n - x)).re := by
  have h₀ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (Analytic.not_neg_nat_of_mem_slitPlane hx.1))
  have hi (i : Fin (r - 1)) := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (upper_re_pos hx i))
  simp only [kernel, norm_mul, norm_pow, norm_prod, Complex.norm_exp]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero r h₀)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hi i))) (Real.exp_ne_zero _)) (Real.exp_ne_zero _),
    Real.log_mul (mul_ne_zero (pow_ne_zero r h₀) (Finset.prod_ne_zero_iff.mpr (fun i _ => hi i)))
      (Real.exp_ne_zero _),
    Real.log_mul (pow_ne_zero r h₀) (Finset.prod_ne_zero_iff.mpr (fun i _ => hi i)),
    Real.log_pow, Real.log_prod (fun i _ => hi i), Real.log_exp, Real.log_exp]

theorem uniform_log_norm_kernel_left_strip {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {H : ℝ} (hH : 1 ≤ H)
    (m : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) :
    ∃ B ≥ 0, ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      Real.log ‖kernel r m A z j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        -T * Real.log T + (1 + |Real.log z|) * T +
          ((∑ i, (A i * n + 1)) + 2) * Real.log T + B := by
  let D := (∑ i, (A i * n + 1)) + 1
  have hshift (i : Fin (r - 1)) : 0 ≤ A i * n + 1 := by
    have hi := hA i
    positivity
  have hsum : 0 ≤ ∑ i, (A i * n + 1) := Finset.sum_nonneg (fun i _ => hshift i)
  have hiD (i : Fin (r - 1)) : A i * n + 1 ≤ D := by
    have h := Finset.single_le_sum (fun i _ => hshift i) (Finset.mem_univ i)
    dsimp only [D]
    linarith
  obtain ⟨C, hC, hb⟩ := Analytic.uniform_log_norm_Gamma_strip_shift
    (D := D) (H := H) (by dsimp only [D]; positivity) (by linarith)
  let B := (2 * (r : ℝ)) * C + (r : ℝ) * (Real.log Real.pi + Real.log 4) +
    2 * Real.pi * |(j : ℝ)| * H + |Real.log z| * (m : ℝ) * n + |Analytic.gammaNormError 2|
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  filter_upwards [hb] with T hT y hy hyH
  let x : ℂ := -(T : ℂ) + (y : ℂ) * Complex.I
  have hxre : x.re = -T := by simp [x, Complex.mul_re]
  have hxim : x.im = y := by simp [x]
  have hynz : y ≠ 0 := by intro he; norm_num [he] at hy
  have hx : x ∈ kernelDomain r A n := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa only [hxim] using hynz)), ?_⟩
    intro i
    rw [hxre]
    nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n, hT.1]
  have hsh (a : ℝ) (ha : 0 ≤ a) (haD : a ≤ D) :
      |Real.log ‖Complex.Gamma ((T : ℂ) + (a : ℂ) - (y : ℂ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma (T : ℂ)‖ - a * Real.log (T - 1)| ≤ C := by
    simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      hT.2 a ha haD (-y) (by simpa using hyH)
  have hzero : Real.log ‖Complex.Gamma (T : ℂ)‖ - C ≤ Real.log ‖Complex.Gamma (-x)‖ := by
    have h := (abs_le.mp (hsh 0 le_rfl (by dsimp only [D]; positivity))).1
    simp only [Complex.ofReal_zero, add_zero, zero_mul, sub_zero] at h
    rw [show -x = (T : ℂ) - (y : ℂ) * Complex.I by dsimp only [x]; ring]
    linarith
  have hlogx : 0 ≤ Real.log ‖x‖ := by
    apply Real.log_nonneg
    have h := Complex.abs_re_le_norm x
    rw [hxre, abs_neg, abs_of_nonneg (by linarith [hT.1] : 0 ≤ T)] at h
    linarith [hT.1]
  have hl := Analytic.log_norm_Gamma_reflection (by rw [hxre]; linarith [hT.1])
    (by simpa only [hxim] using hynz)
  have hsin := Analytic.log_norm_sine_tail_lower (z := x) (by simpa only [hxim] using hy)
  have hleft : Real.log ‖Complex.Gamma x‖ ≤
      Real.log Real.pi + Real.log 4 - Real.log ‖Complex.Gamma (T : ℂ)‖ + C := by linarith
  have hu (i : Fin (r - 1)) :
      Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖ ≤
        Real.log ‖Complex.Gamma (T : ℂ)‖ + (A i * n + 1) * Real.log T + C := by
    have h := (abs_le.mp (hsh (A i * n + 1) (hshift i) (hiD i))).2
    rw [show (T : ℂ) + ((A i * n + 1 : ℝ) : ℂ) - (y : ℂ) * Complex.I =
      (A i : ℂ) * n - x + 1 by dsimp only [x]; push_cast; ring] at h
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith [hT.1] : 0 < T - 1) (by linarith : T - 1 ≤ T)) (hshift i)
    linarith
  have huSum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at huSum
  rw [← Finset.sum_mul] at huSum
  have htw : (2 * (Real.pi : ℂ) * Complex.I * j * x).re ≤ 2 * Real.pi * |(j : ℝ)| * H := by
    have ht : (2 * (Real.pi : ℂ) * Complex.I * j * x).re = -(2 * Real.pi * (j : ℝ) * y) := by
      simp [Complex.mul_re, Complex.mul_im, hxim]
    rw [ht]
    calc
      _ ≤ |2 * Real.pi * (j : ℝ) * y| := neg_le_abs _
      _ = 2 * Real.pi * |(j : ℝ)| * |y| := by rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hyH (by positivity)
  have hz : ((Real.log z : ℂ) * ((m : ℂ) * n - x)).re ≤
      |Real.log z| * ((m : ℝ) * n + T) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_re, Complex.natCast_re, Complex.natCast_im, mul_zero, hxre]
    have h := mul_le_mul_of_nonneg_right (le_abs_self (Real.log z))
      (by nlinarith [hT.1, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n] : 0 ≤ (m : ℝ) * n + T)
    nlinarith
  have hrleft := mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hmain := Analytic.log_norm_Gamma_real_lower hT.1
  rw [log_norm_kernel m z j n hx]
  have hB := le_max_right 0 B
  dsimp only [B] at hB ⊢
  nlinarith

theorem uniform_kernel_left_decay {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {H : ℝ} (hH : 1 ≤ H)
    (m : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      ‖kernel r m A z j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (-q * T) := by
  obtain ⟨B, _, hb⟩ := uniform_log_norm_kernel_left_strip hr hA hH m z j n
  filter_upwards [hb, Analytic.eventually_log_tail_le ((∑ i, (A i * n + 1)) + 2) B
    (q + |Real.log z|), eventually_ge_atTop (0 : ℝ)] with T hT hq hT0 y hy hyH
  exact (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (by linarith [hT y hy hyH, hq.2]))

theorem uniform_weighted_kernel_left_decay {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {H : ℝ} (hH : 1 ≤ H)
    (m : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      ‖(((m : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I)) ^ k) *
        kernel r m A z j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (-q * T) := by
  filter_upwards [uniform_kernel_left_decay hr hA hH m z j n (q + 1),
    Analytic.eventually_shifted_pow_le_exp (D := ((m * n : ℕ) : ℝ) + H) (by positivity) k,
    eventually_ge_atTop (0 : ℝ)] with T hK hP hT y hy hyH
  have hpoly : ‖(m : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ T + (((m * n : ℕ) : ℝ) + H) := by
    simpa only [Nat.cast_mul] using Analytic.norm_polynomial_left_le hT hyH (m * n)
  calc
    _ = ‖(m : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ^ k *
        ‖kernel r m A z j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ := by rw [norm_mul, norm_pow]
    _ ≤ Real.exp T * Real.exp (-(q + 1) * T) :=
      mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) hpoly k).trans hP)
        (hK y hy hyH) (norm_nonneg _) (Real.exp_pos T).le
    _ = Real.exp (-q * T) := by rw [← Real.exp_add]; congr 1; ring

end ThisWork.HigherRank
