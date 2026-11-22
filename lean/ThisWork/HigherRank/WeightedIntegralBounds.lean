module

public import ThisWork.HigherRank.ReflectedIntegralUpper

/-! A polynomially weighted window-and-tail estimate. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set MeasureTheory

theorem integral_polynomial_weight_le_window_tail {f : ℝ → ℂ} {Q : ℝ → ℝ}
    {R T L M C : ℝ} (k : ℕ) (hR : 1 ≤ R) (hT : 1 ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hab : -(R * T) ≤ L) (hf : IntegrableOn f (Iic L))
    (hQ : ∀ x, 0 ≤ Q x)
    (hdom : ∀ x ≤ L, ‖f x‖ ≤ C * (1 + |x|) ^ k * Q x)
    (hwindow : ∀ x ∈ Icc (-(R * T)) L, Q x ≤ M)
    (htail : ∀ t ≥ T, Q (-R * t) ≤ M * Real.exp (-2 * R * (t - T)))
    (hpoly : ∀ t ≥ T, (1 + t) ^ k ≤ Real.exp t) :
    ‖∫ x in Iic L, f x‖ ≤
      C * R ^ k * max ((1 + T + |L|) ^ k) (Real.exp T) * M * (1 + L + R * T) := by
  let K := max ((1 + T + |L|) ^ k) (Real.exp T)
  let G := C * R ^ k * K * M
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hK : 0 ≤ K := (Real.exp_pos T).le.trans (le_max_right _ _)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hb := integral_Iic_le_window_tail hab hf.norm (M := G) (fun x hx => by
    have hax : |x| ≤ R * T + |L| := abs_le.mpr ⟨by linarith [hx.1, abs_nonneg L],
      by nlinarith [hx.2, le_abs_self L, mul_nonneg hR0.le (zero_lt_one.trans_le hT).le]⟩
    have hpow : (1 + |x|) ^ k ≤ R ^ k * (1 + T + |L|) ^ k := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hR (abs_nonneg L)]
    calc
      _ ≤ C * (1 + |x|) ^ k * Q x := hdom x hx.2
      _ ≤ C * (R ^ k * (1 + T + |L|) ^ k) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) (hwindow x hx) (hQ x) (by positivity)
      _ ≤ G := by
        dsimp only [G]
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left ((1 + T + |L|) ^ k) (Real.exp T))
          (show 0 ≤ C * R ^ k * M by positivity)]) (fun x hx => by
    let t := -x / R
    have ht : T ≤ t := (le_div_iff₀ hR0).mpr (by nlinarith)
    have ht0 : 0 ≤ t := by linarith
    have hid : -R * t = x := by dsimp only [t]; field_simp
    have hx0 : x ≤ 0 := by nlinarith
    have hax : |x| = R * t := by rw [abs_of_nonpos hx0]; nlinarith [hid]
    have hpow : (1 + |x|) ^ k ≤ R ^ k * Real.exp t := by
      rw [hax]
      calc
        _ ≤ (R * (1 + t)) ^ k := pow_le_pow_left₀ (by positivity) (by nlinarith) k
        _ = R ^ k * (1 + t) ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpoly t ht) (by positivity)
    have hqt := htail t ht
    rw [hid] at hqt
    have hphase : t - 2 * R * (t - T) ≤ T + (x - -(R * T)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr ht)]
    calc
      _ ≤ C * (1 + |x|) ^ k * Q x := hdom x (hx.trans hab)
      _ ≤ C * (R ^ k * Real.exp t) * (M * Real.exp (-2 * R * (t - T))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hqt (hQ x) (by positivity)
      _ = (C * R ^ k * M) * Real.exp (t - 2 * R * (t - T)) := by
        rw [show t - 2 * R * (t - T) = t + (-2 * R * (t - T)) by ring, Real.exp_add]
        ring
      _ ≤ (C * R ^ k * M) * Real.exp (T + (x - -(R * T))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (by positivity)
      _ ≤ G * Real.exp (x - -(R * T)) := by
        rw [Real.exp_add]
        dsimp only [G]
        nlinarith [mul_le_mul_of_nonneg_left (le_max_right ((1 + T + |L|) ^ k) (Real.exp T))
          (show 0 ≤ C * R ^ k * M * Real.exp (x - -(R * T)) by positivity)])
  exact (norm_integral_le_integral_norm _).trans (by simpa only [sub_neg_eq_add] using hb)

end ThisWork.HigherRank
