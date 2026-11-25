module

public import ThisWork.Definitions

/-! The limiting logarithmic phase in arbitrary rank, parametrized by the
saddle angle. The angle is kept in the open principal-log interval. -/

@[expose] public section
namespace ThisWork.Phase

open Set

noncomputable def rho (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

noncomputable def equation (r : ℕ) (θ c : ℝ) (s : ℂ) : ℂ :=
  (r : ℂ) * (Complex.log (s / (c : ℂ)) - (θ : ℂ) * Complex.I)

noncomputable def phase (r : ℕ) (θ c : ℝ) (s : ℂ) : ℂ :=
  s * (equation r θ c s - r)

/-- A Gaussian descent direction, including for purely imaginary saddles. -/
noncomputable def direction (θ : ℝ) : ℂ :=
  Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)

theorem log_rho {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    Complex.log (rho θ) = (θ : ℂ) * Complex.I := by
  apply Complex.log_exp
  · simpa using hθ.1
  · simpa using hθ.2.le

theorem rho_mem_slitPlane {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    rho θ ∈ Complex.slitPlane := by
  have harg : Complex.arg (rho θ) = θ := by
    rw [← Complex.log_im, log_rho hθ]
    simp
  exact Complex.mem_slitPlane_iff_arg.mpr
    ⟨by rw [harg]; exact hθ.2.ne, Complex.exp_ne_zero _⟩

theorem equation_saddle (r : ℕ) {θ c : ℝ}
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hc : 0 < c) :
    equation r θ c ((c : ℂ) * rho θ) = 0 := by
  rw [equation, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hc.ne'), log_rho hθ]
  ring

theorem phase_saddle (r : ℕ) {θ c : ℝ}
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hc : 0 < c) :
    phase r θ c ((c : ℂ) * rho θ) = -(r : ℂ) * c * rho θ := by
  rw [phase, equation_saddle r hθ hc]
  ring

theorem hasDerivAt_equation (r : ℕ) (θ : ℝ) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (equation r θ c) ((r : ℂ) / s) s := by
  convert ((ThisWork.hasDerivAt_log_scale hc hs).sub_const
    ((θ : ℂ) * Complex.I)).const_mul (r : ℂ) using 1
  · rfl
  · simp only [mul_one_div]

theorem hasDerivAt_phase (r : ℕ) (θ : ℝ) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (phase r θ c) (equation r θ c s) s := by
  have h := (hasDerivAt_id s).mul ((hasDerivAt_equation r θ hc hs).sub_const (r : ℂ))
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  convert h using 1
  · rfl
  · simp only [one_mul, id_eq, mul_div_cancel₀ _ hs0, sub_add_cancel]

theorem direction_sq (θ : ℝ) : direction θ ^ 2 = -rho θ := by
  have he : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) ^ 2 = rho θ := by
    rw [pow_two, ← Complex.exp_add]
    unfold rho
    congr 1
    push_cast
    ring
  rw [direction, mul_pow, Complex.I_sq, he]
  ring

theorem gaussian_coefficient (r : ℕ) (θ : ℝ) {c : ℝ} (hc : 0 < c) :
    ((r : ℂ) / ((c : ℂ) * rho θ)) * direction θ ^ 2 = -(r : ℂ) / c := by
  rw [direction_sq]
  have hρ : rho θ ≠ 0 := Complex.exp_ne_zero _
  field_simp [Complex.ofReal_ne_zero.mpr hc.ne']

theorem gaussian_coefficient_re_neg {r : ℕ} (hr : 0 < r) (θ : ℝ)
    {c : ℝ} (hc : 0 < c) :
    (((r : ℂ) / ((c : ℂ) * rho θ)) * direction θ ^ 2).re < 0 := by
  rw [gaussian_coefficient r θ hc]
  simp only [Complex.div_ofReal_re, Complex.neg_re, Complex.natCast_re]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (Nat.cast_pos.mpr hr)) hc

theorem equation_eq_zero_iff {r : ℕ} (hr : 0 < r) {θ c : ℝ}
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hc : 0 < c) {s : ℂ} (hs : s ≠ 0) :
    equation r θ c s = 0 ↔ s = (c : ℂ) * rho θ := by
  constructor
  · intro he
    have hlog : Complex.log (s / (c : ℂ)) = (θ : ℂ) * Complex.I :=
      sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr hr.ne'))
    have heq := congrArg Complex.exp hlog
    rw [Complex.exp_log (div_ne_zero hs (Complex.ofReal_ne_zero.mpr hc.ne'))] at heq
    calc
      s = (s / (c : ℂ)) * c := (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hc.ne')).symm
      _ = rho θ * c := congrArg (fun x : ℂ => x * c) heq
      _ = (c : ℂ) * rho θ := mul_comm _ _
  · rintro rfl
    exact equation_saddle r hθ hc

end ThisWork.Phase
