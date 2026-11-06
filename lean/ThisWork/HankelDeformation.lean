module

public import ThisWork.AbsoluteConvergence

/-! Contour deformation for the actual Mellin–Barnes integrals. -/

public section

namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

theorem differentiableOn_weighted_kernel (α₁ α₂ : ℝ) (j : Branch) (n k : ℕ) :
    DifferentiableOn ℂ (fun x : ℂ => ((n : ℂ) - x) ^ k * kernel α₁ α₂ j n x)
      (kernelDomain α₁ α₂ n) := by
  exact (by fun_prop : Differentiable ℂ (fun x : ℂ => ((n : ℂ) - x) ^ k)).differentiableOn.mul
    (differentiableOn_kernel α₁ α₂ j n)

theorem rectangle_integral_identity {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) {a r A B : ℝ}
    (hrect : ∀ z : ℂ, z.re ∈ uIcc a r → z.im ∈ uIcc A B → z ∈ U) :
    (∫ u in a..r, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
      (∫ u in a..r, f ((u : ℂ) + (B : ℂ) * Complex.I)) +
      (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) -
      (∫ v in A..B, Complex.I * f ((a : ℂ) + (v : ℂ) * Complex.I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (A : ℂ) * Complex.I) ((r : ℂ) + (B : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add,
    smul_eq_mul, ← intervalIntegral.integral_const_mul] at h
  exact h (hf.mono fun z hz => hrect z hz.1 hz.2)

theorem horizontal_tail_identity_of_rectangles {f : ℂ → ℂ} {r A B : ℝ}
    (hA : IntegrableOn (fun u : ℝ => f ((u : ℂ) + (A : ℂ) * Complex.I)) (Iic r))
    (hB : IntegrableOn (fun u : ℝ => f ((u : ℂ) + (B : ℂ) * Complex.I)) (Iic r))
    (hleft : Tendsto (fun T : ℝ => ∫ v in A..B,
      Complex.I * f (-(T : ℂ) + (v : ℂ) * Complex.I)) atTop (𝓝 0))
    (hrect : ∀ᶠ T : ℝ in atTop,
      (∫ u in -T..r, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
        (∫ u in -T..r, f ((u : ℂ) + (B : ℂ) * Complex.I)) +
        (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) -
        (∫ v in A..B, Complex.I * f (-(T : ℂ) + (v : ℂ) * Complex.I)) = 0) :
    (∫ u in Iic r, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
      (∫ u in Iic r, f ((u : ℂ) + (B : ℂ) * Complex.I)) +
      (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) = 0 := by
  have h := (((intervalIntegral_tendsto_integral_Iic r hA tendsto_neg_atTop_atBot).sub
    (intervalIntegral_tendsto_integral_Iic r hB tendsto_neg_atTop_atBot)).add_const
      (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I))).sub hleft
  simpa only [sub_zero] using tendsto_nhds_unique h (tendsto_const_nhds.congr' (hrect.mono fun _ hx => hx.symm))

theorem weighted_horizontal_tail_deformation {α₁ α₂ r H A B : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hH : 1 ≤ H) (j : Branch) (n k : ℕ)
    (hr : r < min (α₁ * n + 1) (α₂ * n + 1))
    (hstrip : ∀ v ∈ uIcc A B, 1 ≤ |v| ∧ |v| ≤ H) :
    (∫ u in Iic r, ((n : ℂ) - ((u : ℂ) + (A : ℂ) * Complex.I)) ^ k *
      kernel α₁ α₂ j n ((u : ℂ) + (A : ℂ) * Complex.I)) -
    (∫ u in Iic r, ((n : ℂ) - ((u : ℂ) + (B : ℂ) * Complex.I)) ^ k *
      kernel α₁ α₂ j n ((u : ℂ) + (B : ℂ) * Complex.I)) +
    (∫ v in A..B, Complex.I * (((n : ℂ) - ((r : ℂ) + (v : ℂ) * Complex.I)) ^ k *
      kernel α₁ α₂ j n ((r : ℂ) + (v : ℂ) * Complex.I))) = 0 := by
  refine horizontal_tail_identity_of_rectangles
    (f := fun x : ℂ => ((n : ℂ) - x) ^ k * kernel α₁ α₂ j n x)
    (r := r) (A := A) (B := B)
    (integrableOn_weighted_kernel_horizontal h₁ h₂ j n k hr (hstrip A left_mem_uIcc).1)
    (integrableOn_weighted_kernel_horizontal h₁ h₂ j n k hr (hstrip B right_mem_uIcc).1)
    (tendsto_left_bridge_zero h₁ h₂ hH j n k hstrip) ?_
  filter_upwards [eventually_ge_atTop (-r)] with T hT
  convert rectangle_integral_identity (differentiableOn_weighted_kernel α₁ α₂ j n k)
    (a := -T) (r := r) (A := A) (B := B) ?_ using 1
  · simp only [Complex.ofReal_neg]
  intro z hzre hzim
  exact ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by
      have h := (hstrip z.im hzim).1
      intro hz
      norm_num [hz] at h)),
    ((show z.re ≤ r by simpa only [max_eq_right (show -T ≤ r by linarith)] using hzre.2).trans_lt hr)⟩

theorem positive_height_strip {A B v : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hv : v ∈ uIcc A B) : 1 ≤ |v| ∧ |v| ≤ max A B := by
  have hv₁ : 1 ≤ v := (le_min hA hB).trans hv.1
  simpa only [abs_of_nonneg (show 0 ≤ v by linarith)] using And.intro hv₁ hv.2

theorem negative_height_strip {A B v : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hv : v ∈ uIcc (-A) (-B)) : 1 ≤ |v| ∧ |v| ≤ max A B := by
  have hn : -v ∈ uIcc A B := by
    rw [uIcc, mem_Icc, min_neg_neg, max_neg_neg] at hv
    exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
  simpa only [abs_neg] using positive_height_strip hA hB hn

theorem weighted_hankel_height_eq {α₁ α₂ r A B : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n k : ℕ)
    (hr₀ : 0 < r) (hr : r < min (α₁ * n + 1) (α₂ * n + 1))
    (hA : 1 ≤ A) (hB : 1 ≤ B) :
    hankelIntegral r A (fun x => ((n : ℂ) - x) ^ k * kernel α₁ α₂ j n x) =
      hankelIntegral r B (fun x => ((n : ℂ) - x) ^ k * kernel α₁ α₂ j n x) := by
  have hlo := weighted_horizontal_tail_deformation h₁ h₂
    (H := max B A) (hB.trans (le_max_left B A)) j n k hr
    (A := -B) (B := -A) (fun v hv => negative_height_strip hB hA hv)
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hlo
  have hhi := weighted_horizontal_tail_deformation h₁ h₂
    (H := max A B) (hA.trans (le_max_left A B)) j n k hr
    (A := A) (B := B) (fun v hv => positive_height_strip hA hB hv)
  have hvleft := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_weighted_kernel_vertical j n k hr₀ hr (-B) (-A))
    (intervalIntegrable_weighted_kernel_vertical j n k hr₀ hr (-A) A)
  have hvright := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_weighted_kernel_vertical j n k hr₀ hr (-B) A)
    (intervalIntegrable_weighted_kernel_vertical j n k hr₀ hr A B)
  dsimp only [hankelIntegral]
  linear_combination -hlo - hhi + hvleft + hvright

theorem weighted_hankel_right_eq {α₁ α₂ r s h : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n k : ℕ)
    (hr₀ : 0 < r) (hs₀ : 0 < s)
    (hr : r < min (α₁ * n + 1) (α₂ * n + 1))
    (hs : s < min (α₁ * n + 1) (α₂ * n + 1)) (hh : 1 ≤ h) :
    hankelIntegral r h (fun x => ((n : ℂ) - x) ^ k * kernel α₁ α₂ j n x) =
      hankelIntegral s h (fun x => ((n : ℂ) - x) ^ k * kernel α₁ α₂ j n x) := by
  have hrect := rectangle_integral_identity (differentiableOn_weighted_kernel α₁ α₂ j n k)
    (a := r) (r := s) (A := -h) (B := h)
    (fun z hz _ => ⟨Complex.mem_slitPlane_iff.mpr (Or.inl ((lt_min hr₀ hs₀).trans_le hz.1)),
      hz.2.trans_lt (max_lt_iff.mpr ⟨hr, hs⟩)⟩)
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hrect
  have hiR := weighted_hankel_absolutely_convergent h₁ h₂ j n k hr₀ hr hh
  have hiS := weighted_hankel_absolutely_convergent h₁ h₂ j n k hs₀ hs hh
  have hlo := intervalIntegral.integral_Iic_sub_Iic hiR.1 hiS.1
  have hhi := intervalIntegral.integral_Iic_sub_Iic hiR.2.2 hiS.2.2
  dsimp only [hankelIntegral]
  linear_combination -hrect - hlo + hhi

/-- The original vector integral may be evaluated on any admissible symmetric
polygonal Hankel contour, component by component. -/
theorem branchIntegral_eq_deformed {α₁ α₂ r h : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n : ℕ) (k : Fin 3)
    (hr₀ : 0 < r) (hr : r < min (α₁ * n + 1) (α₂ * n + 1)) (hh : 1 ≤ h) :
    branchIntegral α₁ α₂ j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      hankelIntegral r h (fun x => ((n : ℂ) - x) ^ k.val * kernel α₁ α₂ j n x) := by
  have href : (1 / 2 : ℝ) < min (α₁ * n + 1) (α₂ * n + 1) := by
    apply lt_min <;> nlinarith [mul_nonneg h₁.le (Nat.cast_nonneg (α := ℝ) n),
      mul_nonneg h₂.le (Nat.cast_nonneg (α := ℝ) n)]
  exact congrArg (fun z : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
    ((weighted_hankel_height_eq h₁ h₂ j n k.val (by norm_num) href le_rfl hh).trans
      (weighted_hankel_right_eq h₁ h₂ j n k.val (by norm_num) hr₀ href hr hh))

end ThisWork
