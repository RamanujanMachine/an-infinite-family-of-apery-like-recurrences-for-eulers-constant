module

public import ThisWork.Argument
public import ThisWork.HankelTails
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute convergence of the actual polynomially weighted Hankel integrals. -/

public section

namespace ThisWork.Analytic


open Set Filter MeasureTheory
open scoped Topology

theorem integrableOn_Iic_of_exp_bound {f : ℝ → ℂ} {r : ℝ}
    (hf : ContinuousOn f (Iic r)) (hb : ∀ᶠ u : ℝ in atBot, ‖f u‖ ≤ Real.exp u) :
    IntegrableOn f (Iic r) := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp hb
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr
    ⟨⟨Iic (min a r), Iic_mem_atBot _, ?_⟩, hf.locallyIntegrableOn measurableSet_Iic⟩
  exact (integrableOn_exp_Iic _).mono'
    ((hf.mono (Iic_subset_Iic.mpr (min_le_right a r))).aestronglyMeasurable measurableSet_Iic)
    ((ae_restrict_mem measurableSet_Iic).mono fun u hu => ha u (hu.trans (min_le_left a r)))

theorem horizontal_mem_kernelDomain {α₁ α₂ r y u : ℝ} {n : ℕ}
    (hr : r < min (α₁ * n + 1) (α₂ * n + 1)) (hy : y ≠ 0) (hu : u ≤ r) :
    (u : ℂ) + (y : ℂ) * Complex.I ∈ kernelDomain α₁ α₂ n := by
  constructor
  · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hy))
  · simpa [Complex.mul_re] using hu.trans_lt hr

theorem continuousOn_weighted_kernel [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n k : ℕ) :
    ContinuousOn (fun x : ℂ => ((n : ℂ) - x) ^ k * normalizedKernel α₁ α₂ j n x)
      (kernelDomain α₁ α₂ n) := by
  exact (by fun_prop : Continuous (fun x : ℂ => ((n : ℂ) - x) ^ k)).continuousOn.mul
    (differentiableOn_kernel α₁ α₂ j n).continuousOn

theorem integrableOn_weighted_kernel_horizontal [PositiveArgument] {α₁ α₂ r y : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n k : ℕ)
    (hr : r < min (α₁ * n + 1) (α₂ * n + 1)) (hy : 1 ≤ |y|) :
    IntegrableOn (fun u : ℝ => ((n : ℂ) - ((u : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      normalizedKernel α₁ α₂ j n ((u : ℂ) + (y : ℂ) * Complex.I)) (Iic r) := by
  apply integrableOn_Iic_of_exp_bound
  · exact (continuousOn_weighted_kernel α₁ α₂ j n k).comp
      (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I)).continuousOn
      (fun u hu => horizontal_mem_kernelDomain hr
        (by intro h; norm_num [h] at hy) hu)
  have h := tendsto_neg_atBot_atTop.eventually
    (uniform_weighted_kernel_left_decay h₁ h₂ hy j n k 1)
  exact h.mono fun u hu => by simpa using hu y hy le_rfl

theorem intervalIntegrable_weighted_kernel_vertical [PositiveArgument] {α₁ α₂ r : ℝ}
    (j : Branch) (n k : ℕ) (hr₀ : 0 < r)
    (hr : r < min (α₁ * n + 1) (α₂ * n + 1)) (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => Complex.I *
      (((n : ℂ) - ((r : ℂ) + (v : ℂ) * Complex.I)) ^ k *
        normalizedKernel α₁ α₂ j n ((r : ℂ) + (v : ℂ) * Complex.I))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_const.mul ((continuousOn_weighted_kernel α₁ α₂ j n k).comp
    (by fun_prop : Continuous (fun v : ℝ => (r : ℂ) + (v : ℂ) * Complex.I)).continuousOn
    (fun v _ => ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa [Complex.mul_re] using hr₀)),
      by simpa [Complex.mul_re] using hr⟩))

/-- Each of the three pieces in the definition of the actual Hankel integral
is absolutely integrable, for every polynomial weight. -/
theorem weighted_hankel_absolutely_convergent [PositiveArgument] {α₁ α₂ r h : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n k : ℕ)
    (hr₀ : 0 < r) (hr : r < min (α₁ * n + 1) (α₂ * n + 1)) (hh : 1 ≤ h) :
    IntegrableOn (fun u : ℝ => ((n : ℂ) - ((u : ℂ) - (h : ℂ) * Complex.I)) ^ k *
      normalizedKernel α₁ α₂ j n ((u : ℂ) - (h : ℂ) * Complex.I)) (Iic r) ∧
    IntervalIntegrable (fun v : ℝ => Complex.I *
      (((n : ℂ) - ((r : ℂ) + (v : ℂ) * Complex.I)) ^ k *
        normalizedKernel α₁ α₂ j n ((r : ℂ) + (v : ℂ) * Complex.I))) volume (-h) h ∧
    IntegrableOn (fun u : ℝ => ((n : ℂ) - ((u : ℂ) + (h : ℂ) * Complex.I)) ^ k *
      normalizedKernel α₁ α₂ j n ((u : ℂ) + (h : ℂ) * Complex.I)) (Iic r) := by
  refine ⟨?_, intervalIntegrable_weighted_kernel_vertical j n k hr₀ hr (-h) h,
    integrableOn_weighted_kernel_horizontal h₁ h₂ j n k hr (by simpa [abs_of_nonneg (by linarith : 0 ≤ h)] using hh)⟩
  simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
    integrableOn_weighted_kernel_horizontal h₁ h₂ j n k hr
      (y := -h) (by simpa [abs_of_nonneg (by linarith : 0 ≤ h)] using hh)

theorem eventually_norm_left_bridge_le [PositiveArgument] {α₁ α₂ H a b : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hH : 1 ≤ H) (j : Branch) (n k : ℕ)
    (hstrip : ∀ v ∈ uIcc a b, 1 ≤ |v| ∧ |v| ≤ H) :
    ∀ᶠ T : ℝ in atTop,
      ‖∫ v in a..b, Complex.I *
        (((n : ℂ) - (-(T : ℂ) + (v : ℂ) * Complex.I)) ^ k *
          normalizedKernel α₁ α₂ j n (-(T : ℂ) + (v : ℂ) * Complex.I))‖ ≤
        Real.exp (-T) * |b - a| := by
  filter_upwards [uniform_weighted_kernel_left_decay h₁ h₂ hH j n k 1] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => by
    simpa only [norm_mul, Complex.norm_I, one_mul, neg_mul, one_mul] using
      hT v (hstrip v (uIoc_subset_uIcc hv)).1 (hstrip v (uIoc_subset_uIcc hv)).2

theorem tendsto_left_bridge_zero [PositiveArgument] {α₁ α₂ H a b : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hH : 1 ≤ H) (j : Branch) (n k : ℕ)
    (hstrip : ∀ v ∈ uIcc a b, 1 ≤ |v| ∧ |v| ≤ H) :
    Tendsto (fun T : ℝ => ∫ v in a..b, Complex.I *
      (((n : ℂ) - (-(T : ℂ) + (v : ℂ) * Complex.I)) ^ k *
        normalizedKernel α₁ α₂ j n (-(T : ℂ) + (v : ℂ) * Complex.I))) atTop (𝓝 0) := by
  exact squeeze_zero_norm' (eventually_norm_left_bridge_le h₁ h₂ hH j n k hstrip)
    (by simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const |b - a|)

end ThisWork.Analytic
