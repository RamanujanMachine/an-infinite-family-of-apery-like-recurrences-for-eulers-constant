module

public import ThisWork.Trajectory.PolynomialContours

/-! Equality on the contour trace suffices for Hankel integrability and integration. -/

@[expose] public section

namespace ThisWork.Analytic

open Set MeasureTheory

theorem lower_mem_hankelTrace {r h u : ℝ} (hu : u ≤ r) :
    (u : ℂ) - (h : ℂ) * Complex.I ∈ hankelTrace r h :=
  Or.inl (Or.inl ⟨u, hu, by push_cast; ring⟩)

theorem upper_mem_hankelTrace {r h u : ℝ} (hu : u ≤ r) :
    (u : ℂ) + (h : ℂ) * Complex.I ∈ hankelTrace r h :=
  Or.inr ⟨u, hu, rfl⟩

theorem vertical_mem_hankelTrace {r h v : ℝ} (hv : v ∈ Icc (-h) h) :
    (r : ℂ) + (v : ℂ) * Complex.I ∈ hankelTrace r h :=
  Or.inl (Or.inr ⟨v, hv, rfl⟩)

theorem HankelIntegrable.congr {r h : ℝ} {f g : ℂ → ℂ} (hf : HankelIntegrable r h f)
    (hh : 0 ≤ h) (he : EqOn f g (hankelTrace r h)) : HankelIntegrable r h g := by
  refine ⟨hf.1.congr_fun (fun u hu => he (lower_mem_hankelTrace hu)) measurableSet_Iic,
    ?_, hf.2.2.congr_fun (fun u hu => he (upper_mem_hankelTrace hu)) measurableSet_Iic⟩
  exact (intervalIntegrable_congr (fun v hv => congrArg (Complex.I * ·)
    (he (vertical_mem_hankelTrace (by
      simpa only [uIcc_of_le (show -h ≤ h by linarith)] using uIoc_subset_uIcc hv))))).mp hf.2.1

theorem hankelIntegral_congr {r h : ℝ} {f g : ℂ → ℂ} (hh : 0 ≤ h)
    (he : EqOn f g (hankelTrace r h)) : hankelIntegral r h f = hankelIntegral r h g := by
  unfold hankelIntegral
  rw [setIntegral_congr_fun measurableSet_Iic (fun u hu => he (lower_mem_hankelTrace hu)),
    intervalIntegral.integral_congr (fun v hv => congrArg (Complex.I * ·)
      (he (vertical_mem_hankelTrace (by
        simpa only [uIcc_of_le (show -h ≤ h by linarith)] using hv)))),
    setIntegral_congr_fun measurableSet_Iic (fun u hu => he (upper_mem_hankelTrace hu))]

end ThisWork.Analytic
