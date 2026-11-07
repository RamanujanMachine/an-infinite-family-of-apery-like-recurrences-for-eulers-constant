module

public import ThisWork.Argument
public import ThisWork.HankelScaling

/-! Linearity on the absolutely convergent Hankel integrands. -/

@[expose] public section

namespace ThisWork.Analytic


open Set MeasureTheory

/-- Absolute convergence of each of the three defining contour pieces. -/
def HankelIntegrable (r h : ℝ) (f : ℂ → ℂ) : Prop :=
  IntegrableOn (fun u : ℝ => f ((u : ℂ) - (h : ℂ) * Complex.I)) (Iic r) ∧
  IntervalIntegrable (fun v : ℝ => Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) volume (-h) h ∧
  IntegrableOn (fun u : ℝ => f ((u : ℂ) + (h : ℂ) * Complex.I)) (Iic r)

theorem HankelIntegrable.const_mul {r h : ℝ} {f : ℂ → ℂ} (hf : HankelIntegrable r h f) (c : ℂ) :
    HankelIntegrable r h (fun x => c * f x) := by
  refine ⟨hf.1.const_mul c, ?_, hf.2.2.const_mul c⟩
  simpa only [mul_left_comm Complex.I c] using hf.2.1.const_mul c

theorem HankelIntegrable.add {r h : ℝ} {f g : ℂ → ℂ}
    (hf : HankelIntegrable r h f) (hg : HankelIntegrable r h g) :
    HankelIntegrable r h (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_, hf.2.2.add hg.2.2⟩
  simpa only [mul_add] using hf.2.1.add hg.2.1

theorem HankelIntegrable.sub {r h : ℝ} {f g : ℂ → ℂ}
    (hf : HankelIntegrable r h f) (hg : HankelIntegrable r h g) :
    HankelIntegrable r h (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ?_, hf.2.2.sub hg.2.2⟩
  simpa only [mul_sub] using hf.2.1.sub hg.2.1

theorem hankelIntegral_const_mul (r h : ℝ) (f : ℂ → ℂ) (c : ℂ) :
    hankelIntegral r h (fun x => c * f x) = c * hankelIntegral r h f := by
  simp only [hankelIntegral, mul_left_comm Complex.I c, integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

theorem hankelIntegral_add {r h : ℝ} {f g : ℂ → ℂ}
    (hf : HankelIntegrable r h f) (hg : HankelIntegrable r h g) :
    hankelIntegral r h (fun x => f x + g x) = hankelIntegral r h f + hankelIntegral r h g := by
  simp only [hankelIntegral, mul_add]
  rw [integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    integral_add hf.2.2 hg.2.2]
  ring

theorem hankelIntegral_sub {r h : ℝ} {f g : ℂ → ℂ}
    (hf : HankelIntegrable r h f) (hg : HankelIntegrable r h g) :
    hankelIntegral r h (fun x => f x - g x) = hankelIntegral r h f - hankelIntegral r h g := by
  simp only [hankelIntegral, mul_sub]
  rw [integral_sub hf.1 hg.1, intervalIntegral.integral_sub hf.2.1 hg.2.1,
    integral_sub hf.2.2 hg.2.2]
  ring

end ThisWork.Analytic
