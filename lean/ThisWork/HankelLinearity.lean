module

public import ThisWork.Argument
public import ThisWork.HankelScaling

/-! Linearity on the absolutely convergent Hankel integrands. -/

@[expose] public section

namespace ThisWork.Analytic


open Set MeasureTheory

theorem hankelIntegral_congr_on_trace {r h : ℝ} (hh : 0 ≤ h) {f g : ℂ → ℂ}
    (he : ∀ x ∈ hankelTrace r h, f x = g x) :
    hankelIntegral r h f = hankelIntegral r h g := by
  have hlo : (∫ u in Iic r, f ((u : ℂ) - (h : ℂ) * Complex.I)) =
      ∫ u in Iic r, g ((u : ℂ) - (h : ℂ) * Complex.I) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro u hu
    apply he
    exact Or.inl (Or.inl ⟨u, hu, by simp only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg]⟩)
  have hhi : (∫ u in Iic r, f ((u : ℂ) + (h : ℂ) * Complex.I)) =
      ∫ u in Iic r, g ((u : ℂ) + (h : ℂ) * Complex.I) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro u hu
    exact he _ (Or.inr ⟨u, hu, rfl⟩)
  have hv : (∫ v in -h..h, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ v in -h..h, Complex.I * g ((r : ℂ) + (v : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith : -h ≤ h)] at hv
    exact congrArg (Complex.I * ·) (he _ (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
  exact congrArg₂ (· - ·) (congrArg₂ (· + ·) hlo hv) hhi

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

theorem HankelIntegrable.finset_sum {ι : Type*} {r h : ℝ} (s : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ s, HankelIntegrable r h (f i)) :
    HankelIntegrable r h (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HankelIntegrable]
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem hankelIntegral_finset_sum {ι : Type*} {r h : ℝ} (s : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ s, HankelIntegrable r h (f i)) :
    hankelIntegral r h (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, hankelIntegral r h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hankelIntegral]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [hankelIntegral_add (hf i (Finset.mem_insert_self i s))
      (HankelIntegrable.finset_sum s (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end ThisWork.Analytic
