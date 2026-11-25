module

public import ThisWork.OffCutLocalData
public import ThisWork.FullParabolicContour
public import ThisWork.ParabolicWindowIdentity
public import ThisWork.ParabolicTailBounds
public import ThisWork.ParabolicRemainderBounds

/-! Common indexing and the exact saddle displacement for assembling the
off-cut global integral asymptotics. -/

@[expose] public section
namespace ThisWork.OffCutLocalData

open Set Filter Metric
open scoped Topology OnePoint

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

def index (n : ℕ) : ℕ := n + D.localData.shift + D.family.firstIndex

noncomputable def center (n : ℕ) : ℂ := D.family.saddle (n + D.localData.shift)

noncomputable def translation (n : ℕ) : ℂ := D.center n - parabolicPoint D.a D.b

theorem index_tendsto : Tendsto D.index atTop atTop :=
  (tendsto_add_atTop_nat D.family.firstIndex).comp (tendsto_add_atTop_nat D.localData.shift)

theorem center_tendsto : Tendsto D.center atTop (𝓝 (parabolicPoint D.a D.b)) := by
  change Tendsto (fun n : ℕ => D.family.saddle (n + D.localData.shift)) atTop _
  simpa only [Function.comp_def, D.family.saddle_limit] using
    ((OnePoint.continuous_iff_from_nat D.family.saddle).mp D.family.saddle.continuous).comp
      (tendsto_add_atTop_nat D.localData.shift)

theorem translation_tendsto : Tendsto D.translation atTop (𝓝 0) := by
  change Tendsto (fun n => D.center n - parabolicPoint D.a D.b) atTop _
  simpa only [sub_self] using D.center_tendsto.sub_const (parabolicPoint D.a D.b)

theorem eventually_translation_lt {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ‖D.translation n‖ < d :=
  D.translation_tendsto.norm.eventually_lt_const (by simpa using hd)

@[simp] theorem translation_add_point (n : ℕ) :
    D.translation n + parabolicPoint D.a D.b = D.center n := sub_add_cancel _ _

noncomputable def saddleKernel (b n : ℕ) : ℂ :=
  kernel r b A z j (D.index n) ((largeScale r (D.index n) : ℂ) * D.center n)

theorem eventually_saddleKernel_ne_zero (hr : 0 < r) (hA : ∀ i, 0 < A i) (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, D.saddleKernel b n ≠ 0 := by
  filter_upwards [D.index_tendsto.eventually (eventually_translated_parabola_in_kernelDomain hr hA D.a_pos),
    D.eventually_translation_lt (by have ha := D.a_pos; positivity : 0 < D.a ^ 2 / 8)] with n hn hδ
  have hs := hn (D.translation n) hδ.le D.b
  rw [D.translation_add_point] at hs
  exact kernel_ne_zero b z j (D.index n) hs

theorem angle_relation : (r : ℝ) * (2 * Real.arctan (D.b / D.a)) = -2 * Real.pi * j := by
  have hz : limitingEquation r A z j (parabolicPoint D.a D.b) = 0 := by
    simpa only [parameterEquation, Analytic.sequenceFamily_infty, D.family.saddle_limit] using D.family.equation_zero ∞
  have hi := congrArg Complex.im hz
  simp only [limitingEquation, log_parabolicPoint D.a_pos, Complex.sub_im, Complex.add_im,
    Complex.mul_im, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    Complex.im_sum, Complex.log_im, arg_right_halfplane D.a_pos, Complex.im_ofNat,
    Complex.re_ofNat, mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
    Finset.sum_const_zero, Complex.zero_im] at hi
  linarith

end ThisWork.OffCutLocalData
