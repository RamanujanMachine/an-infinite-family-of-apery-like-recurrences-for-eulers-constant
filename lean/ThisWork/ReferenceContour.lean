module

public import ThisWork.BoundaryKernel

/-! The reference Hankel contour avoids every integer, including in the
even-rank boundary reflection identity. -/

@[expose] public section
namespace ThisWork

theorem referenceContour_ne_int {x : ℂ}
    (hx : x ∈ Analytic.hankelTrace (1 / 2) 1) (k : ℤ) : x ≠ k := by
  rcases hx with (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨u, hu, rfl⟩
  · intro he
    have hi := congrArg Complex.im he
    norm_num at hi
  · intro he
    have hre := congrArg Complex.re he
    norm_num at hre
    have hcast : ((2 * k : ℤ) : ℝ) = 1 := by push_cast; linarith
    have hk : (2 * k : ℤ) = 1 := by exact_mod_cast hcast
    omega
  · intro he
    have hi := congrArg Complex.im he
    norm_num at hi

theorem referenceContour_sin_ne_zero {x : ℂ}
    (hx : x ∈ Analytic.hankelTrace (1 / 2) 1) :
    Complex.sin ((Real.pi : ℂ) * x) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.mpr
  intro k he
  apply referenceContour_ne_int hx k
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    (Real.pi : ℂ) * x = (k : ℂ) * (Real.pi : ℂ) := he
    _ = (Real.pi : ℂ) * k := mul_comm _ _

end ThisWork
