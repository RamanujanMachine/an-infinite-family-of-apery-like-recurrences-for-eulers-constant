module

public import ThisWork.Kernel

/-! Fixed neighborhoods off the logarithmic cut, with explicit positive
separation either in real part or in imaginary part. -/

@[expose] public section
namespace ThisWork

open Set Metric

theorem region_mem_slitPlane {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) {s : ℂ}
    (hs : κ ≤ s.re ∨ η ≤ |s.im|) : s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact hs.elim (fun h => Or.inl (hκ.trans_le h)) (fun h => Or.inr (abs_pos.mp (hη.trans_le h)))

theorem exists_local_slit_region {ζ : ℂ} (hζ : ζ ∈ Complex.slitPlane) :
    ∃ δ > 0, ∃ κ > 0, ∃ η > 0, ∃ M ≥ 0, ∀ s ∈ closedBall ζ δ,
      ‖s‖ ≤ M ∧ (κ ≤ s.re ∨ η ≤ |s.im|) := by
  have hp : ∃ κ > 0, ∃ η > 0, κ < ζ.re ∨ η < |ζ.im| := by
    rcases Complex.mem_slitPlane_iff.mp hζ with hre | him
    · exact ⟨ζ.re / 2, half_pos hre, 1, zero_lt_one, Or.inl (half_lt_self hre)⟩
    · have hi := abs_pos.mpr him
      exact ⟨1, zero_lt_one, |ζ.im| / 2, half_pos hi, Or.inr (half_lt_self hi)⟩
  obtain ⟨κ, hκ, η, hη, hcenter⟩ := hp
  let U : Set ℂ := {s | κ < s.re ∨ η < |s.im|} ∩ ball ζ 1
  have hU : IsOpen U := ((isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_lt continuous_const Complex.continuous_im.abs)).inter isOpen_ball
  have hζU : ζ ∈ U := ⟨hcenter, mem_ball_self zero_lt_one⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU ζ hζU
  refine ⟨δ / 2, half_pos hδ, κ, hκ, η, hη, ‖ζ‖ + 1, by positivity, ?_⟩
  intro s hs
  have hu := hball (closedBall_subset_ball (half_lt_self hδ) hs)
  refine ⟨?_, hu.1.imp le_of_lt le_of_lt⟩
  have hd : ‖s - ζ‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hu.2
  calc
    ‖s‖ = ‖(s - ζ) + ζ‖ := by rw [sub_add_cancel]
    _ ≤ ‖s - ζ‖ + ‖ζ‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end ThisWork
