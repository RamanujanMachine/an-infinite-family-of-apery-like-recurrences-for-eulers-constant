module

public import ThisWork.HigherRank.CanonicalRecessiveness

/-! Equal-slope Mellin–Barnes asymptotics in arbitrary rank, including quantitative strong recessiveness.
The branch labels are the balanced integer Fourier labels `floor(r/2)-k`.
Only nonrecessive branches occur in the combinations below. -/

@[expose] public section
namespace ThisWork.HigherRank

open Filter
open scoped Topology

abbrev NonrecessiveBranch (r : ℕ) := {i : Fin r // branchLabel r i ≠ 0}

noncomputable def nonrecessiveCombination (r b : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (a : NonrecessiveBranch r → ℂ) (n : ℕ) : Fin r → ℂ :=
  ∑ i, a i • branchIntegral r b A z (branchLabel r i.val) n

def StronglyRecessive (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) : Prop :=
  ∀ a : NonrecessiveBranch r → ℂ, a ≠ 0 →
    (∀ᶠ n : ℕ in atTop, nonrecessiveCombination r b A z a n ≠ 0) ∧
    ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N *
      (‖branchIntegral r b A z 0 n‖ / ‖nonrecessiveCombination r b A z a n‖)) atTop (𝓝 0)

theorem branch_stronglyRecessive {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (b : ℕ) :
    StronglyRecessive r b A z := by
  classical
  intro a ha
  let auxB : Fin r → ℂ := fun i => if h : branchLabel r i ≠ 0 then a ⟨i, h⟩ else 0
  have hb : auxB ≠ 0 := by
    intro he
    apply ha
    funext i
    have h := congrFun he i.val
    simpa only [auxB, dite_eq_left i.property, Pi.zero_apply] using h
  have hs : ∀ i, branchLabel r i = 0 → auxB i = 0 := by
    intro i hi
    simp only [auxB, hi, ne_eq, not_true_eq_false, dite_eq_right, not_false_eq_true]
  have hsum (n : ℕ) : (∑ i, auxB i • branchIntegral r b A z (branchLabel r i) n) =
      nonrecessiveCombination r b A z a n := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin r => branchLabel r i ≠ 0)
      (fun i => auxB i • branchIntegral r b A z (branchLabel r i) n)
    have h₁ : (∑ i : NonrecessiveBranch r,
        auxB i.val • branchIntegral r b A z (branchLabel r i.val) n) =
          nonrecessiveCombination r b A z a n := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [auxB]
      rw [dite_eq_left i.property]
    have h₂ : (∑ i : {i : Fin r // ¬branchLabel r i ≠ 0},
        auxB i.val • branchIntegral r b A z (branchLabel r i.val) n) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      dsimp only [auxB]
      rw [dite_eq_right i.property, zero_smul]
    rw [h₁, h₂, add_zero] at h
    exact h.symm
  simpa only [hsum] using branch_combination_stronglyRecessive hr hA hz b auxB hb hs

theorem branch_normEstimate {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (k : Fin r) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
      ‖branchIntegral r b A z (branchLabel r k) n‖ = commonScale r b A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re * largeScale r n + E) := by
  obtain ⟨C, hC, hb⟩ := branch_hasLogNormGrowth hr hA hz b k
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  let E := Real.log ‖branchIntegral r b A z (branchLabel r k) n‖ - Real.log (commonScale r b A z n) -
    (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re) * largeScale r n
  refine ⟨E, ?_, ?_⟩
  · simpa only [largeScale_mul_smallParameter r hn0] using hn.2
  · have hS := commonScale_pos hA hz b n
    have hexp : commonScale r b A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re * largeScale r n + E) =
          Real.exp (Real.log (commonScale r b A z n) +
            (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re * largeScale r n + E)) := by
      rw [Real.exp_add (Real.log (commonScale r b A z n))
        (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re * largeScale r n + E), Real.exp_log hS]
    rw [show Real.log (commonScale r b A z n) +
      (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re * largeScale r n + E) =
        Real.log ‖branchIntegral r b A z (branchLabel r k) n‖ by dsimp only [E]; ring, Real.exp_log hn.1] at hexp
    exact hexp.symm

/-- Growth, sequence independence, and strong recessiveness of the original
Mellin–Barnes vector integrals, for every rank at least three. -/
theorem equalSlope_mellinBarnes_asymptotics {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (b : ℕ) :
    (∀ k : Fin r, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
      ‖branchIntegral r b A z (branchLabel r k) n‖ = commonScale r b A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re * largeScale r n + E)) ∧
    LinearIndependent ℂ (fun k : Fin r => branchIntegral r b A z (branchLabel r k)) ∧
    StronglyRecessive r b A z :=
  ⟨branch_normEstimate hr hA hz b, branch_linearIndependent hr hA hz b,
    branch_stronglyRecessive hr hA hz b⟩

end ThisWork.HigherRank
