module
public import ThisWork.Trajectory.GrowingGrowth
public import ThisWork.Trajectory.InitialIndependence
/-! Growth and independence for every two-minimum trajectory `(m,m,m+d)`,
with `m,d ≥ 1`, positive upper-gap parameters, and arbitrary real `z > 0`. -/
@[expose] public section
namespace ThisWork.Trajectory

/-- The two growing branches have coefficient `+2`; the canonical branch has `-2`. -/
def doubleExponentialCoefficient : Branch → ℝ
  | .one | .two => 2
  | .three => -2

/-- All three double-minimum growth estimates, with a logarithmic error. -/
theorem double_normEstimate {m d : ℕ} {A₁ A₂ z : ℝ}
    (hm : 0 < m) (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (j : Branch) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (1 + Real.log (n : ℝ)) ∧
      ‖branchIntegral m d A₁ A₂ z j n‖ = doubleScale m d A₁ A₂ z n *
        Real.exp (doubleExponentialCoefficient j * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E) := by
  cases j with
  | one => exact growing_one_normEstimate hm hd h₁ h₂ hz
  | two => exact growing_two_normEstimate hm hd h₁ h₂ hz
  | three => exact canonical_normEstimate hm hd h₁ h₂ hz

/-- Lemma 8 in the two-minimum regime, including complex linear independence. -/
theorem double_lemma8 {m d : ℕ} {A₁ A₂ z : ℝ}
    (hm : 0 < m) (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    (∀ j : Branch, ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (1 + Real.log (n : ℝ)) ∧
      ‖branchIntegral m d A₁ A₂ z j n‖ = doubleScale m d A₁ A₂ z n *
        Real.exp (doubleExponentialCoefficient j * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E)) ∧
      LinearIndependent ℂ (fun j : Branch => branchIntegral m d A₁ A₂ z j) :=
  ⟨double_normEstimate hm hd h₁ h₂ hz, branchIntegral_linearIndependent m d A₁ A₂ hz⟩

end ThisWork.Trajectory
