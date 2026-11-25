module

public import ThisWork.MellinBarnesAsymptotics

/-! The equal-lower-slope trajectory family `𝒯ᵣ*`.
A trajectory has signed integer upper and lower coordinates. Membership
means that every upper coordinate is nonpositive and all lower coordinates
are one common positive integer `b`. The analytic upper gaps are `b - aᵢ`.
This is the arbitrary-rank, arbitrary-equal-lower-slope version of the
paper's trajectory family; no recurrence or CMF claim is made here. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

/-- Integer coordinates `(a₁,…,aᵣ₋₁; b₁,…,bᵣ)` of a trajectory. -/
structure Trajectory (r : ℕ) where
  a : Fin (r - 1) → ℤ
  b : Fin r → ℤ

/-- `𝒯ᵣ*`: nonpositive upper coordinates and equal positive lower coordinates. -/
def TStar (r : ℕ) : Set (Trajectory r) :=
  {t | (∀ i, t.a i ≤ 0) ∧ ∃ b : ℕ, 0 < b ∧ ∀ i, t.b i = (b : ℤ)}

/-- A trajectory in `𝒯ᵣ*` satisfies the analytic theorem with its actual
common lower slope `b` and upper gaps `Aᵢ = b - aᵢ`. -/
theorem TStar.mellinBarnes_asymptotics {r : ℕ} (hr : 3 ≤ r)
    {t : Trajectory r} (ht : t ∈ TStar r) {z : ℝ} (hz : 0 < z) :
    ∃ b : ℕ, 0 < b ∧ (∀ i, t.b i = (b : ℤ)) ∧
      (∀ k : Fin r, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
        |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
        ‖branchIntegral r b (fun i => (b : ℝ) - (t.a i : ℝ)) z (branchLabel r k) n‖ =
          commonScale r b (fun i => (b : ℝ) - (t.a i : ℝ)) z n *
            Real.exp (-(r : ℝ) * saddleScale r (fun i => (b : ℝ) - (t.a i : ℝ)) z *
              (Phase.rho (branchAngle r k)).re * largeScale r n + E)) ∧
      LinearIndependent ℂ (fun k : Fin r =>
        branchIntegral r b (fun i => (b : ℝ) - (t.a i : ℝ)) z (branchLabel r k)) ∧
      StronglyRecessive r b (fun i => (b : ℝ) - (t.a i : ℝ)) z := by
  obtain ⟨ha, b, hb, hlower⟩ := ht
  have hgap (i : Fin (r - 1)) : 0 < (b : ℝ) - (t.a i : ℝ) := by
    have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    have haR : (t.a i : ℝ) ≤ 0 := by exact_mod_cast ha i
    linarith
  exact ⟨b, hb, hlower, equalSlope_mellinBarnes_asymptotics hr hgap hz b⟩

end ThisWork
