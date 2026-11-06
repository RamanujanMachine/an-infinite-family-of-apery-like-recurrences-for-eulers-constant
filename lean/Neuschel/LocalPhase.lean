module

public import Neuschel.PhaseExpansion
public import Neuschel.ContourDirection

/-! Local phase straightening from the original convergent phase expansion. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

/-- The local coordinate step in Theorem 3.1(i–ii), from joint continuity,
holomorphy, the convergent phase expansion, and positivity along a regular
outgoing contour. All inverse domains are uniform in the compact parameter.
No regularity of the coefficients or normalized factor is assumed. -/
theorem exists_local_phase_from_expansion {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {μ : ℕ} (hμ : μ ≠ 0) {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) {b : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun n => b n z * (t - a) ^ (μ + n)) (p t z - p a z))
    (hb0 : ∀ z, b 0 z ≠ 0) {γ : ℝ → ℂ} {v : ℂ}
    (hγ : HasDerivWithinAt γ v (Ici 0) 0) (hγ0 : γ 0 = a) (hv : v ≠ 0)
    (hpos : ∀ z, ∀ᶠ s : ℝ in 𝓝[>] 0, 0 ≤ (p (γ s) z - p a z).re) :
    ∃ h : ℂ → Z → ℂ, ContinuousOn (Function.uncurry h) (G ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun t => h t z) G) ∧ (∀ z, h a z = 1) ∧
      ∃ e : LocalInverseFamily
          (saddleCoordinate μ a (fun z => leadingRoot μ v (b 0 z)) h) a G,
        (∀ t ∈ ball a e.sourceRadius, ∀ z,
          saddleCoordinate μ a (fun z => leadingRoot μ v (b 0 z)) h t z ^ μ = p t z - p a z) ∧
        ∀ w ∈ ball 0 e.targetRadius, ∀ z, p (e.inverse w z) z - p a z = w ^ μ := by
  obtain ⟨hb, h, hh, hdh, hc, hf⟩ := exists_phase_factor_from_expansion μ hG ha hp hd hs hb0
  exact ⟨h, hh, hdh, hc,
    exists_phase_straightening_of_contour hG ha hμ hγ hγ0 hv hb hb0 hh hdh hc hf hpos⟩

end Neuschel
