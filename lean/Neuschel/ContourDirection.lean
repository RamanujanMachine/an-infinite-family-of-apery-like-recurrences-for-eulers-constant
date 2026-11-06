module

public import Neuschel.SaddleCoordinate

/-! The phase sector forced by the outgoing tangent of a contour. -/

public section

namespace Neuschel

open Set Filter
open scoped Topology

/-- Only the right derivative of the contour is needed at its initial endpoint. -/
theorem tendsto_contour_tangent {γ : ℝ → ℂ} {a v : ℂ}
    (hγ : HasDerivWithinAt γ v (Ici 0) 0) (hγ0 : γ 0 = a) :
    Tendsto (fun s : ℝ => (γ s - a) / (s : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  have hs : Tendsto (fun s : ℝ => (s - 0)⁻¹ • (γ s - γ 0)) (𝓝[>] 0) (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 from lt_irrefl 0)).mp
      (hγ.mono Ioi_subset_Ici_self)
  simpa [hγ0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs

theorem tendsto_contour_endpoint {γ : ℝ → ℂ} {a v : ℂ}
    (hγ : HasDerivWithinAt γ v (Ici 0) 0) (hγ0 : γ 0 = a) :
    Tendsto γ (𝓝[>] 0) (𝓝 a) :=
  (hγ0 ▸ hγ.continuousWithinAt.tendsto).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem scaled_phase_eq (μ : ℕ) (s : ℝ) (b x u : ℂ) :
    (s ^ μ)⁻¹ • (b * x ^ μ * u) = b * (x / (s : ℂ)) ^ μ * u := by
  simp [div_eq_mul_inv, mul_pow, mul_comm, mul_left_comm, mul_assoc]

/-- Positivity of the phase immediately after the initial endpoint forces the
rotated leading coefficient into the closed right half-plane. -/
theorem phase_sector_of_contour {γ : ℝ → ℂ} {a v b : ℂ} {h p : ℂ → ℂ} (μ : ℕ)
    (hγ : HasDerivWithinAt γ v (Ici 0) 0) (hγ0 : γ 0 = a)
    (hh : ContinuousAt h a) (hc : h a = 1)
    (hfactor : ∀ᶠ s : ℝ in 𝓝[>] 0, p (γ s) - p a = b * (γ s - a) ^ μ * h (γ s))
    (hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 ≤ (p (γ s) - p a).re) :
    0 ≤ (b * v ^ μ).re := by
  have hlim : Tendsto (fun s : ℝ => b * ((γ s - a) / (s : ℂ)) ^ μ * h (γ s))
      (𝓝[>] 0) (𝓝 (b * v ^ μ)) := by
    simpa [hγ0, hc] using
      ((tendsto_contour_tangent hγ hγ0).pow μ).const_mul b |>.mul
        (hh.tendsto.comp (tendsto_contour_endpoint hγ hγ0))
  apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hlim)
  filter_upwards [hfactor, hpos, self_mem_nhdsWithin] with s hf hp hs
  change 0 ≤ (b * ((γ s - a) / (s : ℂ)) ^ μ * h (γ s)).re
  rw [← scaled_phase_eq, ← hf, Complex.smul_re]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hs) μ)) hp

/-- The contour positivity supplies the branch-sector hypothesis needed for a
uniform monomial coordinate. The normalized holomorphic factor is still an input. -/
theorem exists_phase_straightening_of_contour {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {μ : ℕ} (hμ : μ ≠ 0) {γ : ℝ → ℂ} {v : ℂ}
    (hγ : HasDerivWithinAt γ v (Ici 0) 0) (hγ0 : γ 0 = a) (hv : v ≠ 0)
    {b : Z → ℂ} {h p : ℂ → Z → ℂ} (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0)
    (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => h t z) G) (hc : ∀ z, h a z = 1)
    (hfactor : ∀ t ∈ G, ∀ z, p t z - p a z = b z * (t - a) ^ μ * h t z)
    (hpos : ∀ z, ∀ᶠ s : ℝ in 𝓝[>] 0, 0 ≤ (p (γ s) z - p a z).re) :
    ∃ e : LocalInverseFamily (saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) h) a G,
      (∀ t ∈ Metric.ball a e.sourceRadius, ∀ z,
        saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) h t z ^ μ = p t z - p a z) ∧
      ∀ w ∈ Metric.ball 0 e.targetRadius, ∀ z, p (e.inverse w z) z - p a z = w ^ μ := by
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 0, γ s ∈ G :=
    (tendsto_contour_endpoint hγ hγ0).eventually (hG.mem_nhds ha)
  exact exists_phase_straightening_in_direction hG ha hμ hv hb hb0
    (fun z => phase_sector_of_contour (p := fun t => p t z) (h := fun t => h t z) μ hγ hγ0
      ((hh.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).comp
        (continuousAt_id.prodMk continuousAt_const))
      (hc z) (hnear.mono (fun s hs => hfactor (γ s) hs z)) (hpos z))
    hh hd hc hfactor

end Neuschel
