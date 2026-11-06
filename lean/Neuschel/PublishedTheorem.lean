module

public import Neuschel.PaperCorrespondence

/-! A source-shaped specialization of the parameterized uniform Laplace theorem. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

/-- The hypotheses and conclusion of Neuschel's Theorem 3.1, with the path
supplied in a fixed parameterization on `[0,1)`. `ℓ` is the paper's positive
amplitude exponent; `N` is its integer base parameter. Connectedness, simplicity
and the nonzero amplitude leader are retained here to match the source. -/
theorem neuschel_theorem_3_1_published {S G : Set ℂ} (hS : IsCompact S)
    (hSne : S.Nonempty) (hG : IsOpen G) (_hconnected : IsPreconnected G)
    {a : ℂ} (ha : a ∈ G) {μ ℓ N : ℕ} (hμ : 0 < μ) (hℓ : 0 < ℓ) (_hN : 0 < N)
    {P q : ℂ → S → ℂ}
    (hP : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {b c : ℕ → S → ℂ}
    (hsP : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => b j z * (t - a) ^ (μ + j)) (P t z - P a z))
    (hb : ∀ z, b 0 z ≠ 0)
    (hsq : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => c j z * (t - a) ^ (j + ℓ - 1)) (q t z))
    (_hc : ∀ z, c 0 z ≠ 0) {γ velocity : ℝ → ℂ} (hγ0 : γ 0 = a)
    (hγ : ContinuousOn γ (Ico 0 1)) (hγG : MapsTo γ (Ico 0 1) G)
    (_hsimple : InjOn γ (Ico 0 1))
    {corners : Set ℝ} (hcorners : corners.Countable)
    (hregular : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ corners → HasDerivAt γ (velocity s) s)
    {L : ℝ} (hL : L ∈ Ioo (0 : ℝ) 1) (hv : ContinuousOn velocity (Icc 0 L))
    (hdγ : ∀ s ∈ Ioo 0 L, HasDerivAt γ (velocity s) s) (hv0 : velocity 0 ≠ 0)
    (hphase : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ ε > 0, ∀ z, ε ≤ (P (γ s) z - P a z).re)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ (P (γ s) z - P a z).re)
    (habsolute : ∀ n : ℕ, N ≤ n → ∀ z, IntegrableOn
      (fun s => Complex.exp (-(n : ℂ) * P (γ s) z) * q (γ s) z * velocity s) (Ioo 0 1))
    {B : ℝ} (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1,
      Real.exp (-(N : ℝ) * (P (γ s) z).re) * ‖q (γ s) z‖ * ‖velocity s‖) ≤ B) :
    Nonempty (UniformLaplaceExpansion μ (ℓ - 1) P q a (velocity 0) b c γ velocity (N : ℝ)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : Nonempty S := hSne.to_subtype
  have hγinitial : ContinuousOn γ (Icc 0 L) :=
    hγ.mono (fun s hs => ⟨hs.1, hs.2.trans_lt hL.2⟩)
  have htangent := endpoint_tangent_of_smooth_piece hL.1 hγinitial hv hdγ
  have hsamp : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => c j z * (t - a) ^ ((ℓ - 1) + j)) (q t z) := by
    have he : ∀ j, (ℓ - 1) + j = j + ℓ - 1 := fun j => by omega
    simpa only [he] using hsq
  have hbase : ∀ z, IntegrableOn
      (fun s => Real.exp (-(N : ℝ) * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) (Ioo 0 1) := by
    intro z
    simpa [IntegrableOn, Complex.norm_exp, Complex.mul_re, mul_comm, mul_left_comm, mul_assoc] using
      (habsolute N le_rfl z).norm
  refine neuschel_theorem_3_1_countable hG ha (Nat.ne_of_gt hμ) (ℓ - 1) hP hdP hq hdq
    hsP hb hsamp hγ0 htangent hv0 hγ hγG hcorners hregular hL.1 hv hdγ ?_ hend
    (le_max_right B 0) hbase ?_
  · intro s hs z
    obtain ⟨ε, hε, hbound⟩ := hphase s hs
    exact hε.trans_le (hbound z)
  · intro z
    simpa only [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hmass z).trans (le_max_left B 0)

end Neuschel
