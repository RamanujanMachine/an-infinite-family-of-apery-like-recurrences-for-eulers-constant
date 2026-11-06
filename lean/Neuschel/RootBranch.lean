module

public import Neuschel.LocalPhase
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Identification of the outgoing saddle branch with the principal phase root. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

theorem normalizedRoot_eq_cpow (μ : ℕ) {u : ℂ} (hu : u ≠ 0) :
    normalizedRoot μ u = u ^ ((μ : ℂ)⁻¹) := by
  rw [normalizedRoot, Complex.cpow_def_of_ne_zero hu, div_eq_mul_inv]

theorem normalizedRoot_nat_power (μ k : ℕ) {u : ℂ} (hu : u ≠ 0) :
    normalizedRoot μ u ^ (k + 1) = u ^ ((((k : ℝ) + 1) / (μ : ℝ) : ℝ) : ℂ) := by
  rw [normalizedRoot_eq_cpow μ hu, ← Complex.cpow_nat_mul]
  push_cast
  rw [div_eq_mul_inv]

theorem normalizedRoot_pos_scale {μ : ℕ} (hμ : μ ≠ 0) {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : u ≠ 0) :
    normalizedRoot μ ((r : ℂ) ^ μ * u) = (r : ℂ) * normalizedRoot μ u := by
  have hcast : (μ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hμ
  have he : Complex.log ((r : ℂ) ^ μ * u) / (μ : ℂ) =
      (Real.log r : ℂ) + Complex.log u / (μ : ℂ) := by
    rw [← Complex.ofReal_pow, Complex.log_ofReal_mul (pow_pos hr μ) hu, Real.log_pow,
      Complex.ofReal_mul, Complex.ofReal_natCast, add_div, mul_div_cancel_left₀ _ hcast]
  rw [normalizedRoot, he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  rfl

theorem exists_root_unity_isolation {μ : ℕ} (hμ : μ ≠ 0) :
    ∃ r > 0, ∀ u ∈ ball (1 : ℂ) r, u ^ μ = 1 → u = 1 := by
  have hd : ∀ t : ℂ, HasDerivAt (fun u : ℂ => u ^ μ) ((μ : ℂ) * t ^ (μ - 1)) t :=
    hasDerivAt_pow μ
  obtain ⟨r, hr, _, hi⟩ := exists_uniform_injOn (Z := Unit) (p := fun t _ => t ^ μ)
    (G := univ) isOpen_univ (a := 1) (mem_univ _)
    (continuous_fst.pow μ).continuousOn
    (fun _ t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun _ => by simpa only [(hd 1).deriv, one_pow, mul_one] using
      (show (μ : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hμ))
  exact ⟨r, hr, fun u hu he => hi () hu (mem_ball_self hr) (he.trans (one_pow μ).symm)⟩

/-- Two continuous families of roots agreeing at the center agree on one
parameter-uniform neighborhood, provided their common central values are nonzero. -/
theorem eventually_uniform_eq_of_pow_eq {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] [CompactSpace Z] {U : Set X} (hU : IsOpen U) {a : X} (ha : a ∈ U)
    {μ : ℕ} (hμ : μ ≠ 0) {f g : X → Z → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hg : ContinuousOn (Function.uncurry g) (U ×ˢ univ))
    (hc : ∀ z, f a z = g a z) (hne : ∀ z, g a z ≠ 0)
    (hpow : ∀ x ∈ U, ∀ z, f x z ^ μ = g x z ^ μ) :
    ∀ᶠ x in 𝓝 a, ∀ z, f x z = g x z := by
  obtain ⟨r, hr, hroot⟩ := exists_root_unity_isolation hμ
  have hnear : ∀ᶠ x in 𝓝 a, ∀ z ∈ (univ : Set Z),
      f x z / g x z ∈ ball (1 : ℂ) r ∧ g x z ≠ 0 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro z _
    have hcont := And.intro
      (hf.continuousAt (x := (a, z)) ((hU.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩))
      (hg.continuousAt (x := (a, z)) ((hU.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩))
    exact ((hcont.1.div hcont.2 (hne z)).tendsto.eventually
      (show ball (1 : ℂ) r ∈ 𝓝 (f a z / g a z) from by
        simpa only [hc z, div_self (hne z)] using ball_mem_nhds (1 : ℂ) hr)).and
      (hcont.2.eventually_ne (hne z))
  filter_upwards [hnear, hU.mem_nhds ha] with x hx hxU z
  apply (div_eq_one_iff_eq (hx z (mem_univ z)).2).mp
  exact hroot _ (hx z (mem_univ z)).1 (by
    rw [div_pow, hpow x hxU z, div_self (pow_ne_zero μ (hx z (mem_univ z)).2)])

/-- The outgoing leading root selects the principal root uniformly when the
tangent quotient and normalized phase factor are sufficiently near their centers. -/
theorem eventually_uniform_factor_root {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) {b : Z → ℂ} (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0)
    {v : ℂ} (hv : v ≠ 0) (hsector : ∀ z, 0 ≤ (b z * v ^ μ).re) :
    ∀ᶠ x : ℂ × ℂ in 𝓝 (v, 1), ∀ z,
      leadingRoot μ v (b z) * x.1 * normalizedRoot μ x.2 =
        normalizedRoot μ (b z * x.1 ^ μ * x.2) := by
  have hA : Continuous (fun w : (ℂ × ℂ) × Z => b w.2 * w.1.1 ^ μ * w.1.2) :=
    ((hb.comp continuous_snd).mul ((continuous_fst.comp continuous_fst).pow μ)).mul
      (continuous_snd.comp continuous_fst)
  have hnearA : ∀ᶠ x : ℂ × ℂ in 𝓝 (v, 1), ∀ z ∈ (univ : Set Z),
      b z * x.1 ^ μ * x.2 ∈ Complex.slitPlane :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun z _ =>
      (hA.tendsto ((v, 1), z)).eventually (Complex.isOpen_slitPlane.mem_nhds (by
        simpa only [mul_one] using mem_slitPlane_of_re_nonneg (hsector z)
          (mul_ne_zero (hb0 z) (pow_ne_zero μ hv)))))
  obtain ⟨U, hsub, hU, ha⟩ := _root_.mem_nhds_iff.mp
    (hnearA.and ((continuous_snd.tendsto (v, (1 : ℂ))).eventually
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)))
  have hβ : Continuous (fun z => leadingRoot μ v (b z)) :=
    continuous_leadingRoot μ v hb (fun z => mem_slitPlane_of_re_nonneg (hsector z)
      (mul_ne_zero (hb0 z) (pow_ne_zero μ hv)))
  refine eventually_uniform_eq_of_pow_eq hU ha hμ ?_ ?_ ?_ ?_ ?_
  · exact ((hβ.comp continuous_snd).mul (continuous_fst.comp continuous_fst)).continuousOn.mul
      ((continuousOn_normalizedRoot μ).comp
        (continuous_snd.comp continuous_fst).continuousOn (fun w hw => (hsub hw.1).2))
  · exact (continuousOn_normalizedRoot μ).comp hA.continuousOn
      (fun w hw => (hsub hw.1).1 w.2 (mem_univ w.2))
  · exact fun z => by simp [leadingRoot, div_mul_cancel₀ _ hv]
  · exact fun _ => Complex.exp_ne_zero _
  · exact fun x hx z => by
      rw [mul_pow, mul_pow, leadingRoot_pow hμ hv (hb0 z),
        normalizedRoot_pow hμ (Complex.slitPlane_ne_zero (hsub hx).2),
        normalizedRoot_pow hμ (Complex.slitPlane_ne_zero ((hsub hx).1 z (mem_univ z)))]

/-- The tangent-prescribed saddle coordinate is the principal phase root on
one initial contour interval, uniformly in the compact parameter family. -/
theorem eventually_principal_phase_root {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {b : Z → ℂ} (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0)
    {γ : ℝ → ℂ} {v : ℂ} (hγ : HasDerivWithinAt γ v (Ici 0) 0)
    (hγ0 : γ 0 = a) (hv : v ≠ 0) (hsector : ∀ z, 0 ≤ (b z * v ^ μ).re)
    {P h : ℂ → Z → ℂ} (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hc : ∀ z, h a z = 1)
    (hfactor : ∀ t ∈ G, ∀ z, P t z - P a z = b z * (t - a) ^ μ * h t z) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z,
      saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) h (γ s) z =
        normalizedRoot μ (P (γ s) z - P a z) := by
  obtain ⟨ε, hε, hroot⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_uniform_factor_root hμ hb hb0 hv hsector)
  have hHnear : ∀ᶠ t in 𝓝 a, ∀ z ∈ (univ : Set Z), h t z ∈ ball (1 : ℂ) ε ∧ h t z ≠ 0 :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun z _ =>
      let ht := hh.continuousAt (x := (a, z)) ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)
      (ht.tendsto.eventually (show ball (1 : ℂ) ε ∈ 𝓝 (Function.uncurry h (a, z)) from by
        simpa only [Function.uncurry_apply_pair, hc z] using ball_mem_nhds (1 : ℂ) hε)).and
        (ht.eventually_ne (by simpa only [Function.uncurry_apply_pair, hc z] using (one_ne_zero : (1 : ℂ) ≠ 0))))
  have hD := tendsto_contour_tangent hγ hγ0
  have hend := tendsto_contour_endpoint hγ hγ0
  filter_upwards [hD.eventually (ball_mem_nhds v hε), hD.eventually (isOpen_ne.mem_nhds hv),
    hend.eventually hHnear, hend.eventually (hG.mem_nhds ha), self_mem_nhdsWithin]
    with s hsD hsD0 hHs hsG hs0 z
  have hsel := hroot ((γ s - a) / (s : ℂ), h (γ s) z)
    (by simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using
      And.intro hsD (hHs z (mem_univ z)).1) z
  have hdiff : γ s - a = (s : ℂ) * ((γ s - a) / (s : ℂ)) :=
    (mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hs0))).symm
  have hpow : (γ s - a) ^ μ = (s : ℂ) ^ μ * ((γ s - a) / (s : ℂ)) ^ μ :=
    (congrArg (fun u : ℂ => u ^ μ) hdiff).trans (mul_pow _ _ μ)
  have hphase : P (γ s) z - P a z =
      (s : ℂ) ^ μ * (b z * ((γ s - a) / (s : ℂ)) ^ μ * h (γ s) z) :=
    (hfactor (γ s) hsG z).trans (by simp only [hpow, mul_left_comm, mul_assoc])
  rw [hphase, normalizedRoot_pos_scale hμ hs0
    (mul_ne_zero (mul_ne_zero (hb0 z) (pow_ne_zero μ hsD0)) (hHs z (mem_univ z)).2), ← hsel]
  dsimp only [saddleCoordinate]
  linear_combination leadingRoot μ v (b z) * normalizedRoot μ (h (γ s) z) * hdiff

/-- Phase positivity supplies the sector condition in the principal-branch
identity; no additional branch hypothesis is required of the contour. -/
theorem eventually_principal_phase_root_of_positive {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {b : Z → ℂ} (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0)
    {γ : ℝ → ℂ} {v : ℂ} (hγ : HasDerivWithinAt γ v (Ici 0) 0)
    (hγ0 : γ 0 = a) (hv : v ≠ 0)
    {P h : ℂ → Z → ℂ} (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hc : ∀ z, h a z = 1)
    (hfactor : ∀ t ∈ G, ∀ z, P t z - P a z = b z * (t - a) ^ μ * h t z)
    (hpos : ∀ z, ∀ᶠ s : ℝ in 𝓝[>] 0, 0 ≤ (P (γ s) z - P a z).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z,
      saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) h (γ s) z =
        normalizedRoot μ (P (γ s) z - P a z) := by
  have hnear := (tendsto_contour_endpoint hγ hγ0).eventually (hG.mem_nhds ha)
  exact eventually_principal_phase_root hμ hG ha hb hb0 hγ hγ0 hv
    (fun z => phase_sector_of_contour (p := fun t => P t z) (h := fun t => h t z) μ hγ hγ0
      ((hh.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).comp
        (continuousAt_id.prodMk continuousAt_const)) (hc z)
      (hnear.mono (fun s hs => hfactor (γ s) hs z)) (hpos z)) hh hc hfactor

end Neuschel
