module

public import Neuschel.LocalInverse
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Local roots and saddle coordinates

The normalized root uses the logarithm near one. The root of the leading
coefficient is a separate parameter, so this construction does not impose
the principal branch on that coefficient.
-/

@[expose] public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

noncomputable def normalizedRoot (μ : ℕ) (u : ℂ) : ℂ :=
  Complex.exp (Complex.log u / (μ : ℂ))

@[simp] theorem normalizedRoot_one (μ : ℕ) : normalizedRoot μ 1 = 1 := by
  simp [normalizedRoot]

theorem normalizedRoot_pow {μ : ℕ} (hμ : μ ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    normalizedRoot μ u ^ μ = u := by
  rw [normalizedRoot, ← Complex.exp_nat_mul]
  rw [mul_comm, div_mul_cancel₀ _ (show (μ : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hμ)]
  exact Complex.exp_log hu

theorem differentiableOn_normalizedRoot (μ : ℕ) :
    DifferentiableOn ℂ (normalizedRoot μ) Complex.slitPlane :=
  (DifferentiableOn.clog differentiableOn_id (fun _ hu => hu)).div_const (μ : ℂ) |>.cexp

theorem continuousOn_normalizedRoot (μ : ℕ) :
    ContinuousOn (normalizedRoot μ) Complex.slitPlane :=
  (differentiableOn_normalizedRoot μ).continuousOn

variable {Z : Type*}

/-- The leading root `β` is supplied independently of the principal logarithm. -/
noncomputable def saddleCoordinate (μ : ℕ) (a : ℂ) (β : Z → ℂ)
    (h : ℂ → Z → ℂ) (t : ℂ) (z : Z) : ℂ :=
  β z * ((t - a) * normalizedRoot μ (h t z))

@[simp] theorem saddleCoordinate_center (μ : ℕ) (a : ℂ) (β : Z → ℂ)
    (h : ℂ → Z → ℂ) (z : Z) : saddleCoordinate μ a β h a z = 0 := by
  simp [saddleCoordinate]

theorem saddleCoordinate_pow {μ : ℕ} (hμ : μ ≠ 0) (a : ℂ) (β : Z → ℂ)
    (h : ℂ → Z → ℂ) {t : ℂ} {z : Z} (hu : h t z ≠ 0) :
    saddleCoordinate μ a β h t z ^ μ = β z ^ μ * (t - a) ^ μ * h t z := by
  simp only [saddleCoordinate, mul_pow, normalizedRoot_pow hμ hu, mul_assoc]

/-- Root selected after rotating the outgoing direction to the positive axis. -/
noncomputable def leadingRoot (μ : ℕ) (v b : ℂ) : ℂ :=
  normalizedRoot μ (b * v ^ μ) / v

theorem leadingRoot_pow {μ : ℕ} (hμ : μ ≠ 0) {v b : ℂ} (hv : v ≠ 0) (hb : b ≠ 0) :
    leadingRoot μ v b ^ μ = b := by
  rw [leadingRoot, div_pow, normalizedRoot_pow hμ (mul_ne_zero hb (pow_ne_zero μ hv)),
    mul_div_cancel_right₀ _ (pow_ne_zero μ hv)]

theorem leadingRoot_ne_zero (μ : ℕ) {v : ℂ} (hv : v ≠ 0) (b : ℂ) :
    leadingRoot μ v b ≠ 0 :=
  div_ne_zero (Complex.exp_ne_zero _) hv

theorem mem_slitPlane_of_re_nonneg {u : ℂ} (hre : 0 ≤ u.re) (hu : u ≠ 0) :
    u ∈ Complex.slitPlane :=
  (lt_or_eq_of_le hre).elim Or.inl
    (fun h => Or.inr (fun hi => hu (Complex.ext h.symm hi)))

variable [TopologicalSpace Z]

theorem continuous_leadingRoot (μ : ℕ) (v : ℂ) {b : Z → ℂ}
    (hb : Continuous b) (hslit : ∀ z, b z * v ^ μ ∈ Complex.slitPlane) :
    Continuous (fun z => leadingRoot μ v (b z)) :=
  ((continuousOn_normalizedRoot μ).comp_continuous (hb.mul continuous_const) hslit).div_const v

theorem continuousOn_saddleCoordinate (μ : ℕ) (a : ℂ) {G : Set ℂ}
    {β : Z → ℂ} {h : ℂ → Z → ℂ} (hβ : Continuous β)
    (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hslit : ∀ t ∈ G, ∀ z, h t z ∈ Complex.slitPlane) :
    ContinuousOn (Function.uncurry (saddleCoordinate μ a β h)) (G ×ˢ univ) :=
  (hβ.comp continuous_snd).continuousOn.mul
    ((continuous_fst.sub continuous_const).continuousOn.mul
      ((continuousOn_normalizedRoot μ).comp hh (fun w hw => hslit w.1 hw.1 w.2)))

omit [TopologicalSpace Z] in
theorem differentiableOn_saddleCoordinate (μ : ℕ) (a : ℂ) {G : Set ℂ}
    (β : Z → ℂ) {h : ℂ → Z → ℂ}
    (hd : ∀ z, DifferentiableOn ℂ (fun t => h t z) G)
    (hslit : ∀ t ∈ G, ∀ z, h t z ∈ Complex.slitPlane) :
    ∀ z, DifferentiableOn ℂ (fun t => saddleCoordinate μ a β h t z) G :=
  fun z => ((differentiableOn_id.sub_const a).mul
    ((differentiableOn_normalizedRoot μ).comp (hd z) (fun t ht => hslit t ht z))).const_mul (β z)

omit [TopologicalSpace Z] in
theorem hasDerivAt_saddleCoordinate_center (μ : ℕ) (a : ℂ) (β : Z → ℂ)
    {h : ℂ → Z → ℂ} {z : Z} (hd : DifferentiableAt ℂ (fun t => h t z) a)
    (hc : h a z = 1) :
    HasDerivAt (fun t => saddleCoordinate μ a β h t z) (β z) a := by
  have hr : DifferentiableAt ℂ (fun t => normalizedRoot μ (h t z)) a :=
    ((differentiableOn_normalizedRoot μ).differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds (hc ▸ Complex.one_mem_slitPlane))).comp a hd
  simpa [saddleCoordinate, hc] using
    (((hasDerivAt_id a).sub_const a).mul hr.hasDerivAt).const_mul (β z)

/-- A compact normalized holomorphic family admits saddle coordinates on one
common neighborhood. The selected leading roots must be continuous and nonzero. -/
theorem exists_saddleCoordinate_inverse [CompactSpace Z] {G : Set ℂ}
    (hG : IsOpen G) {a : ℂ} (ha : a ∈ G) (μ : ℕ)
    {β : Z → ℂ} {h : ℂ → Z → ℂ} (hβ : Continuous β) (hβ0 : ∀ z, β z ≠ 0)
    (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => h t z) G) (hc : ∀ z, h a z = 1) :
    ∃ e : LocalInverseFamily (saddleCoordinate μ a β h) a G,
      ∀ t ∈ ball a e.sourceRadius, ∀ z, h t z ∈ Complex.slitPlane := by
  obtain ⟨r, hr, hrG, hslit⟩ := exists_uniform_mapsTo_nhds hG ha hh
    Complex.isOpen_slitPlane (fun z => (hc z) ▸ Complex.one_mem_slitPlane)
  obtain ⟨e⟩ := exists_localInverseFamily isOpen_ball (mem_ball_self hr)
    (continuousOn_saddleCoordinate μ a hβ (hh.mono (Set.prod_mono hrG Subset.rfl))
      (fun t ht z => hslit z ht))
    (differentiableOn_saddleCoordinate μ a β (fun z => (hd z).mono hrG)
      (fun t ht z => hslit z ht))
    (saddleCoordinate_center μ a β h)
    (fun z => (hasDerivAt_saddleCoordinate_center μ a β
      ((hd z).differentiableAt (hG.mem_nhds ha)) (hc z)).deriv ▸ hβ0 z)
  exact ⟨{ e with source_subset := e.source_subset.trans hrG },
    fun t ht z => hslit z (e.source_subset ht)⟩

/-- The local change of variable makes the factored phase exactly a monomial.
Factorization and the continuous leading root are explicit inputs here. -/
theorem exists_phase_straightening [CompactSpace Z] {G : Set ℂ}
    (hG : IsOpen G) {a : ℂ} (ha : a ∈ G) {μ : ℕ} (hμ : μ ≠ 0)
    {β : Z → ℂ} {h p : ℂ → Z → ℂ} (hβ : Continuous β) (hβ0 : ∀ z, β z ≠ 0)
    (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => h t z) G) (hc : ∀ z, h a z = 1)
    (hfactor : ∀ t ∈ G, ∀ z, p t z - p a z = β z ^ μ * (t - a) ^ μ * h t z) :
    ∃ e : LocalInverseFamily (saddleCoordinate μ a β h) a G,
      (∀ t ∈ ball a e.sourceRadius, ∀ z,
        saddleCoordinate μ a β h t z ^ μ = p t z - p a z) ∧
      ∀ w ∈ ball 0 e.targetRadius, ∀ z, p (e.inverse w z) z - p a z = w ^ μ := by
  obtain ⟨e, he⟩ := exists_saddleCoordinate_inverse hG ha μ hβ hβ0 hh hd hc
  have hpower : ∀ t ∈ ball a e.sourceRadius, ∀ z,
      saddleCoordinate μ a β h t z ^ μ = p t z - p a z :=
    fun t ht z => (saddleCoordinate_pow hμ a β h (Complex.slitPlane_ne_zero (he t ht z))).trans
      (hfactor t (e.source_subset ht) z).symm
  exact ⟨e, hpower, fun w hw z => (hpower (e.inverse w z) (e.inverse_mem w hw z) z).symm.trans
    (congrArg (fun v : ℂ => v ^ μ) (e.right_inv w hw z))⟩

/-- Select the leading root using a nonzero outgoing direction `v`. It is enough
that the rotated leading coefficient lies in the closed right half-plane.
The phase factorization and that sector condition remain explicit hypotheses. -/
theorem exists_phase_straightening_in_direction [CompactSpace Z] {G : Set ℂ}
    (hG : IsOpen G) {a : ℂ} (ha : a ∈ G) {μ : ℕ} (hμ : μ ≠ 0)
    {v : ℂ} (hv : v ≠ 0) {b : Z → ℂ} {h p : ℂ → Z → ℂ}
    (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0)
    (hsector : ∀ z, 0 ≤ (b z * v ^ μ).re)
    (hh : ContinuousOn (Function.uncurry h) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => h t z) G) (hc : ∀ z, h a z = 1)
    (hfactor : ∀ t ∈ G, ∀ z, p t z - p a z = b z * (t - a) ^ μ * h t z) :
    ∃ e : LocalInverseFamily (saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) h) a G,
      (∀ t ∈ ball a e.sourceRadius, ∀ z,
        saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) h t z ^ μ = p t z - p a z) ∧
      ∀ w ∈ ball 0 e.targetRadius, ∀ z, p (e.inverse w z) z - p a z = w ^ μ :=
  exists_phase_straightening hG ha hμ
    (continuous_leadingRoot μ v hb (fun z => mem_slitPlane_of_re_nonneg
      (hsector z) (mul_ne_zero (hb0 z) (pow_ne_zero μ hv))))
    (fun z => leadingRoot_ne_zero μ hv (b z)) hh hd hc
    (fun t ht z => (leadingRoot_pow hμ hv (hb0 z)).symm ▸ hfactor t ht z)

end Neuschel
