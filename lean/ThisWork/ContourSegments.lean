module

public import Neuschel.ContourIntegral

/-! Finite contour identities inside a holomorphic disk, with arbitrary
orientations of the real parameter interval. -/

@[expose] public section
namespace ThisWork

open Set Metric MeasureTheory

theorem affine_line_mem_of_endpoints {K : Set ℂ} (hK : Convex ℝ K)
    (q v : ℂ) {a b u : ℝ} (ha : q + (a : ℂ) * v ∈ K)
    (hb : q + (b : ℂ) * v ∈ K) (hu : u ∈ uIcc a b) : q + (u : ℂ) * v ∈ K := by
  let L : ℝ →ₗ[ℝ] ℂ :=
    { toFun := fun t => (t : ℂ) * v
      map_add' := by intro x y; push_cast; ring
      map_smul' := by intro x y; simp only [smul_eq_mul, RingHom.id_apply,
        Complex.ofReal_mul, Complex.real_smul]; ring }
  exact ((hK.translate_preimage_right q).linear_preimage L).ordConnected.uIcc_subset ha hb hu

theorem segmentIntegral_reverse {f : ℂ → ℂ} {c x y : ℂ} {d : ℝ}
    (hf : DifferentiableOn ℂ f (ball c d)) (hx : x ∈ ball c d) (hy : y ∈ ball c d) :
    Neuschel.segmentIntegral f y x = -Neuschel.segmentIntegral f x y := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  rw [Neuschel.segmentIntegral_eq_primitive_sub (convex_ball c d) hF hf.continuousOn hy hx,
    Neuschel.segmentIntegral_eq_primitive_sub (convex_ball c d) hF hf.continuousOn hx hy]
  abel

theorem segmentIntegral_add {f : ℂ → ℂ} {c x y z : ℂ} {d : ℝ}
    (hf : DifferentiableOn ℂ f (ball c d)) (hx : x ∈ ball c d)
    (hy : y ∈ ball c d) (hz : z ∈ ball c d) :
    Neuschel.segmentIntegral f x y + Neuschel.segmentIntegral f y z =
      Neuschel.segmentIntegral f x z := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  rw [Neuschel.segmentIntegral_eq_primitive_sub (convex_ball c d) hF hf.continuousOn hx hy,
    Neuschel.segmentIntegral_eq_primitive_sub (convex_ball c d) hF hf.continuousOn hy hz,
    Neuschel.segmentIntegral_eq_primitive_sub (convex_ball c d) hF hf.continuousOn hx hz]
  abel

theorem contour_integral_eq_segment_of_uIcc {A B : ℝ} {c : ℂ} {d : ℝ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c d)) {γ v : ℝ → ℂ}
    (hc : Continuous γ) (hv : Continuous v) (hd : ∀ s, HasDerivAt γ (v s) s)
    (hmap : ∀ s ∈ uIcc A B, γ s ∈ ball c d) :
    (∫ s in A..B, v s * f (γ s)) = Neuschel.segmentIntegral f (γ A) (γ B) := by
  by_cases hab : A ≤ B
  · exact Neuschel.contour_integral_eq_segment hab hf hc.continuousOn hv.continuousOn
      (fun s _ => hd s) (fun s hs => hmap s (by simpa only [uIcc_of_le hab] using hs))
  · have hba : B ≤ A := (le_of_not_ge hab)
    rw [intervalIntegral.integral_symm B A,
      Neuschel.contour_integral_eq_segment hba hf hc.continuousOn hv.continuousOn
        (fun s _ => hd s) (fun s hs => hmap s (by simpa only [uIcc_of_ge hba] using hs)),
      segmentIntegral_reverse hf (hmap A left_mem_uIcc) (hmap B right_mem_uIcc), neg_neg]

theorem horizontal_integral_eq_segment {f : ℂ → ℂ} {c : ℂ} {d a b y : ℝ}
    (hf : DifferentiableOn ℂ f (ball c d))
    (hmap : ∀ u ∈ uIcc a b, (u : ℂ) + (y : ℂ) * Complex.I ∈ ball c d) :
    (∫ u in a..b, f ((u : ℂ) + (y : ℂ) * Complex.I)) =
      Neuschel.segmentIntegral f ((a : ℂ) + (y : ℂ) * Complex.I) ((b : ℂ) + (y : ℂ) * Complex.I) := by
  simpa only [one_mul] using contour_integral_eq_segment_of_uIcc hf
    (γ := fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I) (v := fun _ => 1)
    (by fun_prop) continuous_const
    (fun u => by simpa only [id_eq, Complex.ofReal_one] using
      ((hasDerivAt_id u).ofReal_comp).add_const ((y : ℂ) * Complex.I)) hmap

theorem affine_integral_eq_segment {f : ℂ → ℂ} {c q v : ℂ} {d a b : ℝ}
    (hf : DifferentiableOn ℂ f (ball c d))
    (ha : q + (a : ℂ) * v ∈ ball c d) (hb : q + (b : ℂ) * v ∈ ball c d) :
    (∫ u in a..b, v * f (q + (u : ℂ) * v)) =
      Neuschel.segmentIntegral f (q + (a : ℂ) * v) (q + (b : ℂ) * v) := by
  exact contour_integral_eq_segment_of_uIcc hf (by fun_prop) continuous_const
    (fun u => by simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id u).ofReal_comp).mul_const v).const_add q)
    (fun u hu => affine_line_mem_of_endpoints (convex_ball c d) q v ha hb hu)

theorem vertical_integral_eq_segment {f : ℂ → ℂ} {c : ℂ} {d a b x : ℝ}
    (hf : DifferentiableOn ℂ f (ball c d))
    (hmap : ∀ u ∈ uIcc a b, (x : ℂ) + (u : ℂ) * Complex.I ∈ ball c d) :
    (∫ u in a..b, Complex.I * f ((x : ℂ) + (u : ℂ) * Complex.I)) =
      Neuschel.segmentIntegral f ((x : ℂ) + (a : ℂ) * Complex.I) ((x : ℂ) + (b : ℂ) * Complex.I) := by
  exact contour_integral_eq_segment_of_uIcc hf (by fun_prop) continuous_const
    (fun u => by simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id u).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)) hmap

end ThisWork
