module

public import Neuschel.ContourIntegral
public import ThisWork.AffineDigamma
public import ThisWork.PoleFree
public import ThisWork.SaddleStability

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology

theorem exists_normalized_log_ball {f : ℂ → ℂ} {a b : ℂ} {r : ℝ}
    (ha : a ∈ ball b r) (hf : DifferentiableOn ℂ f (ball b r))
    (hne : ∀ s ∈ ball b r, f s ≠ 0) :
    ∃ p : ℂ → ℂ, p a = 0 ∧
      (∀ s ∈ ball b r, HasDerivAt p (logDeriv f s) s) ∧
      ∀ s ∈ ball b r, f s = f a * Complex.exp (p s) := by
  have hlog : DifferentiableOn ℂ (logDeriv f) (ball b r) := by
    convert (hf.deriv isOpen_ball).div hf hne using 1
    rfl
  obtain ⟨p, hpa, hp⟩ := hlog.isExactOn_ball.with_val_at a 0
  have hconst : ∀ s ∈ ball b r, HasDerivAt (fun t => f t * Complex.exp (-p t)) 0 s := by
    intro s hs
    convert ((hf.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt.fun_mul (hp s hs).neg.cexp) using 1
    simp only [logDeriv_apply]
    field_simp [hne s hs]
    ring
  refine ⟨p, hpa, hp, fun s hs => ?_⟩
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball b r).isPreconnected
    (fun t ht => (hconst t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hconst t ht).deriv) hs ha
  have hm := congrArg (fun z : ℂ => z * Complex.exp (p s)) he
  simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel, hpa, neg_zero,
    Complex.exp_zero, mul_one, zero_add] using hm

theorem exists_normalized_phase_ball {f Q : ℂ → ℂ} {a b R : ℂ} {r : ℝ}
    (ha : a ∈ ball b r) (hR : R ≠ 0) (hf : DifferentiableOn ℂ f (ball b r))
    (hne : ∀ s ∈ ball b r, f s ≠ 0)
    (hQ : ∀ s ∈ ball b r, logDeriv f s = R * Q s) :
    ∃ p : ℂ → ℂ, p a = 0 ∧
      (∀ s ∈ ball b r, HasDerivAt p (-Q s) s) ∧
      ∀ s ∈ ball b r, f s = f a * Complex.exp (-R * p s) := by
  obtain ⟨g, hga, hg, he⟩ := exists_normalized_log_ball ha hf hne
  refine ⟨fun s => -g s / R, by simp only [hga, neg_zero, zero_div], ?_, ?_⟩
  · intro s hs
    convert (hg s hs).neg.div_const R using 1
    rw [hQ s hs, eq_div_iff hR]
    ring
  · intro s hs
    convert he s hs using 2
    congr 1
    dsimp only
    field_simp

theorem phase_simple_saddle {p Q : ℂ → ℂ} {a b : ℂ} {r : ℝ}
    (ha : a ∈ ball b r) (hp : ∀ s ∈ ball b r, HasDerivAt p (-Q s) s)
    (hz : Q a = 0) (hd : deriv Q a ≠ 0) :
    deriv p a = 0 ∧ deriv (deriv p) a ≠ 0 := by
  have he : deriv p =ᶠ[𝓝 a] fun s => -Q s :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds ha) (fun s hs => (hp s hs).deriv)
  constructor
  · simpa only [hz, neg_zero] using (hp a ha).deriv
  · rw [he.deriv_eq, deriv.fun_neg]
    exact neg_ne_zero.mpr hd

theorem norm_segmentIntegral_le_ball {f : ℂ → ℂ} {b x y : ℂ} {r B : ℝ}
    (hb : ∀ s ∈ ball b r, ‖f s‖ ≤ B) (hx : x ∈ ball b r) (hy : y ∈ ball b r) :
    ‖Neuschel.segmentIntegral f x y‖ ≤ ‖y - x‖ * B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖y - x‖ * B)
    (f := fun t : ℝ => (y - x) * f (AffineMap.lineMap x y t))
  apply (by simpa only [Neuschel.segmentIntegral, sub_zero, abs_one, mul_one] using h)
  intro t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ ((convex_ball b r).lineMap_mem hx hy
    (by simpa using Ioc_subset_Icc_self ht))) (norm_nonneg _)

theorem norm_primitive_sub_le_ball {p q F H : ℂ → ℂ} {a b s : ℂ} {r B : ℝ}
    (ha : a ∈ ball b r) (hs : s ∈ ball b r)
    (hp : ∀ t ∈ ball b r, HasDerivAt p (F t) t)
    (hq : ∀ t ∈ ball b r, HasDerivAt q (H t) t)
    (hcont : ContinuousOn (fun t => F t - H t) (ball b r))
    (hb : ∀ t ∈ ball b r, ‖F t - H t‖ ≤ B) :
    ‖(p s - p a) - (q s - q a)‖ ≤ ‖s - a‖ * B := by
  have he := Neuschel.segmentIntegral_eq_primitive_sub (convex_ball b r)
    (fun t ht => (hp t ht).fun_sub (hq t ht)) hcont ha hs
  have hn := norm_segmentIntegral_le_ball hb ha hs
  convert hn using 1
  rw [he]
  congr 1
  abel

end ThisWork.Analytic
