module

public import Neuschel.UniformLocal

/-! Quantitative stability of a simple holomorphic zero under uniform perturbations. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem exists_zero_of_approximates_id {f : ℂ → ℂ} {a d : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : d ≠ 0)
    (hf : ApproximatesLinearOn (fun s => f s / d)
      (ContinuousLinearMap.id ℂ ℂ) (ball a r) (1 / 2))
    (ha : ‖f a / d‖ ≤ r / 4) :
    ∃ s ∈ ball a r, f s = 0 ∧ ‖s - a‖ ≤ 2 * ‖f a‖ / ‖d‖ ∧
      ∀ t ∈ ball a r, f t = 0 → t = s := by
  obtain ⟨s, hs, he⟩ := Neuschel.closedBall_subset_image_of_approximates_id hr hf
    (show (0 : ℂ) ∈ closedBall (f a / d) (r / 4) by simpa using ha)
  have hz : f s = 0 := (div_eq_zero_iff.mp he).resolve_right hd
  refine ⟨s, hs, hz, ?_, ?_⟩
  · have hb := Neuschel.dist_le_of_approximates_id_half hf hs (mem_ball_self hr)
    simpa only [hz, zero_div, dist_zero_left, dist_eq_norm, zero_sub, norm_neg,
      norm_div, mul_div_assoc] using hb
  · intro t ht htz
    exact hf.injOn (f' := ContinuousLinearEquiv.refl ℂ ℂ) (Or.inr (by norm_num)) ht hs
      (by simp only [htz, hz])

theorem eventually_approximates_simple_zero {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {G : Set ℂ} {a : ℂ} (hG : IsOpen G) (ha : a ∈ G)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) G)
    (hf : DifferentiableOn ℂ f G)
    (hlim : TendstoLocallyUniformlyOn F f atTop G)
    (hz : f a = 0) (hd : deriv f a ≠ 0) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ᶠ n in atTop,
      ApproximatesLinearOn (fun s => F n s / deriv f a)
        (ContinuousLinearMap.id ℂ ℂ) (ball a r) (1 / 2) ∧
      (∀ s ∈ ball a r, deriv (F n) s ≠ 0) ∧ ‖F n a / deriv f a‖ ≤ r / 4 := by
  have hc : ContinuousAt (fun s => ‖(deriv f s - deriv f a) / deriv f a‖) a :=
    ((((hf.deriv hG).continuousOn.continuousAt (hG.mem_nhds ha)).sub_const _).div_const _).norm
  have hnear : ∀ᶠ s in 𝓝 a, ‖(deriv f s - deriv f a) / deriv f a‖ < 1 / 4 :=
    hc.tendsto.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨r₀, hr₀, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hnear.and (hG.mem_nhds ha))
  have hKG : closedBall a (r₀ / 2) ⊆ G :=
    fun s hs => (hb s (closedBall_subset_ball (half_lt_self hr₀) hs)).2
  have hconv := (tendstoLocallyUniformlyOn_iff_forall_isCompact hG).mp
    (hlim.deriv hF hG) _ hKG (isCompact_closedBall a (r₀ / 2))
  have hdn := Metric.tendstoUniformlyOn_iff.mp hconv (‖deriv f a‖ / 4)
    (by positivity)
  have hcenter : Tendsto (fun n => ‖F n a / deriv f a‖) atTop (𝓝 0) := by
    simpa only [hz, zero_div, norm_zero] using ((hlim.tendsto_at ha).div_const (deriv f a)).norm
  refine ⟨r₀ / 2, half_pos hr₀, fun s hs => hKG (ball_subset_closedBall hs), ?_⟩
  filter_upwards [hF, hdn, hcenter.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r₀ / 2 / 4))]
    with n hn hdn hcn
  have hrel : ∀ s ∈ ball a (r₀ / 2), ‖deriv (F n) s / deriv f a - 1‖ < 1 / 2 := by
    intro s hs
    have herr : ‖(deriv (F n) s - deriv f s) / deriv f a‖ < 1 / 4 := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hd)]
      simpa only [Function.comp_apply, dist_eq_norm, norm_sub_rev, div_eq_mul_inv,
        one_mul, mul_comm] using hdn s (ball_subset_closedBall hs)
    have hbase := (hb s (ball_subset_ball (half_le_self hr₀.le) hs)).1
    rw [show deriv (F n) s / deriv f a - 1 =
      (deriv (F n) s - deriv f s) / deriv f a + (deriv f s - deriv f a) / deriv f a by
        rw [← add_div, sub_add_sub_cancel, sub_div, div_self hd]]
    exact (norm_add_le _ _).trans_lt (by linarith)
  refine ⟨Neuschel.approximates_id_of_deriv_near
    (fun s hs => (hn.differentiableAt (hG.mem_nhds (hKG (ball_subset_closedBall hs)))).div_const _) ?_,
    ?_, hcn.le⟩
  · simpa [deriv_div_const] using fun s hs => (hrel s hs).le
  · intro s hs he
    have hh := hrel s hs
    norm_num [he] at hh

/-- A rate for the residual at a limiting simple zero gives the same rate for
the displacement of the unique nearby simple zero. -/
theorem exists_simple_zero_with_rate {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {G : Set ℂ} {a : ℂ} (hG : IsOpen G) (ha : a ∈ G)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) G)
    (hf : DifferentiableOn ℂ f G)
    (hlim : TendstoLocallyUniformlyOn F f atTop G)
    (hz : f a = 0) (hd : deriv f a ≠ 0)
    {ε : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ n in atTop, ‖F n a‖ ≤ C * ε n) :
    ∃ r > 0, ball a r ⊆ G ∧ ∃ K ≥ 0, ∀ᶠ n in atTop,
      ∃ s ∈ ball a r, F n s = 0 ∧ deriv (F n) s ≠ 0 ∧ ‖s - a‖ ≤ K * ε n ∧
        ∀ t ∈ ball a r, F n t = 0 → t = s := by
  obtain ⟨r, hr, hrG, hn⟩ := eventually_approximates_simple_zero hG ha hF hf hlim hz hd
  refine ⟨r, hr, hrG, 2 * C / ‖deriv f a‖, by positivity, ?_⟩
  filter_upwards [hn, hb] with n hn hbn
  obtain ⟨s, hs, hz, hdist, huniq⟩ := exists_zero_of_approximates_id hr hd hn.1 hn.2.2
  refine ⟨s, hs, hz, hn.2.1 s hs, hdist.trans ?_, huniq⟩
  calc
    2 * ‖F n a‖ / ‖deriv f a‖ ≤ 2 * (C * ε n) / ‖deriv f a‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbn (by norm_num)) (norm_nonneg _)
    _ = _ := by ring

end ThisWork
