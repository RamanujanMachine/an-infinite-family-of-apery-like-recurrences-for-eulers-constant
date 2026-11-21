module

public import ThisWork.Lemma8
public import ThisWork.MomentNoncancellation
public import ThisWork.ExponentialSeparation

/-! Strong recessiveness inside the span of the three integral sequences.
The quantitative moment bound prevents cancellation in every fixed
combination having a nonzero dominant coefficient. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

/-- Constant coefficients, ordered as branches one, two, and three. -/
noncomputable def branchCombination (V : Branch → ℕ → Fin 3 → ℂ)
    (a : Fin 3 → ℂ) (n : ℕ) : Fin 3 → ℂ := ∑ i, a i • V (Analytic.branchEquiv i) n

/-- A fixed combination of the two dominant branches. -/
noncomputable def dominantCombination (V : Branch → ℕ → Fin 3 → ℂ)
    (a : Fin 2 → ℂ) (n : ℕ) : Fin 3 → ℂ := a 0 • V .one n + a 1 • V .two n

/-- Branch three is strongly recessive relative to every nontrivial fixed
combination of branches one and two. -/
def StronglyRecessiveInSpan (V : Branch → ℕ → Fin 3 → ℂ) : Prop :=
  ∀ a : Fin 2 → ℂ, a 0 ≠ 0 ∨ a 1 ≠ 0 →
    (∀ᶠ n : ℕ in atTop, dominantCombination V a n ≠ 0) ∧
    ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N *
      (‖V .three n‖ / ‖dominantCombination V a n‖)) atTop (𝓝 0)

theorem branchIntegral_noncancellation {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ a : Fin 3 → ℂ, ∀ j : Fin 3,
      ‖a j‖ * ‖branchIntegral α₁ α₂ z (Analytic.branchEquiv j) n‖ ≤
        K * (n : ℝ) ^ 4 * ‖branchCombination (branchIntegral α₁ α₂ z) a n‖ := by
  let : PositiveArgument := ⟨z, hz⟩
  let S : ∀ i : Fin 3, Analytic.CompactSaddleFamily α₁ α₂ (Analytic.branchEquiv i) :=
    fun i => (Analytic.exists_compactSaddleFamily h₁ h₂ (Analytic.branchEquiv i)).some
  let D : ∀ i, (S i).LocalSaddleData := fun i => ((S i).exists_localSaddleData h₁ h₂).some
  apply Analytic.eventually_noncancellation_of_rank_three_moments
    ((Analytic.saddle_locations_injective (Analytic.saddleScale_pos h₁ h₂)).comp Analytic.branchEquiv.injective)
    (fun n i => (D i).normalizingScalar n * Complex.exp (-((n : ℂ) * (Real.log z : ℂ))))
  · exact Filter.eventually_all.mpr (fun i =>
      ((D i).eventually_normalizingScalar_ne_zero h₁ h₂).mono
        (fun n hn => mul_ne_zero hn (Complex.exp_ne_zero _)))
  · intro i k
    apply ((D i).normalized_originalMoment_tendsto h₁ h₂ k).congr'
    filter_upwards [] with n
    rw [branchIntegral_factor hz, LinearMap.map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.exp_neg, mul_assoc,
      inv_mul_cancel_left₀ (Complex.exp_ne_zero _)]

theorem eventually_branchIntegral_ne_zero {α₁ α₂ z : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, branchIntegral α₁ α₂ z j n ≠ 0 := by
  obtain ⟨C, hC, N, hb⟩ := lemma8_normEstimate h₁ h₂ hz j
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨E, _, he⟩ := hb n hn
  exact norm_pos_iff.mp (he.symm ▸ mul_pos
    (mul_pos (gammaScale_pos h₁ h₂ n) (pow_pos hz n)) (Real.exp_pos _))

theorem branchIntegral_separation_bound {α₁ α₂ z : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) {j : Branch} (hj : j = .one ∨ j = .two) :
    ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖branchIntegral α₁ α₂ z .three n‖ / ‖branchIntegral α₁ α₂ z j n‖ ≤
        Real.exp (-(9 / 2 : ℝ) * saddleScale α₁ α₂ z * (n : ℝ) ^ (2 / 3 : ℝ) +
          D * (n : ℝ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨C₃, hC₃, N₃, hb₃⟩ := lemma8_normEstimate h₁ h₂ hz .three
  obtain ⟨Cj, hCj, Nj, hbj⟩ := lemma8_normEstimate h₁ h₂ hz j
  refine ⟨C₃ + Cj, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N₃, eventually_ge_atTop Nj] with n hn₃ hnj
  obtain ⟨E₃, hE₃, he₃⟩ := hb₃ n hn₃
  obtain ⟨Ej, hEj, hej⟩ := hbj n hnj
  have hρ : (rho j).re = -1 / 2 := by
    rcases hj with rfl | rfl
    · exact rho_one_re
    · exact rho_two_re
  rw [he₃, hej, mul_div_mul_left _ _ (ne_of_gt (mul_pos (gammaScale_pos h₁ h₂ n) (pow_pos hz n))),
    ← Real.exp_sub]
  simp only [rho_three, Complex.one_re, mul_one, hρ]
  apply Real.exp_le_exp.mpr
  nlinarith [le_abs_self E₃, neg_le_abs Ej]

theorem branchIntegral_superpolynomial_separation {α₁ α₂ z : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) {j : Branch} (hj : j = .one ∨ j = .two) (N : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ N *
      (‖branchIntegral α₁ α₂ z .three n‖ / ‖branchIntegral α₁ α₂ z j n‖)) atTop (𝓝 0) := by
  obtain ⟨D, _, hb⟩ := branchIntegral_separation_bound h₁ h₂ hz hj
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity))
    (hb.mono (fun n hn => mul_le_mul_of_nonneg_left hn (pow_nonneg (Nat.cast_nonneg n) N)))
  convert Analytic.tendsto_nat_pow_mul_exp_gap
    (show 0 < (9 / 2 : ℝ) * saddleScale α₁ α₂ z by have hc := saddleScale_pos h₁ h₂ hz; positivity) D N using 1
  funext n
  congr 2
  ring

/-- Every nontrivial fixed combination of branches one and two is eventually
nonzero and dominates branch three by more than every polynomial factor. -/
theorem branchIntegral_stronglyRecessive {α₁ α₂ z : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) (a : Fin 2 → ℂ)
    (ha : a 0 ≠ 0 ∨ a 1 ≠ 0) :
    (∀ᶠ n : ℕ in atTop, dominantCombination (branchIntegral α₁ α₂ z) a n ≠ 0) ∧
    ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N *
      (‖branchIntegral α₁ α₂ z .three n‖ /
        ‖dominantCombination (branchIntegral α₁ α₂ z) a n‖)) atTop (𝓝 0) := by
  let b : Fin 3 → ℂ := ![a 0, a 1, 0]
  have hcomb (n : ℕ) : branchCombination (branchIntegral α₁ α₂ z) b n =
      dominantCombination (branchIntegral α₁ α₂ z) a n := by
    simp [branchCombination, dominantCombination, Fin.sum_univ_three, Analytic.branchEquiv, b]
  obtain ⟨j, hj, haj⟩ : ∃ j : Fin 3, (j = 0 ∨ j = 1) ∧ b j ≠ 0 := by
    rcases ha with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  have hjB : Analytic.branchEquiv j = .one ∨ Analytic.branchEquiv j = .two := by
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hajpos : 0 < ‖b j‖ := norm_pos_iff.mpr haj
  obtain ⟨K, hK, hcontrol⟩ := branchIntegral_noncancellation h₁ h₂ hz
  have hcontrol' : ∀ᶠ n : ℕ in atTop, ∀ j : Fin 3,
      ‖b j‖ * ‖branchIntegral α₁ α₂ z (Analytic.branchEquiv j) n‖ ≤
        K * (n : ℝ) ^ 4 * ‖dominantCombination (branchIntegral α₁ α₂ z) a n‖ :=
    hcontrol.mono (fun n hn j => by simpa only [hcomb] using hn b j)
  have hV := eventually_branchIntegral_ne_zero h₁ h₂ hz (Analytic.branchEquiv j)
  have hS : ∀ᶠ n : ℕ in atTop, dominantCombination (branchIntegral α₁ α₂ z) a n ≠ 0 := by
    filter_upwards [hcontrol', hV] with n hn hVn
    have hb := hn j
    have hp := mul_pos hajpos (norm_pos_iff.mpr hVn)
    intro he
    rw [he, norm_zero, mul_zero] at hb
    linarith
  refine ⟨hS, fun N => ?_⟩
  have hlim := (branchIntegral_superpolynomial_separation h₁ h₂ hz hjB (N + 4)).const_mul (K / ‖b j‖)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ hlim
  filter_upwards [hcontrol', hV, hS] with n hn hVn hSn
  have hvpos : 0 < ‖branchIntegral α₁ α₂ z (Analytic.branchEquiv j) n‖ := norm_pos_iff.mpr hVn
  have hspos : 0 < ‖dominantCombination (branchIntegral α₁ α₂ z) a n‖ := norm_pos_iff.mpr hSn
  have hr : ‖branchIntegral α₁ α₂ z .three n‖ / ‖dominantCombination (branchIntegral α₁ α₂ z) a n‖ ≤
      (K * (n : ℝ) ^ 4 / ‖b j‖) *
        (‖branchIntegral α₁ α₂ z .three n‖ / ‖branchIntegral α₁ α₂ z (Analytic.branchEquiv j) n‖) := by
    rw [div_mul_div_comm]
    apply (div_le_div_iff₀ hspos (mul_pos hajpos hvpos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hn j) (norm_nonneg (branchIntegral α₁ α₂ z .three n))]
  calc
    _ ≤ (n : ℝ) ^ N * ((K * (n : ℝ) ^ 4 / ‖b j‖) *
        (‖branchIntegral α₁ α₂ z .three n‖ / ‖branchIntegral α₁ α₂ z (Analytic.branchEquiv j) n‖)) :=
      mul_le_mul_of_nonneg_left hr (pow_nonneg (Nat.cast_nonneg n) N)
    _ = _ := by rw [pow_add]; ring

/-- Lemma 8 together with the quantitative consequence needed for strong
recessiveness. The original Lemma 8 statement is preserved. -/
theorem lemma8_with_strongRecessiveness {α₁ α₂ z : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    Lemma8 α₁ α₂ z ∧ StronglyRecessiveInSpan (branchIntegral α₁ α₂ z) :=
  ⟨lemma8 h₁ h₂ hz, branchIntegral_stronglyRecessive h₁ h₂ hz⟩

end ThisWork
