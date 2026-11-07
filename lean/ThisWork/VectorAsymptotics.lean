module

public import ThisWork.Argument
public import ThisWork.OriginalMomentLimits

/-! The original vector shape recovered from the common Gaussian moment limits. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter
open scoped Topology

/-- Exact recovery of the original coordinates after removing their powers of `n`. -/
theorem normalized_vector_eq_moments (n : ℕ) {R : ℝ} (hn : n ≠ 0) (hR : R ≠ 0)
    (a : ℂ) (v : Fin 3 → ℂ) :
    (fun k : Fin 3 => a * v k / (n : ℂ) ^ k.val) =
      ![a * momentTransform n R v 0,
        a * momentTransform n R v 0 - (R : ℂ) / n * (a * momentTransform n R v 1),
        a * momentTransform n R v 0 - 2 * ((R : ℂ) / n) * (a * momentTransform n R v 1) +
          ((R : ℂ) / n) ^ 2 * (a * momentTransform n R v 2)] := by
  ext k
  fin_cases k <;> simp [momentTransform]
  all_goals
    field_simp [Nat.cast_ne_zero.mpr hn, Complex.ofReal_ne_zero.mpr hR]
    ring

/-- The power-moment limits recover one common leading amplitude in the original vector. -/
theorem vector_profile_tendsto_of_moment_limits {V : ℕ → Fin 3 → ℂ} {a : ℕ → ℂ} {ζ : ℂ}
    (hlim : ∀ k : Fin 3, Tendsto
      (fun n => a n * momentTransform n (largeScale n) (V n) k) atTop (𝓝 (ζ ^ k.val))) :
    Tendsto (fun n => fun k : Fin 3 => a n * V n k / (n : ℂ) ^ k.val)
      atTop (𝓝 (fun _ => 1)) := by
  let w := fun n k => a n * momentTransform n (largeScale n) (V n) k
  have hR : Tendsto (fun n : ℕ => (largeScale n : ℂ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp largeScale_div_nat_tendsto
  have h0 : Tendsto (fun n => w n 0) atTop (𝓝 1) := by simpa only [Fin.val_zero, pow_zero] using hlim 0
  have hp : Tendsto (fun n =>
      ![w n 0, w n 0 - (largeScale n : ℂ) / n * w n 1,
        w n 0 - 2 * ((largeScale n : ℂ) / n) * w n 1 + ((largeScale n : ℂ) / n) ^ 2 * w n 2])
      atTop (𝓝 (fun _ : Fin 3 => (1 : ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro k
    fin_cases k
    · exact h0
    · simpa [w] using h0.sub (hR.mul (hlim 1))
    · simpa [w] using
        (h0.sub (((tendsto_const_nhds.mul hR).mul (hlim 1)))).add ((hR.pow 2).mul (hlim 2))
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (normalized_vector_eq_moments n hn.ne' (largeScale_pos hn).ne' (a n) (V n)).symm

/-- A vector with profile `(1,n,n²)` has norm asymptotic to its last component scale. -/
theorem vector_norm_tendsto_of_profile {V : ℕ → Fin 3 → ℂ} {a : ℕ → ℂ}
    (hp : Tendsto (fun n => fun k : Fin 3 => a n * V n k / (n : ℂ) ^ k.val)
      atTop (𝓝 (fun _ => 1))) :
    Tendsto (fun n => ‖a n‖ * ‖V n‖ / (n : ℝ) ^ 2) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hs : Tendsto (fun n : ℕ => ![(n : ℂ)⁻¹ ^ 2, (n : ℂ)⁻¹, 1])
      atTop (𝓝 (Pi.single (2 : Fin 3) (1 : ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro k
    fin_cases k
    · simpa using hi.pow 2
    · simpa using hi
    · simp
  have he (n : ℕ) :
      ![(n : ℂ)⁻¹ ^ 2, (n : ℂ)⁻¹, 1] * (fun k : Fin 3 => a n * V n k / (n : ℂ) ^ k.val) =
        (a n / (n : ℂ) ^ 2) • V n := by
    ext k
    fin_cases k <;> simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, inv_pow]
    all_goals ring
  have ht : Tendsto (fun n : ℕ => (a n / (n : ℂ) ^ 2) • V n)
      atTop (𝓝 (Pi.single (2 : Fin 3) (1 : ℂ))) := by
    simpa only [Pi.mul_def, mul_one] using (hs.mul hp).congr' (Eventually.of_forall he)
  simpa only [norm_smul, norm_div, norm_pow, Complex.norm_natCast, Pi.norm_single,
    norm_one, div_mul_eq_mul_div] using ht.norm

namespace CompactSaddleFamily.LocalSaddleData

/-- Dividing coordinate `k` by the Gaussian amplitude and `n^k` gives limit one. -/
theorem vector_profile_tendsto [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    Tendsto (fun n => fun k : Fin 3 =>
      normalizedBranchIntegral α₁ α₂ j n k / (D.gaussianAmplitude n * (n : ℂ) ^ k.val))
      atTop (𝓝 (fun _ => 1)) := by
  have hm := D.gaussian_moment_asymptotics h₁ h₂
  have hp := vector_profile_tendsto_of_moment_limits
    (a := fun n => (D.gaussianAmplitude n)⁻¹)
    (fun k => by simpa only [div_eq_mul_inv, mul_comm] using (tendsto_pi_nhds.mp hm.2) k)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hp

/-- The original vector norm has the precise leading polynomial factor `n²`. -/
theorem vector_norm_asymptotic [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    Tendsto (fun n => ‖normalizedBranchIntegral α₁ α₂ j n‖ /
      ((n : ℝ) ^ 2 * ‖D.gaussianAmplitude n‖)) atTop (𝓝 1) := by
  have hp : Tendsto (fun n => fun k : Fin 3 =>
      (D.gaussianAmplitude n)⁻¹ * normalizedBranchIntegral α₁ α₂ j n k / (n : ℂ) ^ k.val)
      atTop (𝓝 (fun _ => 1)) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      D.vector_profile_tendsto h₁ h₂
  simpa only [norm_inv, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
    vector_norm_tendsto_of_profile hp

/-- Taking logarithms of the vector shape costs only a bounded error. -/
theorem eventually_vector_log_norm_shape [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∀ᶠ n : ℕ in atTop, 0 < ‖normalizedBranchIntegral α₁ α₂ j n‖ ∧
      |Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖ - Real.log ‖D.gaussianAmplitude n‖ -
        2 * Real.log (n : ℝ)| ≤ 1 := by
  have hl : Tendsto (fun n => Real.log (‖normalizedBranchIntegral α₁ α₂ j n‖ /
      ((n : ℝ) ^ 2 * ‖D.gaussianAmplitude n‖))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using (D.vector_norm_asymptotic h₁ h₂).log one_ne_zero
  filter_upwards [(D.gaussian_moment_asymptotics h₁ h₂).1, eventually_gt_atTop (0 : ℕ),
    (D.vector_norm_asymptotic h₁ h₂).eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
    hl.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))] with n hB hn hpos hlog
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hB0 : 0 < ‖D.gaussianAmplitude n‖ := norm_pos_iff.mpr hB
  have hd : 0 < (n : ℝ) ^ 2 * ‖D.gaussianAmplitude n‖ := mul_pos (pow_pos hn0 _) hB0
  have hx : 0 < ‖normalizedBranchIntegral α₁ α₂ j n‖ := by
    simpa only [zero_mul] using (lt_div_iff₀ hd).mp hpos
  rw [Real.log_div hx.ne' hd.ne', Real.log_mul (pow_ne_zero 2 hn0.ne') hB0.ne',
    Real.log_pow] at hlog
  simp only [Nat.cast_ofNat] at hlog
  refine ⟨hx, ?_⟩
  convert hlog.le using 1
  congr 1
  ring

end CompactSaddleFamily.LocalSaddleData

end ThisWork.Analytic
