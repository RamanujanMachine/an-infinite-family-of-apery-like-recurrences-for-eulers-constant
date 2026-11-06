module

public import ThisWork.FullMomentAsymptotics
public import ThisWork.HankelMoments

/-! Normalized moment limits for the original vector integral sequences. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology OnePoint

noncomputable def cauchyFactor : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem cauchyFactor_ne_zero : cauchyFactor ≠ 0 :=
  inv_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

theorem div_mul_cancel_extra_factor (A K B H : ℂ) (hB : B ≠ 0) :
    (A / (K * B)) * (B * H) = A * K⁻¹ * H := by
  rw [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (A * K⁻¹ * H) * (B⁻¹ * B) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hB, mul_one]

namespace CompactSaddleFamily.LocalSaddleData

noncomputable def offset {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : ℕ := D.shift + S.firstIndex

theorem index_eq_add_offset {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : D.index m = m + D.offset := Nat.add_assoc _ _ _

@[simp] theorem index_sub_offset {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : D.index m - D.offset = m := by
  simp only [D.index_eq_add_offset, Nat.add_sub_cancel_right]

noncomputable def rawCenter {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (n : ℕ) : ℂ := D.center (n - D.offset)

noncomputable def rawKernel {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (n : ℕ) : ℂ :=
  kernel α₁ α₂ j n ((largeScale n : ℂ) * D.rawCenter n)

noncomputable def normalizingScalar {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (n : ℕ) : ℂ :=
  (D.quadraticRoot (n - D.offset) * ((largeScale n ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)) /
    (branchOrientation j * D.rawKernel n * cauchyFactor * (largeScale n : ℂ))

@[simp] theorem rawCenter_index {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : D.rawCenter (D.index m) = D.center m := by
  rw [rawCenter, index_sub_offset]

@[simp] theorem rawKernel_index {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : D.rawKernel (D.index m) = D.saddleKernel m := by
  simp only [rawKernel, rawCenter_index, saddleKernel]

theorem rawCenter_mem_disk {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (n : ℕ) :
    D.rawCenter n ∈ saddleDisk (saddleScale α₁ α₂) j :=
  S.saddle_mem_disk h₁ h₂ (n - D.offset + D.shift)

theorem eventually_rawKernel_ne_zero {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∀ᶠ n : ℕ in atTop, D.rawKernel n ≠ 0 := by
  filter_upwards [eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j] with n hn
  exact kernel_ne_zero j n (hn.2 (D.rawCenter_mem_disk h₁ h₂ n))

@[simp] theorem normalizingScalar_index {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) :
    D.normalizingScalar (D.index m) = D.gaussianNormalizer m /
      (branchOrientation j * D.saddleKernel m * cauchyFactor * (largeScale (D.index m) : ℂ)) := by
  simp only [normalizingScalar, index_sub_offset, rawKernel_index, gaussianNormalizer]

theorem eventually_normalizingScalar_ne_zero {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∀ᶠ n : ℕ in atTop, D.normalizingScalar n ≠ 0 := by
  filter_upwards [D.eventually_rawKernel_ne_zero h₁ h₂, eventually_gt_atTop (0 : ℕ)] with n hK hn
  have hR := largeScale_pos hn
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hp : 0 < largeScale n ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) :=
    div_pos (Real.rpow_pos_of_pos hR _) hG
  exact div_ne_zero
    (mul_ne_zero (Neuschel.leadingRoot_ne_zero 2 D.velocity_ne_zero _) (Complex.ofReal_ne_zero.mpr hp.ne'))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (branchOrientation_ne_zero j) hK) cauchyFactor_ne_zero)
      (Complex.ofReal_ne_zero.mpr hR.ne'))

theorem eventually_normalized_transform_eq_fullMoment {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (k : Fin 3) :
    ∀ᶠ m : ℕ in atTop,
      D.normalizingScalar (D.index m) *
        momentTransform (D.index m) (largeScale (D.index m)) (branchIntegral α₁ α₂ j (D.index m)) k =
      D.normalizedFullMoment m k.val := by
  filter_upwards [D.index_tendsto.eventually (eventually_saddleContours_admissible h₁ h₂ j)] with m hn
  have hσ := S.saddle_mem_disk h₁ h₂ (m + D.shift)
  have ha := hn.2 (D.center m) hσ
  have hr := saddleContourRight_bounds (saddleScale_pos h₁ h₂) j hσ
  have hv := congrFun (branchIntegral_momentTransform_eq_scaled_contour h₁ h₂ j (D.index m)
    (largeScale_pos hn.1) hr.1 ha.2.1 ha.2.2.1) k
  change momentTransform (D.index m) (largeScale (D.index m)) (branchIntegral α₁ α₂ j (D.index m)) k =
    cauchyFactor * (largeScale (D.index m) : ℂ) * D.fullMoment m k.val at hv
  rw [hv, normalizingScalar_index,
    mul_assoc (branchOrientation j * D.saddleKernel m) cauchyFactor (largeScale (D.index m) : ℂ)]
  exact div_mul_cancel_extra_factor _ _ _ _
    (mul_ne_zero cauchyFactor_ne_zero (Complex.ofReal_ne_zero.mpr (largeScale_pos hn.1).ne'))

theorem normalized_originalMoment_tendsto {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (k : Fin 3) :
    Tendsto (fun n : ℕ => D.normalizingScalar n *
      momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) k) atTop
      (𝓝 (((saddleScale α₁ α₂ : ℂ) * rho j) ^ k.val)) := by
  apply (tendsto_add_atTop_iff_nat D.offset).mp
  have hm := (D.normalizedFullMoment_tendsto h₁ h₂ k.val).congr'
    ((D.eventually_normalized_transform_eq_fullMoment h₁ h₂ k).mono (fun m hm => hm.symm))
  simpa only [D.index_eq_add_offset] using hm

/-- The common nonzero Gaussian amplitude for the three power moments. -/
noncomputable def gaussianAmplitude {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (n : ℕ) : ℂ := (D.normalizingScalar n)⁻¹

/-- One Gaussian moment asymptotic supplies both the vector shape and independence. -/
theorem gaussian_moment_asymptotics {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) :
    (∀ᶠ n : ℕ in atTop, D.gaussianAmplitude n ≠ 0) ∧
      Tendsto (fun n => fun k : Fin 3 =>
        momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) k / D.gaussianAmplitude n)
        atTop (𝓝 (fun k => ((saddleScale α₁ α₂ : ℂ) * rho j) ^ k.val)) := by
  refine ⟨(D.eventually_normalizingScalar_ne_zero h₁ h₂).mono (fun n hn => inv_ne_zero hn), ?_⟩
  apply tendsto_pi_nhds.mpr
  intro k
  simpa only [gaussianAmplitude, div_inv_eq_mul, mul_comm] using
    D.normalized_originalMoment_tendsto h₁ h₂ k

end CompactSaddleFamily.LocalSaddleData

theorem branchIntegral_linearIndependent {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) :
    LinearIndependent ℂ (fun j : Branch => branchIntegral α₁ α₂ j) := by
  let : Fintype Branch := Fintype.ofEquiv (Fin 3) branchEquiv
  let S : ∀ j, CompactSaddleFamily α₁ α₂ j := fun j => (exists_compactSaddleFamily h₁ h₂ j).some
  let D : ∀ j, (S j).LocalSaddleData := fun j => ((S j).exists_localSaddleData h₁ h₂).some
  have hm := fun j => (D j).gaussian_moment_asymptotics h₁ h₂
  apply linearIndependent_branches_of_moment_limits (saddleScale_pos h₁ h₂)
    (fun n => momentTransform n (largeScale n)) (fun n j => ((D j).gaussianAmplitude n)⁻¹)
  · exact Filter.eventually_all.mpr (fun j => (hm j).1.mono (fun _ hn => inv_ne_zero hn))
  · intro j k
    simpa only [div_eq_mul_inv, mul_comm] using (tendsto_pi_nhds.mp (hm j).2) k

end ThisWork
