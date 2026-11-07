module

public import ThisWork.NormalizedAsymptotics
public import ThisWork.Normalization

/-! Lemma 8 for the three Mellin–Barnes integral sequences at arbitrary `z > 0`.
The shared analytic proof estimates the normalized integrals; the common `z^n`
factor is restored exactly for growth and canceled by a linear map for independence. -/

@[expose] public section

namespace ThisWork

open Set Filter
open scoped Topology

/-- Growth of the actual z-dependent integrals, including their common `z^n` factor. -/
theorem lemma8_normEstimate {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (hz : 0 < z) : Lemma8NormEstimate α₁ α₂ z := by
  let : PositiveArgument := ⟨z, hz⟩
  intro j
  obtain ⟨C, hC, N, hb⟩ := Analytic.lemma8_normEstimate h₁ h₂ j
  refine ⟨C, hC, N, fun n hn => ?_⟩
  obtain ⟨E, hE, he⟩ := hb n hn
  refine ⟨E, hE, ?_⟩
  rw [norm_branchIntegral_factor hz, he]
  change z ^ n * (gammaScale α₁ α₂ n * Real.exp
    (-3 * saddleScale α₁ α₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)) = _
  ring

/-- Independence is preserved when the same nonzero scalar rescales every branch at each n. -/
theorem branchIntegral_linearIndependent {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (hz : 0 < z) : LinearIndependent ℂ (fun j : Branch => branchIntegral α₁ α₂ z j) := by
  let : PositiveArgument := ⟨z, hz⟩
  let unscale : (ℕ → Fin 3 → ℂ) →ₗ[ℂ] (ℕ → Fin 3 → ℂ) := {
    toFun := fun f n => Complex.exp (-((n : ℂ) * (Real.log z : ℂ))) • f n
    map_add' := by
      intro f g
      funext n k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
    map_smul' := by
      intro a f
      funext n k
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm]
  }
  have he : (⇑unscale ∘ fun j : Branch => branchIntegral α₁ α₂ z j) =
      (fun j : Branch => @Analytic.normalizedBranchIntegral ⟨z, hz⟩ α₁ α₂ j) := by
    funext j n k
    change Complex.exp (-((n : ℂ) * (Real.log z : ℂ))) * branchIntegral α₁ α₂ z j n k = _
    rw [branchIntegral_factor hz]
    simp [Pi.smul_apply, smul_eq_mul, Complex.exp_neg]
  apply LinearIndependent.of_comp unscale
  rw [he]
  exact Analytic.branchIntegral_linearIndependent h₁ h₂

/-- Lemma 8: growth and independence, for every positive real Meijer G argument. -/
theorem lemma8 {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    Lemma8 α₁ α₂ z := ⟨lemma8_normEstimate h₁ h₂ hz, branchIntegral_linearIndependent h₁ h₂ hz⟩

/-- The former `z=1` result is a direct specialization of the general theorem. -/
theorem lemma8_one {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) : Lemma8 α₁ α₂ 1 :=
  lemma8 h₁ h₂ (by norm_num)

end ThisWork
