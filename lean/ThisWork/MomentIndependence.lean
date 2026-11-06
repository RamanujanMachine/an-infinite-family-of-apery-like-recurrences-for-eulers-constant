module

public import ThisWork.Definitions
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Topology.Instances.Matrix

/-! Independence from limiting power moments at distinct saddle locations. -/

@[expose] public section

namespace ThisWork

open Set Filter Matrix
open scoped Topology

theorem eventually_linearIndependent_of_moment_limits {d : ℕ} {ζ : Fin d → ℂ}
    (hζ : Function.Injective ζ) {A : ℕ → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ i k, Tendsto (fun n => A n i k) atTop (𝓝 (ζ i ^ k.val))) :
    ∀ᶠ n : ℕ in atTop, LinearIndependent ℂ (fun i => A n i) := by
  have hlim : Tendsto A atTop (𝓝 (Matrix.vandermonde ζ)) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun k => hA i k))
  have hdet : Tendsto (fun n => (A n).det) atTop (𝓝 (Matrix.vandermonde ζ).det) :=
    (continuous_id.matrix_det.continuousAt.tendsto).comp hlim
  have hn : (Matrix.vandermonde ζ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hζ
  exact (hdet.eventually (isOpen_ne.mem_nhds hn)).mono
    (fun n hn => Matrix.linearIndependent_rows_of_det_ne_zero hn)

theorem rho_injective : Function.Injective rho := by
  intro a b he
  cases a <;> cases b <;> try rfl
  all_goals
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    simp only [rho_one_re, rho_two_re, rho_three, Complex.one_re,
      rho_one_im, rho_two_im, Complex.one_im] at hre him
    exfalso
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]

theorem saddle_locations_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective (fun j => (c : ℂ) * rho j) := by
  intro a b he
  exact rho_injective (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne') he)

theorem linearIndependent_sequences_of_moment_limits {d : ℕ} {ζ : Fin d → ℂ}
    (hζ : Function.Injective ζ) {V : Fin d → ℕ → Fin d → ℂ}
    (T : ℕ → (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (a : ℕ → Fin d → ℂ)
    (ha : ∀ᶠ n : ℕ in atTop, ∀ i, a n i ≠ 0)
    (hlim : ∀ i k, Tendsto (fun n => a n i * T n (V i n) k) atTop (𝓝 (ζ i ^ k.val))) :
    LinearIndependent ℂ V := by
  obtain ⟨n, hn, hna⟩ := ((eventually_linearIndependent_of_moment_limits hζ hlim).and ha).exists
  have hscaled : LinearIndependent ℂ (fun i => a n i • T n (V i n)) := hn
  have hbase : LinearIndependent ℂ (fun i => T n (V i n)) := by
    apply (LinearIndependent.units_smul_iff (fun i => T n (V i n))
      (fun i => Units.mk0 (a n i) (hna i))).mp
    change LinearIndependent ℂ (fun i => (Units.mk0 (a n i) (hna i)) • T n (V i n))
    simpa only [Units.smul_def, Units.val_mk0] using hscaled
  exact LinearIndependent.of_comp ((T n).comp (LinearMap.proj n)) hbase

noncomputable def momentTransform (n : ℕ) (R : ℝ) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 0, ((n : ℂ) * v 0 - v 1) / (R : ℂ),
    ((n : ℂ) ^ 2 * v 0 - 2 * (n : ℂ) * v 1 + v 2) / (R : ℂ) ^ 2]
  map_add' := by
    intro v w
    ext k
    fin_cases k <;> simp [Pi.add_apply] <;> ring
  map_smul' := by
    intro c v
    ext k
    fin_cases k <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

def branchEquiv : Fin 3 ≃ Branch where
  toFun := ![Branch.one, Branch.two, Branch.three]
  invFun := fun j => match j with | .one => 0 | .two => 1 | .three => 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro j; cases j <;> rfl

theorem linearIndependent_branches_of_moment_limits {c : ℝ} (hc : 0 < c)
    {V : Branch → ℕ → Fin 3 → ℂ}
    (T : ℕ → (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (a : ℕ → Branch → ℂ)
    (ha : ∀ᶠ n : ℕ in atTop, ∀ j, a n j ≠ 0)
    (hlim : ∀ j k, Tendsto (fun n => a n j * T n (V j n) k) atTop
      (𝓝 (((c : ℂ) * rho j) ^ k.val))) :
    LinearIndependent ℂ V := by
  have hv := linearIndependent_sequences_of_moment_limits
    ((saddle_locations_injective hc).comp branchEquiv.injective)
    T (fun n i => a n (branchEquiv i))
    (ha.mono (fun n hn i => hn (branchEquiv i))) (fun i k => hlim (branchEquiv i) k)
  exact (linearIndependent_equiv branchEquiv).mp hv

end ThisWork
