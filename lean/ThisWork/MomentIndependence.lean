module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Topology.Instances.Matrix
public import ThisWork.ContourDefinitions

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

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

theorem linearIndependent_sequences_of_moment_limits {d : ℕ} {ζ : Fin d → ℂ}
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (hζ : Function.Injective ζ) {V : Fin d → ℕ → E}
    (T : ℕ → E →ₗ[ℂ] (Fin d → ℂ)) (a : ℕ → Fin d → ℂ)
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

end ThisWork.Analytic
