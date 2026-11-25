module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import ThisWork.LocalPhaseTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology OnePoint

noncomputable def sequenceFamily (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (s : ℂ) (z : OnePoint ℕ) : ℂ :=
  z.elim (f s) (fun n => F n s)

@[simp] theorem sequenceFamily_infty (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (s : ℂ) :
    sequenceFamily F f s ∞ = f s := rfl

@[simp] theorem sequenceFamily_nat (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (s : ℂ) (n : ℕ) :
    sequenceFamily F f s n = F n s := rfl

theorem continuousOn_sequenceFamily {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hF : ∀ n, ContinuousOn (F n) K) (hf : ContinuousOn f K)
    (hlim : TendstoUniformlyOn F f atTop K) :
    ContinuousOn (Function.uncurry (sequenceFamily F f)) (K ×ˢ univ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let P : C(OnePoint ℕ, C(K, ℂ)) := OnePoint.continuousMapMkNat
    (fun n => ⟨_, (hF n).domRestrict⟩) ⟨_, hf.domRestrict⟩
    ((hf.tendsto_domRestrict_iff_tendstoUniformlyOn hF).mpr hlim)
  have hP : Continuous (fun w : K × OnePoint ℕ => P w.2 w.1) :=
    continuous_eval.comp ((P.continuous.comp continuous_snd).prodMk continuous_fst)
  rw [continuousOn_iff_continuous_domRestrict]
  have hin : Continuous (fun w : (K ×ˢ (univ : Set (OnePoint ℕ))) =>
      ((⟨w.val.1, w.property.1⟩ : K), w.val.2)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (continuous_snd.comp continuous_subtype_val)
  convert hP.comp hin using 1
  funext w
  rcases w with ⟨⟨s, z⟩, hs, hz⟩
  cases z <;> rfl

end ThisWork.Analytic
