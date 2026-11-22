module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A strictly dominant sequence extends any independent subfamily. This
avoids requiring boundary moment limits solely for sequence independence. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Asymptotics
open scoped Topology

theorem dominant_not_mem_span {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {b : ℕ → V} {v : ι → ℕ → V} (hb : ∀ᶠ n : ℕ in atTop, b n ≠ 0)
    (hv : ∀ i, v i =o[atTop] b) : b ∉ Submodule.span ℂ (range v) := by
  intro hspan
  have hsmall : b =o[atTop] b := by
    apply Submodule.span_induction (p := fun w _ => w =o[atTop] b) _ _ _ _ hspan
    · intro w hw
      obtain ⟨i, rfl⟩ := hw
      exact hv i
    · exact isLittleO_zero b atTop
    · intro w u _ _ hw hu
      exact hw.add hu
    · intro c w _ hw
      exact hw.const_smul_left c
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖b n‖ := hb.mono (fun _ hn => norm_pos_iff.mpr hn)
  obtain ⟨n, hn⟩ := (hsmall.eventuallyLT_norm_of_eventually_pos hpos).exists
  exact (lt_irrefl ‖b n‖) hn

theorem linearIndependent_option_of_dominance {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {b : ℕ → V} {v : ι → ℕ → V} (hlin : LinearIndependent ℂ v)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≠ 0) (hv : ∀ i, v i =o[atTop] b) :
    LinearIndependent ℂ (fun q : Option ι => Option.casesOn' q b v) :=
  hlin.option (dominant_not_mem_span hb hv)

end ThisWork.HigherRank
