module

public import ThisWork.HigherRank.CanonicalGrowth
public import ThisWork.HigherRank.DominantExtension
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Independence of all original Fourier branches in arbitrary rank. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter
open scoped Topology

theorem branch_linearIndependent {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ) :
    LinearIndependent ℂ (fun k : Fin r => branchIntegral r m A z (branchLabel r k)) := by
  cases r with
  | zero => omega
  | succ s =>
    by_cases heven : 2 * ((s + 1) / 2) = s + 1
    · have hθ (i : Fin s) : branchAngle (s + 1) i.succ ∈ Ioo (-Real.pi) Real.pi :=
        branchAngle_mem_principal (by omega) i.succ (Or.inr (by simp))
      have hlin := offCut_linearIndependent hr (Nat.le_succ s) hA hz m
        (fun i : Fin s => branchLabel (s + 1) i.succ)
        (fun i : Fin s => branchAngle (s + 1) i.succ) hθ
        (fun i => branchAngle_relation (by omega) i.succ)
        ((branchAngle_injective (by omega : 0 < s + 1)).comp (Fin.succ_injective s))
      have hb : HasLogNormGrowth (s + 1) (commonScale (s + 1) m A z)
          ((s + 1 : ℕ) * saddleScale (s + 1) A z)
          (branchIntegral (s + 1) m A z (branchLabel (s + 1) 0)) := by
        simpa only [branchLabel, Fin.val_zero, Nat.cast_zero, sub_zero] using
          (evenBoundary_zeroCenter_hasLogNormGrowth hr hA hz ((s + 1) / 2) heven.symm).recenter_branch hr hA hz m
      have hdom (i : Fin s) :
          branchIntegral (s + 1) m A z (branchLabel (s + 1) i.succ) =o[atTop]
            branchIntegral (s + 1) m A z (branchLabel (s + 1) 0) := by
        apply (branch_hasLogNormGrowth hr hA hz m i.succ).isLittleO (by omega) hb
        have hc : 0 < (s + 1 : ℕ) * saddleScale (s + 1) A z :=
          mul_pos (Nat.cast_pos.mpr (by omega)) (saddleScale_pos hA hz)
        nlinarith [rho_re_gt_neg_one (hθ i)]
      have hopt := linearIndependent_option_of_dominance hlin
        (hb.choose_spec.2.mono (fun _ hn => norm_pos_iff.mp hn.1)) hdom
      have h := (linearIndependent_equiv (finSuccEquiv s)).mpr hopt
      convert h using 1
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Function.comp_apply, finSuccEquiv_zero, Option.casesOn'_none]
      · simp only [Function.comp_apply, finSuccEquiv_succ, Option.casesOn'_some]
    · exact offCut_linearIndependent hr le_rfl hA hz m (branchLabel (s + 1))
        (branchAngle (s + 1))
        (fun i => branchAngle_mem_principal (by omega) i (Or.inl (by omega)))
        (fun i => branchAngle_relation (by omega) i) (branchAngle_injective (by omega))

end ThisWork.HigherRank
