module

public import ThisWork.HigherRank.CanonicalIndependence
public import ThisWork.HigherRank.OffCutRecessiveness

/-! Strong recessiveness relative to every fixed combination supported on
the nonrecessive original branches. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Asymptotics
open scoped Topology

theorem branch_combination_stronglyRecessive {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (m : ℕ) (a : Fin r → ℂ) (ha : a ≠ 0)
    (hsupport : ∀ i, branchLabel r i = 0 → a i = 0) :
    (∀ᶠ n : ℕ in atTop, (∑ i, a i • branchIntegral r m A z (branchLabel r i) n) ≠ 0) ∧
      ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N *
        (‖branchIntegral r m A z 0 n‖ /
          ‖∑ i, a i • branchIntegral r m A z (branchLabel r i) n‖)) atTop (𝓝 0) := by
  classical
  cases r with
  | zero => omega
  | succ s =>
    by_cases heven : 2 * ((s + 1) / 2) = s + 1
    · have hθ (i : Fin s) : branchAngle (s + 1) i.succ ∈ Ioo (-Real.pi) Real.pi :=
        branchAngle_mem_principal (by omega) i.succ (Or.inr (by simp))
      by_cases ha0 : a 0 = 0
      · have ha' : (fun i : Fin s => a i.succ) ≠ 0 := by
          intro hz
          apply ha
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ha0
          · exact congrFun hz j
        have hs := offCut_stronglyRecessive hr (Nat.le_succ s) hA hz m
          (fun i : Fin s => branchLabel (s + 1) i.succ)
          (fun i : Fin s => branchAngle (s + 1) i.succ) hθ
          (fun i => branchAngle_relation (by omega) i.succ)
          ((branchAngle_injective (by omega : 0 < s + 1)).comp (Fin.succ_injective s))
          (fun i => a i.succ) ha' (fun i hi he => hi (hsupport i.succ he))
        have hsum (n : ℕ) :
            (∑ i : Fin (s + 1), a i • branchIntegral (s + 1) m A z (branchLabel (s + 1) i) n) =
              ∑ i : Fin s, a i.succ • branchIntegral (s + 1) m A z (branchLabel (s + 1) i.succ) n := by
          rw [Fin.sum_univ_succ]
          simp only [ha0, zero_smul, zero_add]
        simpa only [hsum] using hs
      · have hb : HasLogNormGrowth (s + 1) (commonScale (s + 1) m A z)
            ((s + 1 : ℕ) * saddleScale (s + 1) A z)
            (branchIntegral (s + 1) m A z (branchLabel (s + 1) 0)) := by
          simpa only [branchLabel, Fin.val_zero, Nat.cast_zero, sub_zero] using
            (evenBoundary_zeroCenter_hasLogNormGrowth hr hA hz ((s + 1) / 2) heven.symm).recenter_branch hr hA hz m
        have hc : 0 < (s + 1 : ℕ) * saddleScale (s + 1) A z :=
          mul_pos (Nat.cast_pos.mpr (by omega)) (saddleScale_pos hA hz)
        have hterms (i : Fin s) :
            (fun n => a i.succ • branchIntegral (s + 1) m A z (branchLabel (s + 1) i.succ) n) =o[atTop]
              branchIntegral (s + 1) m A z (branchLabel (s + 1) 0) := by
          have hrate : -(s + 1 : ℕ) * saddleScale (s + 1) A z *
              (Phase.rho (branchAngle (s + 1) i.succ)).re <
                (s + 1 : ℕ) * saddleScale (s + 1) A z := by nlinarith [rho_re_gt_neg_one (hθ i)]
          have h := ((branch_hasLogNormGrowth hr hA hz m i.succ).isLittleO (by omega) hb hrate).const_mul_left (fun _ : Fin (s + 1) => a i.succ)
          exact h
        have hsmall : (fun n => ∑ i : Fin s, a i.succ •
            branchIntegral (s + 1) m A z (branchLabel (s + 1) i.succ) n) =o[atTop]
              branchIntegral (s + 1) m A z (branchLabel (s + 1) 0) := by
          have h := Asymptotics.IsLittleO.sum (s := Finset.univ) (fun i _ => hterms i)
          convert h using 1
          funext n
          simp only [Finset.sum_apply]
        have hcomb : HasLogNormGrowth (s + 1) (commonScale (s + 1) m A z)
            ((s + 1 : ℕ) * saddleScale (s + 1) A z)
            (fun n => ∑ i, a i • branchIntegral (s + 1) m A z (branchLabel (s + 1) i) n) := by
          have h := hb.add_smaller hr hsmall ha0
          convert h using 1
          funext n
          rw [Fin.sum_univ_succ]
        refine ⟨hcomb.choose_spec.2.mono (fun _ hn => norm_pos_iff.mp hn.1), fun N => ?_⟩
        exact (recessive_hasLogNormGrowth hr hA hz m).superpolynomial_separation (by omega) hcomb
          (by linarith : -(s + 1 : ℕ) * saddleScale (s + 1) A z <
            (s + 1 : ℕ) * saddleScale (s + 1) A z) N
    · exact offCut_stronglyRecessive hr le_rfl hA hz m (branchLabel (s + 1)) (branchAngle (s + 1))
        (fun i => branchAngle_mem_principal (by omega) i (Or.inl (by omega)))
        (fun i => branchAngle_relation (by omega) i) (branchAngle_injective (by omega)) a ha
        (fun i hi he => hi (hsupport i he))

end ThisWork.HigherRank
