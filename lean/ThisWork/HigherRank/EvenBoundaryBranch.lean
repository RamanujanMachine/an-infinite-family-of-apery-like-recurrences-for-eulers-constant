module

public import ThisWork.HigherRank.BranchGrowth

/-! Recovery of the original boundary Fourier branch from the reflected
auxiliary vector and the strictly smaller off-cut branches. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Asymptotics
open scoped Topology

noncomputable def boundaryRemainder (r half : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (n : ℕ) : Fin r → ℂ :=
  ∑ i : Fin r, if i.val = 0 then 0 else
    ((-1 : ℂ) ^ i.val * ((r - 1).choose i.val : ℂ)) •
      branchIntegral r 0 A z ((half : ℤ) - i.val) n

theorem boundaryRemainder_isLittleO {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) :
    boundaryRemainder r half A z =o[atTop] boundaryIntegral r 0 A z := by
  have hhalf : r / 2 = half := by omega
  have hb := boundary_hasLogNormGrowth hr hA hz half hrh
  have hc : 0 < (r : ℝ) * saddleScale r A z :=
    mul_pos (Nat.cast_pos.mpr (by omega)) (saddleScale_pos hA hz)
  have hterms (i : Fin r) :
      (fun n => if i.val = 0 then (0 : Fin r → ℂ) else
        ((-1 : ℂ) ^ i.val * ((r - 1).choose i.val : ℂ)) •
          branchIntegral r 0 A z ((half : ℤ) - i.val) n) =o[atTop] boundaryIntegral r 0 A z := by
    by_cases hi : i.val = 0
    · simpa only [hi, ite_true] using (isLittleO_zero (boundaryIntegral r 0 A z) atTop)
    · have hθ := branchAngle_mem_principal (by omega : 0 < r) i (Or.inr (by omega))
      have hj : (r : ℝ) * branchAngle r i = -2 * Real.pi * (((half : ℤ) - i.val : ℤ) : ℝ) := by
        simpa only [branchLabel, hhalf] using branchAngle_relation (by omega : 0 < r) i
      have hg := offCut_hasLogNormGrowth hr hA hz 0 ((half : ℤ) - i.val) hθ hj
      have hrate : -(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r i)).re <
          (r : ℝ) * saddleScale r A z := by nlinarith [rho_re_gt_neg_one hθ]
      have ht := (hg.isLittleO (by omega : 1 < r) hb hrate).const_mul_left
        (fun _ : Fin r => (-1 : ℂ) ^ i.val * ((r - 1).choose i.val : ℂ))
      convert ht using 1
      funext n k
      simp only [hi, ite_false, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]

  have hs := Asymptotics.IsLittleO.sum (s := Finset.univ) (fun i _ => hterms i)
  convert hs using 1
  funext n
  simp only [Finset.sum_apply, boundaryRemainder]

theorem boundaryIntegral_fourier_split {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (z : ℝ) (n : ℕ) :
    (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) • boundaryIntegral r 0 A z n =
      branchIntegral r 0 A z half n + boundaryRemainder r half A z n := by
  classical
  rw [boundaryIntegral_fourier hr hA half hrh 0 z n]
  let zero : Fin r := ⟨0, hr⟩
  have h0 : ((-1 : ℂ) ^ zero.val * ((r - 1).choose zero.val : ℂ)) •
      branchIntegral r 0 A z ((half : ℤ) - zero.val) n = branchIntegral r 0 A z half n := by
    simp [zero]
  rw [← h0, boundaryRemainder]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zero)]
  rw [add_comm]
  congr 1
  calc
    _ = ∑ i ∈ Finset.univ.erase zero, if i.val = 0 then (0 : Fin r → ℂ) else
        ((-1 : ℂ) ^ i.val * ((r - 1).choose i.val : ℂ)) •
          branchIntegral r 0 A z ((half : ℤ) - i.val) n := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : i.val ≠ 0 := by
        intro he
        exact (Finset.mem_erase.mp hi).1 (Fin.ext he)
      simp only [hi0, ite_false]
    _ = _ := by
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro i _ hi
      have he : i = zero := by simpa using hi
      subst i
      simp only [zero, ite_true]

theorem evenBoundary_zeroCenter_hasLogNormGrowth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) :
    HasLogNormGrowth r (commonScale r 0 A z) ((r : ℝ) * saddleScale r A z)
      (branchIntegral r 0 A z half) := by
  have hB := boundary_hasLogNormGrowth hr hA hz half hrh
  have hR := (boundaryRemainder_isLittleO hr hA hz half hrh).neg_left
  have hL : (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hg := hB.add_smaller hr hR hL
  convert hg using 1
  funext n
  have he := boundaryIntegral_fourier_split (by omega : 0 < r) hA half hrh z n
  rw [he]
  simp only [add_neg_cancel_right]

end ThisWork.HigherRank
