module
public import ThisWork.Trajectory.KernelConjugation
public import ThisWork.OriginalMomentLimits
/-! The second growing branch is the complex conjugate of the first. -/
public section
namespace ThisWork.Analytic
open Set MeasureTheory
open scoped ComplexConjugate

theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (∫ t in a..b, conj (f t)) = conj (∫ t in a..b, f t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

theorem hankelIntegral_conj (f : ℂ → ℂ) (r h : ℝ) :
    hankelIntegral r h (fun x => conj (f (conj x))) = -conj (hankelIntegral r h f) := by
  have hl : (∫ u in Iic r, conj (f (conj ((u : ℂ) - (h : ℂ) * Complex.I)))) =
      conj (∫ u in Iic r, f ((u : ℂ) + (h : ℂ) * Complex.I)) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_neg_eq_add, integral_conj]
  have hu : (∫ u in Iic r, conj (f (conj ((u : ℂ) + (h : ℂ) * Complex.I)))) =
      conj (∫ u in Iic r, f ((u : ℂ) - (h : ℂ) * Complex.I)) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, ← sub_eq_add_neg, integral_conj]
  have hv : (∫ v in -h..h, Complex.I * conj (f (conj ((r : ℂ) + (v : ℂ) * Complex.I)))) =
      -conj (∫ v in -h..h, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) := by
    have he : (fun v : ℝ => Complex.I * conj (f (conj ((r : ℂ) + (v : ℂ) * Complex.I)))) =
        (fun v : ℝ => (fun t : ℝ => Complex.I * conj (f ((r : ℂ) + (t : ℂ) * Complex.I))) (-v)) := by
      funext v
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg, neg_mul]
    rw [he, intervalIntegral.integral_comp_neg (fun t : ℝ => Complex.I * conj (f ((r : ℂ) + (t : ℂ) * Complex.I))),
      neg_neg, ← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [map_mul, Complex.conj_I, neg_mul, neg_neg]
  unfold ThisWork.hankelIntegral
  dsimp only
  rw [hl, hu, hv]
  simp only [map_add, map_sub]
  ring

end ThisWork.Analytic

namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology ComplexConjugate

theorem kernel_two_eq_conj_one (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (x : ℂ) :
    kernel m d A₁ A₂ z .two n x = conj (kernel m d A₁ A₂ z .one n (conj x)) := by
  rw [kernel_eq_twist m d A₁ A₂ z .two n x, kernel_eq_twist m d A₁ A₂ z .one n (conj x),
    map_mul, ← Complex.exp_conj, kernel_three_conj, Complex.conj_conj]
  congr 1
  congr 1
  simp only [map_mul, Complex.conj_conj, twist_one, twist_two, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

theorem branchIntegral_two_eq_conj_one (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (k : Fin 3) :
    branchIntegral m d A₁ A₂ z .two n k = conj (branchIntegral m d A₁ A₂ z .one n k) := by
  have he : (fun x : ℂ => ((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z .two n x) =
      (fun x : ℂ => conj (((m : ℂ) * n - conj x) ^ k.val * kernel m d A₁ A₂ z .one n (conj x))) := by
    funext x
    rw [kernel_two_eq_conj_one]
    simp only [map_mul, map_pow, map_sub, map_natCast, Complex.conj_conj]
  have hcf : conj cauchyFactor = -cauchyFactor := by
    simp [cauchyFactor, map_mul, Complex.conj_I]
    exact map_ofNat (starRingEnd ℂ) 2
  change cauchyFactor * hankelIntegral (1 / 2) 1 _ = conj (cauchyFactor * hankelIntegral (1 / 2) 1 _)
  rw [he, hankelIntegral_conj (fun x => ((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z .one n x), map_mul, hcf]
  ring

theorem norm_branchIntegral_two_eq_one (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) :
    ‖branchIntegral m d A₁ A₂ z .two n‖ = ‖branchIntegral m d A₁ A₂ z .one n‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    rw [branchIntegral_two_eq_conj_one, Complex.norm_conj]
    exact norm_le_pi_norm _ k
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    have h := norm_le_pi_norm (branchIntegral m d A₁ A₂ z .two n) k
    rw [branchIntegral_two_eq_conj_one, Complex.norm_conj] at h
    exact h

end ThisWork.Trajectory
