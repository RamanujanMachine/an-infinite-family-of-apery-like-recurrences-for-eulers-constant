module

public import ThisWork.HigherRank.BoundaryMomentBounds
public import ThisWork.HigherRank.BoundaryMomentConvergence
public import ThisWork.HigherRank.WeightedIntegralBounds

/-! Upper growth bounds for all polynomial moments on the boundary banks. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem boundary_moment_bank_upper {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, y = 1 ∨ y = -1 →
      ‖∫ x in Iic (-(6 * (r : ℝ))),
        (-((x : ℂ) + (y : ℂ) * Complex.I)) ^ k *
          boundaryKernel r 0 A z n ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        commonScale r 0 A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n +
          C * (largeScale r n * smallParameter r n)) := by
  let L := -(6 * (r : ℝ))
  have hL : L < 1 := by dsimp only [L]; have hp : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); linarith
  obtain ⟨T₀, hT₀, htail⟩ := uniform_reflected_real_tail_decay hr hA 0 z 2
  obtain ⟨Tp, hTp⟩ := eventually_atTop.mp
    (Analytic.eventually_shifted_pow_le_exp (D := 1) (by norm_num) k)
  let T := max T₀ (max Tp (|L| + 1))
  have hT : 1 ≤ T := hT₀.trans (le_max_left _ _)
  obtain ⟨C, hC, hwindow⟩ := uniform_reflectedKernel_real_window_upper hr hA hz
    (zero_lt_one.trans_le hT) hL 0
  let B := 2 * Real.pi * Real.exp 1 + Real.pi / 4
  let K := max ((1 + T + |L|) ^ k) (Real.exp T)
  let D := 1 + |L| + T
  let U := B * K * D
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 ≤ K := (Real.exp_pos _).le.trans (le_max_right _ _)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  let F := U + ((k + 1 : ℕ) : ℝ) * (2 * ((r : ℝ) + 1))
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨C + F, by positivity, ?_⟩
  filter_upwards [htail, hwindow, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with n hnT hnW hR1 hn1 y hy
  let R := largeScale r n
  let M := commonScale r 0 A z n * Real.exp ((r : ℝ) * saddleScale r A z * R +
    C * (largeScale r n * smallParameter r n))
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hM : 0 ≤ M := (mul_pos (commonScale_pos hA hz 0 n) (Real.exp_pos _)).le
  have hTL : |L| + 1 ≤ T := (le_max_right Tp (|L| + 1)).trans (le_max_right _ _)
  have hab : -(R * T) ≤ L := by
    nlinarith [neg_le_abs L, mul_le_mul_of_nonneg_right hR1 (zero_lt_one.trans_le hT).le]
  have hi : IntegrableOn (fun x : ℝ => (-((x : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      boundaryKernel r 0 A z n ((x : ℂ) + (y : ℂ) * Complex.I)) (Iic L) := by
    have hy1 : |y| = 1 := by rcases hy with rfl | rfl <;> norm_num
    simpa only [Nat.cast_zero, zero_mul, zero_sub] using
      integrableOn_weighted_boundary_horizontal (by omega : 0 < r) hA half hrh 0 z n k hL hy1
  have hb := integral_polynomial_weight_le_window_tail k hR1 hT hB hM hab hi
    (Q := fun x => ‖reflectedKernel r 0 A z n (x : ℂ)‖) (fun _ => norm_nonneg _)
    (fun x hx => weighted_boundary_bank_le (by omega : 0 < r) hA z n k hx hy)
    (fun x hx => hnW x hx.1 hx.2)
    (fun t ht => by
      have hk := hnT T (le_max_left _ _) t ht
      have he : ‖reflectedKernel r 0 A z n (-(R : ℂ) * (T : ℂ))‖ ≤ M := by
        rw [neg_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
        exact hnW (-(R * T)) le_rfl hab
      simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using
        hk.trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le))
    (fun t ht => by
      simpa only [add_comm] using hTp t
        (((le_max_left Tp (|L| + 1)).trans (le_max_right _ _)).trans ht))
  have hlen : 1 + L + R * T ≤ D * R := by
    dsimp only [D]
    nlinarith [le_abs_self L, mul_le_mul_of_nonneg_right hR1 (show 0 ≤ 1 + |L| by positivity)]
  have hRn : R ≤ (n : ℝ) := Real.rpow_le_self_of_one_le (by exact_mod_cast hn1)
    (by linarith [div_nonneg zero_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : 1 - 1 / (r : ℝ) ≤ 1)
  have hfactor : U * R ^ (k + 1) ≤ Real.exp (F * (largeScale r n * smallParameter r n)) := by
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    calc
      _ ≤ U * (n : ℝ) ^ (k + 1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRn _) hU
      _ = U * Real.exp (((k + 1 : ℕ) : ℝ) * Real.log (n : ℝ)) := by rw [Real.exp_nat_mul, Real.exp_log hn0]
      _ ≤ U * Real.exp (((k + 1 : ℕ) : ℝ) * (1 + Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) (k + 1)])) hU
      _ ≤ _ := polynomial_le_exp_errorScale hr hn1 hU (by positivity)
  calc
    _ ≤ B * R ^ k * K * M * (1 + L + R * T) := hb
    _ ≤ B * R ^ k * K * M * (D * R) := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = M * (U * R ^ (k + 1)) := by dsimp only [U]; rw [pow_succ]; ring
    _ ≤ M * Real.exp (F * (largeScale r n * smallParameter r n)) := mul_le_mul_of_nonneg_left hfactor hM
    _ = _ := by dsimp only [M, R]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end ThisWork.HigherRank
