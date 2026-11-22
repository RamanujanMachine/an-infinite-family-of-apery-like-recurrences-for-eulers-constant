module

public import ThisWork.HigherRank.PositiveSeries

/-! The positive residue series for the fourth rank-four mode.
Its summation saddle is positive, avoiding a logarithm at the negative-real
Mellin–Barnes saddle. The contour-to-series identification is a separate task. -/

@[expose] public section
namespace ThisWork.HigherRank

open Filter
open scoped Topology

noncomputable abbrev positiveTerm (A : Fin 3 → ℝ) (z : ℝ) (n k : ℕ) : ℝ :=
  PositiveSeries.term 3 A z n k

noncomputable abbrev positiveRatio (A : Fin 3 → ℝ) (z : ℝ) (n k : ℕ) : ℝ :=
  PositiveSeries.ratio 3 A z n k

theorem positiveTerm_pos {A : Fin 3 → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n k : ℕ) :
    0 < positiveTerm A z n k := PositiveSeries.term_pos hA hz n k

theorem positiveTerm_succ {A : Fin 3 → ℝ} (hA : ∀ i, 0 < A i)
    (z : ℝ) (n k : ℕ) :
    positiveTerm A z n (k + 1) =
      (z * ∏ i, (A i * n + k + 1)) / ((k : ℝ) + 1) ^ 4 * positiveTerm A z n k :=
  PositiveSeries.term_succ hA z n k

theorem positiveTerm_succ_normalized {A : Fin 3 → ℝ} (hA : ∀ i, 0 < A i)
    (z : ℝ) (n k : ℕ) :
    positiveTerm A z n (k + 1) = positiveRatio A z n k * positiveTerm A z n k :=
  PositiveSeries.term_succ_normalized hA z n k

theorem positiveRatio_tendsto (A : Fin 3 → ℝ) (z : ℝ) (n : ℕ) :
    Tendsto (positiveRatio A z n) atTop (𝓝 0) := PositiveSeries.ratio_tendsto 3 A z n

theorem positiveTerm_summable {A : Fin 3 → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n : ℕ) :
    Summable (positiveTerm A z n) := PositiveSeries.term_summable hA hz n

end ThisWork.HigherRank
