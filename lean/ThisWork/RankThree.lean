module

public import ThisWork.MellinBarnesAsymptotics

/-! Rank-three compatibility corollaries of the arbitrary-rank theorem.
The three traditional labels are retained; there is no separate saddle-point
or contour proof in this module. Equal positive lower slopes use the same
specialization with arbitrary `b`. -/

@[expose] public section
namespace ThisWork.RankThree

open Set Filter
open scoped Topology

inductive Branch where
  | one | two | three
  deriving DecidableEq

def branchIndex : Branch → ℤ
  | .one => 1
  | .two => -1
  | .three => 0

def branchPosition : Branch → Fin 3
  | .one => 0
  | .two => 2
  | .three => 1

theorem branchPosition_injective : Function.Injective branchPosition := by
  intro i j hij
  cases i <;> cases j <;> simp_all [branchPosition]

theorem branchPosition_label (j : Branch) :
    ThisWork.branchLabel 3 (branchPosition j) = branchIndex j := by
  cases j <;> norm_num [ThisWork.branchLabel, branchPosition, branchIndex]

noncomputable def rho (j : Branch) : ℂ :=
  ThisWork.Phase.rho (ThisWork.branchAngle 3 (branchPosition j))

noncomputable def saddleScale (A₁ A₂ z : ℝ) : ℝ :=
  ThisWork.saddleScale 3 ![A₁, A₂] z

noncomputable def gammaScale (A₁ A₂ : ℝ) (n : ℕ) : ℝ :=
  ThisWork.gammaScale 3 ![A₁, A₂] n

noncomputable def equalBranchIntegral (b : ℕ) (A₁ A₂ z : ℝ) (j : Branch) : ℕ → Fin 3 → ℂ :=
  ThisWork.branchIntegral 3 b ![A₁, A₂] z (branchIndex j)

noncomputable def branchIntegral (A₁ A₂ z : ℝ) (j : Branch) : ℕ → Fin 3 → ℂ :=
  equalBranchIntegral 1 A₁ A₂ z j

noncomputable def equalScale (b : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) : ℝ :=
  gammaScale A₁ A₂ n * z ^ (b * n)

def Lemma8NormEstimate (A₁ A₂ z : ℝ) : Prop :=
  ∀ j : Branch, ∃ C ≥ 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ E : ℝ,
    |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
    ‖branchIntegral A₁ A₂ z j n‖ = gammaScale A₁ A₂ n * z ^ n *
      Real.exp (-3 * saddleScale A₁ A₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)

def Lemma8 (A₁ A₂ z : ℝ) : Prop :=
  Lemma8NormEstimate A₁ A₂ z ∧ LinearIndependent ℂ (branchIntegral A₁ A₂ z)

private theorem gaps_pos {A₁ A₂ : ℝ} (h₁ : 0 < A₁) (h₂ : 0 < A₂) :
    ∀ i : Fin 2, 0 < (![A₁, A₂] : Fin 2 → ℝ) i := by
  intro i
  fin_cases i
  · exact h₁
  · exact h₂

theorem equal_normEstimate (b : ℕ) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (j : Branch) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
      ‖equalBranchIntegral b A₁ A₂ z j n‖ = equalScale b A₁ A₂ z n *
        Real.exp (-3 * saddleScale A₁ A₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E) := by
  obtain ⟨C, hC, hbound⟩ := ThisWork.branch_normEstimate (r := 3) (by norm_num)
    (gaps_pos h₁ h₂) hz b (branchPosition j)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  refine ⟨C, hC, N, fun n hn => ?_⟩
  obtain ⟨E, hE, hval⟩ := hN n hn
  refine ⟨E, ?_, ?_⟩
  · norm_num at hE ⊢
    exact hE
  · simpa only [equalBranchIntegral, branchPosition_label, equalScale, gammaScale,
      saddleScale, rho, ThisWork.commonScale, ThisWork.largeScale,
      Nat.cast_ofNat, show (1 - 1 / (3 : ℝ)) = 2 / 3 by norm_num] using hval

theorem equal_linearIndependent (b : ℕ) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    LinearIndependent ℂ (equalBranchIntegral b A₁ A₂ z) := by
  have h := (ThisWork.branch_linearIndependent (r := 3) (by norm_num)
    (gaps_pos h₁ h₂) hz b).comp branchPosition branchPosition_injective
  change LinearIndependent ℂ (fun j => ThisWork.branchIntegral 3 b ![A₁, A₂] z (branchIndex j))
  simpa only [Function.comp_def, branchPosition_label] using h

theorem lemma8_normEstimate {A₁ A₂ z : ℝ} (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    Lemma8NormEstimate A₁ A₂ z := by
  simpa only [Lemma8NormEstimate, branchIntegral, equalScale, one_mul] using
    equal_normEstimate 1 h₁ h₂ hz

theorem branchIntegral_linearIndependent {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    LinearIndependent ℂ (branchIntegral A₁ A₂ z) := equal_linearIndependent 1 h₁ h₂ hz

theorem lemma8 {A₁ A₂ z : ℝ} (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    Lemma8 A₁ A₂ z := ⟨lemma8_normEstimate h₁ h₂ hz, branchIntegral_linearIndependent h₁ h₂ hz⟩

theorem lemma8_one {A₁ A₂ : ℝ} (h₁ : 0 < A₁) (h₂ : 0 < A₂) : Lemma8 A₁ A₂ 1 :=
  lemma8 h₁ h₂ (by norm_num)

noncomputable def dominantCombination (V : Branch → ℕ → Fin 3 → ℂ)
    (a : Fin 2 → ℂ) (n : ℕ) : Fin 3 → ℂ := a 0 • V .one n + a 1 • V .two n

def StronglyRecessiveInSpan (V : Branch → ℕ → Fin 3 → ℂ) : Prop :=
  ∀ a : Fin 2 → ℂ, a 0 ≠ 0 ∨ a 1 ≠ 0 →
    (∀ᶠ n : ℕ in atTop, dominantCombination V a n ≠ 0) ∧
    ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N *
      (‖V .three n‖ / ‖dominantCombination V a n‖)) atTop (𝓝 0)

theorem equal_stronglyRecessive (b : ℕ) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    StronglyRecessiveInSpan (equalBranchIntegral b A₁ A₂ z) := by
  intro a ha
  let coefficients : Fin 3 → ℂ := ![a 0, 0, a 1]
  have hcoeff : coefficients ≠ 0 := by
    intro he
    rcases ha with ha | ha
    · exact ha (by simpa only [coefficients, Matrix.cons_val_zero, Pi.zero_apply] using congrFun he 0)
    · have h := congrFun he (2 : Fin 3)
      change a 1 = 0 at h
      exact ha h
  have hsupport (i : Fin 3) (hi : ThisWork.branchLabel 3 i = 0) : coefficients i = 0 := by
    fin_cases i
    · norm_num [ThisWork.branchLabel] at hi
    · rfl
    · norm_num [ThisWork.branchLabel] at hi
  have h := ThisWork.branch_combination_stronglyRecessive (r := 3) (by norm_num)
    (gaps_pos h₁ h₂) hz b coefficients hcoeff hsupport
  have hsum (n : ℕ) :
      (∑ i, coefficients i • ThisWork.branchIntegral 3 b ![A₁, A₂] z (ThisWork.branchLabel 3 i) n) =
        dominantCombination (equalBranchIntegral b A₁ A₂ z) a n := by
    simp [Fin.sum_univ_three, coefficients, dominantCombination, equalBranchIntegral,
      ThisWork.branchLabel, branchIndex]
  simpa only [hsum, equalBranchIntegral, branchIndex] using h

theorem branchIntegral_stronglyRecessive {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    StronglyRecessiveInSpan (branchIntegral A₁ A₂ z) := equal_stronglyRecessive 1 h₁ h₂ hz

theorem equal_lemma8 (b : ℕ) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    (∀ j : Branch, ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
      ‖equalBranchIntegral b A₁ A₂ z j n‖ = equalScale b A₁ A₂ z n *
        Real.exp (-3 * saddleScale A₁ A₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)) ∧
      LinearIndependent ℂ (equalBranchIntegral b A₁ A₂ z) :=
  ⟨equal_normEstimate b h₁ h₂ hz, equal_linearIndependent b h₁ h₂ hz⟩

theorem lemma8_with_strongRecessiveness {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    Lemma8 A₁ A₂ z ∧ StronglyRecessiveInSpan (branchIntegral A₁ A₂ z) :=
  ⟨lemma8 h₁ h₂ hz, branchIntegral_stronglyRecessive h₁ h₂ hz⟩

end ThisWork.RankThree

namespace ThisWork

-- Preserve the former theorem entry points as aliases of specialization corollaries.
export RankThree (Lemma8NormEstimate Lemma8 lemma8_normEstimate
  branchIntegral_linearIndependent lemma8 lemma8_one
  branchIntegral_stronglyRecessive lemma8_with_strongRecessiveness)

end ThisWork
