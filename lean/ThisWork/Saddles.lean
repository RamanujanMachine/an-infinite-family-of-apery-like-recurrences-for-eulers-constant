module

public import ThisWork.Scales
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-! The distinct limiting saddle locations in every positive rank. -/

@[expose] public section
namespace ThisWork

noncomputable def root (r : ℕ) (j : Fin r) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / r) ^ j.val

theorem root_injective {r : ℕ} (hr : 0 < r) : Function.Injective (root r) := by
  intro i j hij
  apply Fin.ext
  exact (Complex.isPrimitiveRoot_exp r hr.ne').pow_inj i.isLt j.isLt hij

theorem norm_root {r : ℕ} (hr : 0 < r) (j : Fin r) : ‖root r j‖ = 1 := by
  rw [root, norm_pow, (Complex.isPrimitiveRoot_exp r hr.ne').norm'_eq_one hr.ne', one_pow]

theorem root_pow {r : ℕ} (hr : 0 < r) (j : Fin r) : root r j ^ r = 1 := by
  rw [root, ← pow_mul, Nat.mul_comm j.val r, pow_mul,
    (Complex.isPrimitiveRoot_exp r hr.ne').pow_eq_one, one_pow]

theorem root_re_lt_one {r : ℕ} (hr : 0 < r) (j : Fin r) (hj : j.val ≠ 0) :
    (root r j).re < 1 := by
  have hle : (root r j).re ≤ 1 := (Complex.re_le_norm _).trans (norm_root hr j).le
  have hne : root r j ≠ 1 :=
    (Complex.isPrimitiveRoot_exp r hr.ne').pow_ne_one_of_pos_of_lt hj j.isLt
  apply lt_of_le_of_ne hle
  intro hre
  have him : (root r j).im = 0 := Complex.abs_re_eq_norm.mp (by
    rw [hre, norm_root hr j, abs_one])
  apply hne
  apply Complex.ext
  · simpa using hre
  · simpa using him

theorem root_eq_neg_one_iff {r : ℕ} (hr : 0 < r) (j : Fin r) :
    root r j = -1 ↔ 2 * j.val = r := by
  have hp := Complex.isPrimitiveRoot_exp r hr.ne'
  constructor
  · intro hj
    have hj0 : j.val ≠ 0 := by
      intro he
      norm_num [root, he] at hj
    have hpow : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / r) ^ (2 * j.val) = 1 := by
      rw [Nat.mul_comm 2 j.val, pow_mul]
      change root r j ^ 2 = 1
      rw [hj]
      norm_num
    obtain ⟨k, hk⟩ := hp.dvd_of_pow_eq_one _ hpow
    have hk0 : 0 < k := by
      by_contra h
      have he : k = 0 := by omega
      simp only [he, Nat.mul_zero] at hk
      omega
    have hk2 : k < 2 := by
      by_contra h
      have hm := Nat.mul_le_mul_left r (show 2 ≤ k by omega)
      nlinarith [j.isLt]
    have he : k = 1 := by omega
    simpa only [he, Nat.mul_one] using hk
  · intro hj
    have hsq : root r j ^ 2 = 1 := by
      rw [root, ← pow_mul, Nat.mul_comm j.val 2, hj, hp.pow_eq_one]
    have hj0 : j.val ≠ 0 := by omega
    exact (sq_eq_one_iff.mp hsq).resolve_left
      (hp.pow_ne_one_of_pos_of_lt hj0 j.isLt)

theorem root_mem_slitPlane_iff {r : ℕ} (hr : 0 < r) (j : Fin r) :
    root r j ∈ Complex.slitPlane ↔ 2 * j.val ≠ r := by
  constructor
  · intro hs he
    rw [(root_eq_neg_one_iff hr j).mpr he] at hs
    norm_num [Complex.mem_slitPlane_iff] at hs
  · intro hj
    have hne : root r j ≠ -1 := by
      intro he
      exact hj ((root_eq_neg_one_iff hr j).mp he)
    rw [Complex.mem_slitPlane_iff]
    by_contra h
    push Not at h
    have habs : |(root r j).re| = 1 :=
      (Complex.abs_re_eq_norm.mpr h.2).trans (norm_root hr j)
    rw [abs_of_nonpos h.1] at habs
    apply hne
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.one_re]
      linarith
    · simpa using h.2

end ThisWork
