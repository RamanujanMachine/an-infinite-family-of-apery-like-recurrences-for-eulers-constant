module

public import ThisWork.PhaseApproximation
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Compact parameter families obtained by adjoining the uniform limit of a sequence. -/

@[expose] public section

namespace ThisWork

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

/-- The exact saddle equations and their limit form a jointly continuous,
holomorphic family on a common disk with compact parameter space. -/
theorem eventually_compact_equation_family {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) :
    ∀ᶠ N : ℕ in atTop,
      ContinuousOn (Function.uncurry (sequenceFamily
        (fun m => exactSaddleEquation α₁ α₂ j (m + N))
        (limitingEquation j (saddleScale α₁ α₂))))
        (ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8) ×ˢ univ) ∧
      ∀ z : OnePoint ℕ, DifferentiableOn ℂ
        (fun s => sequenceFamily (fun m => exactSaddleEquation α₁ α₂ j (m + N))
          (limitingEquation j (saddleScale α₁ α₂)) s z)
        (ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_differentiableOn_exactSaddleEquation h₁ h₂ j)
  filter_upwards [eventually_ge_atTop N₀] with N hNge
  have hN := fun n (hn : N ≤ n) => hN₀ n (hNge.trans hn)
  have hc := saddleScale_pos h₁ h₂
  have hsub : closedBall ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8) ⊆
      ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4) :=
    closedBall_subset_ball (by linarith)
  have hlim : TendstoUniformlyOn (fun m => exactSaddleEquation α₁ α₂ j (m + N))
      (limitingEquation j (saddleScale α₁ α₂)) atTop
      (closedBall ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8)) :=
    ((exactSaddleEquation_tendsto_uniform_disk h₁ h₂ j).mono
      (fun s hs => ball_subset_closedBall (hsub hs))).seq_tendstoUniformlyOn
        (fun m => m + N) (tendsto_add_atTop_nat N)
  have hcont := continuousOn_sequenceFamily (isCompact_closedBall _ _)
    (fun m => ((hN (m + N) (Nat.le_add_left N m)).mono hsub).continuousOn)
    (((differentiableOn_limitingEquation_disk hc j).mono hsub).continuousOn) hlim
  refine ⟨hcont.mono (Set.prod_mono ball_subset_closedBall Subset.rfl), ?_⟩
  intro z
  cases z with
  | infty =>
    exact (differentiableOn_limitingEquation_disk hc j).mono
      (fun s hs => hsub (ball_subset_closedBall hs))
  | coe m =>
    exact (hN (m + N) (Nat.le_add_left N m)).mono
      (fun s hs => hsub (ball_subset_closedBall hs))

end ThisWork
