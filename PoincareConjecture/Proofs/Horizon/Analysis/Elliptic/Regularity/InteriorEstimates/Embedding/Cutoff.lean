import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Profile

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_cutoff_derivative_bound {χ : E → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ A := by
  classical
  have hbounds : ∀ j : ℕ, ∃ A : ℝ, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ A := by
    intro j
    exact (hc.iteratedFDeriv (𝕜 := ℝ) j).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose A hA using hbounds
  refine ⟨∑ j ∈ Finset.range (k + 1), max 0 (A j),
    Finset.sum_nonneg (fun j hj => le_max_left _ _), ?_⟩
  intro j hj x
  exact ((hA j x).trans (le_max_right _ _)).trans
    (Finset.single_le_sum (fun i hi => le_max_left _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem exists_fixed_cutoff_profile_bound {x₀ : E} {R : ℝ} (hR : 0 < R) (k : ℕ) :
    ∃ χ : E → ℝ, ∃ A : ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball x₀ R ∧
      EqOn χ (fun _ => 1) (Metric.ball x₀ (R / 2)) ∧ 0 ≤ A ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        derivativeProfile 2 (Metric.ball x₀ R) k (fun x => χ x * u x) ≤
          ENNReal.ofReal A * derivativeProfile 2 (Metric.ball x₀ R) k u := by
  let χ : ContDiffBump x₀ :=
    ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  obtain ⟨A, hA, hbound⟩ :=
    exists_cutoff_derivative_bound χ.contDiff χ.hasCompactSupport k
  refine ⟨χ, cutoffMultiplier k A, χ.contDiff, χ.hasCompactSupport, ?_, ?_,
    cutoffMultiplier_nonneg k hA, ?_⟩
  · rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  · intro x hx
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  · intro u hu
    exact derivativeProfile_mul_le isOpen_ball (by norm_num) k χ.contDiff hu hA
      (fun j hj x hx => hbound j hj x)

end Poincare.Analysis.Elliptic.InteriorEstimates
