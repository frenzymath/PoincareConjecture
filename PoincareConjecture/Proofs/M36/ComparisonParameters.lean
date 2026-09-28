import PoincareConjecture.Proofs.M36.ComparisonSmoothJets
import PoincareConjecture.Proofs.M36.ComparisonChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped ContDiff Topology

namespace PoincareConjecture.M36

theorem exists_standardComparison_dilation (g₀ : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ a : ℝ, 1 < a ∧ a < 2 ∧ ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (standardDilationError g₀ a) x‖ < eta := by
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp
    (standardDilationError_jets_eventually_small g₀ hK m heta)
  let b := min d 1 / 2
  have hb : 0 < b := div_pos (lt_min hd zero_lt_one) (by norm_num)
  have hbd : b < d := by
    have h := min_le_left d 1
    dsimp [b]
    linarith only [h, hd]
  have hb1 : b < 1 := by
    have h := min_le_right d 1
    dsimp [b]
    linarith only [h]
  refine ⟨1 + b, by linarith only [hb], by linarith only [hb1], hbound ?_⟩
  simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hb] using hbd

theorem standardComparison_radial_margin (g₀ : StandardInitialMetric)
    {a R : ℝ} (ha : 1 < a) (hR : 0 < R) :
    R < radialArclength g₀ (a * radialEuclideanRadius g₀ R) := by
  have hrho := (radialEuclideanRadius_pos_iff g₀ R).mpr hR
  calc
    R = radialArclength g₀ (radialEuclideanRadius g₀ R) :=
      (radialArclength_euclideanRadius g₀ R).symm
    _ < radialArclength g₀ (a * radialEuclideanRadius g₀ R) :=
      (radialArclength_strictMono g₀) (by nlinarith only [ha, hrho])

theorem exists_standardComparison_image_threshold (C : ℝ)
    {R S : ℝ} (hRS : R < S) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ delta →
      0 < 1 - 6 * epsilon ∧
        R < Real.sqrt ((1 - 6 * epsilon) * Real.exp (-2 * C * epsilon)) * S := by
  let f : ℝ → ℝ := fun e => Real.sqrt ((1 - 6 * e) * Real.exp (-2 * C * e)) * S
  have hf : Continuous f :=
    (Real.continuous_sqrt.comp
      ((continuous_const.sub (continuous_const.mul continuous_id)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).mul continuous_const
  have hbase : R < f 0 := by simpa [f] using hRS
  have hevent : ∀ᶠ e in nhds (0 : ℝ), R < f e ∧ e < 1 / 6 :=
    (hf.continuousAt.eventually (lt_mem_nhds hbase)).and
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 6))
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨d / 2, by positivity, ?_⟩
  intro epsilon hepsilon he
  have hdist : dist epsilon 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hepsilon]
    linarith only [he, hd]
  have h := hbound hdist
  exact ⟨by linarith only [h.2], h.1⟩

end PoincareConjecture.M36
