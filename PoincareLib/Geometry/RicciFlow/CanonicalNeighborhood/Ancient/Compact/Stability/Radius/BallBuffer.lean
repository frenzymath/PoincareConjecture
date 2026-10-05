import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform containment margins for a compact family of core balls

In a proper metric space, a continuous compact family of closed balls
contained in an open set admits a uniform enlargement. The distance to
the closed complement attains its infimum, so the containment gives a
strict positive gap; compactness makes this gap uniform over the centers.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.CompactKappaCoreRadius

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X]

/-- A compact family of contained closed balls admits a common positive
additive enlargement. Only continuity on the compact center set is needed. -/
theorem exists_additive_closedBall_buffer
    {Y U : Set X} (hY : IsCompact Y) (hU : IsOpen U)
    {rho : X → ℝ} (hrho : ContinuousOn rho Y)
    (hball : ∀ y ∈ Y, closedBall y (rho y) ⊆ U) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ y ∈ Y, closedBall y (rho y + delta) ⊆ U := by
  rcases (Uᶜ).eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy x hx
    by_contra hxU
    have : x ∈ Uᶜ := hxU
    simp only [hempty, mem_empty_iff_false] at this
  have hgap : ∀ y ∈ Y, 0 < infDist y Uᶜ - rho y := by
    intro y hy
    obtain ⟨x, hx, hdist⟩ := hU.isClosed_compl.exists_infDist_eq_dist hne y
    have hlt : rho y < dist y x := by
      by_contra hle
      exact hx (hball y hy (by simpa only [mem_closedBall, dist_comm] using le_of_not_gt hle))
    rw [hdist]
    exact sub_pos.mpr hlt
  obtain ⟨delta, hdelta, hbound⟩ := hY.exists_forall_le'
    ((continuous_infDist_pt Uᶜ).continuousOn.sub hrho) hgap
  refine ⟨delta / 2, by positivity, ?_⟩
  intro y hy x hx
  by_contra hxU
  have hdist : dist y x ≤ rho y + delta / 2 := by
    simpa only [mem_closedBall, dist_comm] using hx
  have hnear : infDist y Uᶜ ≤ dist y x := infDist_le_dist_of_mem hxU
  have hmargin : delta ≤ infDist y Uᶜ - rho y := hbound y hy
  linarith

/-- Compactness also supplies a uniform multiplicative enlargement of the
contained closed balls. This is the form used for scalar-radius cap cores. -/
theorem exists_multiplicative_closedBall_buffer
    {Y U : Set X} (hY : IsCompact Y) (hU : IsOpen U)
    {rho : X → ℝ} (hrho : ContinuousOn rho Y)
    (hball : ∀ y ∈ Y, closedBall y (rho y) ⊆ U) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ y ∈ Y, closedBall y ((1 + delta) * rho y) ⊆ U := by
  obtain ⟨eta, heta, hbuffer⟩ := exists_additive_closedBall_buffer hY hU hrho hball
  obtain ⟨R, hR⟩ := hY.bddAbove_image hrho
  let B := max R 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨eta / B, div_pos heta hB, ?_⟩
  intro y hy
  apply Set.Subset.trans (closedBall_subset_closedBall ?_) (hbuffer y hy)
  have hrB : rho y ≤ B := (hR (mem_image_of_mem rho hy)).trans (le_max_left _ _)
  have hmul := mul_le_mul_of_nonneg_left hrB (div_pos heta hB).le
  have heq : (eta / B) * B = eta := div_mul_cancel₀ eta hB.ne'
  rw [heq] at hmul
  nlinarith

end PoincareMT.CompactKappaCoreRadius
