import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.VariableEnergy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

private theorem localized_coefficient_smooth
    {U : Set (Spacetime n)} (hU : IsOpen U)
    {q : Spacetime n → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {z : Spacetime n} (χ : ContDiffBump z) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun y => χ y * q y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport (fun w => χ w * q w)
  · have hyU := hχU (tsupport_mul_subset_left hy)
    exact χ.contDiff.contDiffAt.mul ((hq y hyU).contDiffAt (hU.mem_nhds hyU))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

theorem exists_local_principal_parabolic_coercivity
    {U : Set (Spacetime n)} (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    {z : Spacetime n} (hz : z ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, a i j z * ξ i * ξ j) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      ∀ (v : Spacetime n → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ ball z r →
        (∫ y, (timeDeriv v y) ^ 2) + (κ ^ 2 / 2) *
            (∫ y, ∑ i, ∑ j, (spatialSecond i j v y) ^ 2) ≤
          2 * (∫ y, (timeDeriv v y - ∑ i, ∑ j, a i j y * spatialSecond i j v y) ^ 2) := by
  let osc : Spacetime n → ℝ := fun y => ∑ i, ∑ j, (a i j y - a i j z) ^ 2
  have hc : ContinuousAt osc z := by
    have hcOn : ContinuousOn osc U := by
      apply continuousOn_finsetSum
      intro i hi
      apply continuousOn_finsetSum
      intro j hj
      exact ((ha i j).continuousOn.sub continuousOn_const).pow 2
    exact hcOn.continuousAt (hU.mem_nhds hz)
  have ho : osc z = 0 := by simp [osc]
  have hsmall : ∀ᶠ y in 𝓝 z, osc y < (κ / 2) ^ 2 := by
    exact hc.eventually (gt_mem_nhds (by rw [ho]; positivity))
  obtain ⟨δ, hδ, hδall⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hz) hsmall)
  let χ : ContDiffBump z :=
    { rIn := δ / 4
      rOut := δ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hχU : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro y hy
    exact (hδall ((mem_closedBall.mp hy).trans_lt (by change δ / 2 < δ; linarith))).1
  let a' : Fin n → Fin n → Spacetime n → ℝ := fun i j y => χ y * a i j y
  have ha' (i j : Fin n) : Continuous (a' i j) :=
    (localized_coefficient_smooth hU (ha i j) χ hχU).continuous
  have heq (i j : Fin n) {y : Spacetime n} (hy : y ∈ ball z (δ / 4)) :
      a' i j y = a i j y := by
    change χ y * a i j y = a i j y
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  refine ⟨δ / 4, by positivity, ?_, ?_⟩
  · intro y hy
    exact (hδall ((mem_closedBall.mp hy).trans_lt (by linarith))).1
  intro v hv hvc hvs
  have hosc : ∀ y ∈ tsupport v,
      (∑ i, ∑ j, (a' i j y - a i j z) ^ 2) ≤ (κ / 2) ^ 2 := by
    intro y hy
    simp_rw [heq _ _ (hvs hy)]
    exact le_of_lt (hδall ((mem_ball.mp (hvs hy)).trans (by linarith))).2
  have hbound := variable_principal_parabolic_coercivity hκ
    (show 2 * (κ / 2) ^ 2 < κ ^ 2 by nlinarith [sq_pos_of_pos hκ])
    hEll ha' hv hvc hosc
  have hweight : κ ^ 2 - 2 * (κ / 2) ^ 2 = κ ^ 2 / 2 := by ring
  rw [hweight] at hbound
  convert hbound using 1
  congr 2
  funext y
  by_cases hy : y ∈ tsupport v
  · simp_rw [heq _ _ (hvs hy)]
  · have hzero (i j : Fin n) : spatialSecond i j v y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hy (((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
        (tsupport_fderiv_apply_subset ℝ (spatialDirection j))) h)
    simp only [hzero, mul_zero, Finset.sum_const_zero]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
