import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialJets
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open Set MeasureTheory Metric
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Parabolic.WeakRegularity.Canonical

theorem exists_global_l2_spatial_weak_derivatives
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hEll : C.IsUniformlyEllipticOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) {z : Spacetime n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      ∃ g : Fin n → Spacetime n → ℝ,
        (∀ i, MemLp (g i) 2 volume) ∧ (∀ i, HasCompactSupport (g i)) ∧
        ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * g i y) =
            -(∫ y in ball z r, spatialDeriv i φ y * u y) := by
  obtain ⟨r, hr, hclosed, _, V, hweak⟩ :=
    exists_local_spatial_weak_derivatives hU hC hEll hu hw hz
  let g : Fin n → Spacetime n → ℝ := fun i => (ball z r).indicator (fun y => V i y)
  have hgm (i : Fin n) : MemLp (g i) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp (V i))
  have hgc (i : Fin n) : HasCompactSupport (g i) := by
    apply (isCompact_closedBall z r).of_isClosed_subset (isClosed_tsupport (g i))
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra hn
    have hyb : y ∉ ball z r := fun h => hn (ball_subset_closedBall h)
    exact hy (indicator_of_notMem hyb _)
  refine ⟨r, hr, hclosed, g, hgm, hgc, ?_⟩
  intro i φ hφ hφc hφs
  calc
    (∫ y in ball z r, φ y * g i y) = ∫ y in ball z r, φ y * V i y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      rw [show g i y = V i y from indicator_of_mem hy _]
    _ = _ := hweak i φ hφ hφc hφs

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
