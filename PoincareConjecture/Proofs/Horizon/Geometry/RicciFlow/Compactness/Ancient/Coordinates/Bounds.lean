import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.TimeWindows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space

theorem eventually_referenceNormalChartCover_extension
    {n : ℕ} {T' T S' S : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hS : S' < 0 ∧ 0 < S)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 < b) :
    ∃ a' b' : ℝ, 0 < a' ∧ 0 < b' ∧ ∀ᶠ k in atTop,
      ∀ cover : NormalChartCover (H.sequence.flow k).metricAt
          (H.sequence.flow k).base S' S A R ρ a b N,
        ∃ wide : NormalChartCover (H.sequence.flow k).metricAt
            (H.sequence.flow k).base T' T A R ρ a' b' N,
          wide.chart = cover.chart := by
  have hR : 0 < R := by linarith
  obtain ⟨K, hK, hcurv⟩ := H.all_time_curvature_control_on_zero_ball
    (A + R) (add_pos hA hR)
  let a' := Real.exp (-(2 * ((n : ℝ) ^ 3 * K)) * (T - T')) * a
  let b' := Real.exp ((2 * ((n : ℝ) ^ 3 * K)) * (T - T')) * b
  refine ⟨a', b', mul_pos (Real.exp_pos _) ha, mul_pos (Real.exp_pos _) hb, ?_⟩
  filter_upwards [hcurv] with k hk
  intro cover
  exact ⟨cover.extendTimeOfCurvatureBoundOnBall hS H.time_bounds (Subset.refl _)
    hA.le hR.le hρR ha.le hb.le hK hk, rfl⟩

theorem eventually_referenceNormalChartCover_ellipticity
    {n : ℕ} {T' T S' S : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hS : S' < 0 ∧ 0 < S)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 < b) :
    ∃ a' b' : ℝ, 0 < a' ∧ 0 < b' ∧ ∀ᶠ k in atTop,
      ∀ cover : NormalChartCover (H.sequence.flow k).metricAt
          (H.sequence.flow k).base S' S A R ρ a b N,
        ∀ i, ∀ t ∈ Ioo T' T, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v,
          a' * ‖v‖ ^ 2 ≤ ((H.sequence.flow k).metricAt t).pullbackCoefficients
              (cover.chart i) x v v ∧
          ((H.sequence.flow k).metricAt t).pullbackCoefficients (cover.chart i) x v v ≤
            b' * ‖v‖ ^ 2 := by
  obtain ⟨a', b', ha', hb', hext⟩ :=
    H.eventually_referenceNormalChartCover_extension hS (N := N) hA hρ hρR ha hb
  refine ⟨a', b', ha', hb', ?_⟩
  filter_upwards [hext] with k hk
  intro cover
  obtain ⟨wide, hchart⟩ := hk cover
  simpa only [hchart] using wide.coefficients

theorem eventually_referenceNormalChartCover_spacetime_jet_bound
    {n : ℕ} {T' T S' S : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0}) (hS : S' < 0 ∧ 0 < S)
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 < b) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ cover : NormalChartCover (H.sequence.flow k).metricAt
          (H.sequence.flow k).base S' S A R ρ a b N,
        ∀ i, ∀ t ∈ I, ∀ x ∈ Metric.closedBall 0 ρ,
          ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((H.sequence.flow k).metricAt z.1).pullbackCoefficients
              (cover.chart i) z.2) (t, x)‖ ≤ B := by
  obtain ⟨a', b', ha', hb', hext⟩ :=
    H.eventually_referenceNormalChartCover_extension hS (N := N) hA hρ hρR ha hb
  obtain ⟨B, hB, hjets⟩ :=
    H.eventually_normalChartCover_spacetime_jet_bound_of_local_derivative_estimates
      hShi hIcompact hI (N := N) hA hρ hρR ha' hb'.le m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hext, hjets] with k hextk hjetsk
  intro cover
  obtain ⟨wide, hchart⟩ := hextk cover
  simpa only [hchart] using hjetsk wide

theorem referenceNormalChartCover_contDiffOn
    {n : ℕ} {T' T S' S : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    {A R ρ a b : ℝ} {N : ℕ} (k : ℕ)
    (cover : NormalChartCover (H.sequence.flow k).metricAt
      (H.sequence.flow k).base S' S A R ρ a b N) (i : Fin (N + 1)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      ((H.sequence.flow k).metricAt z.1).pullbackCoefficients (cover.chart i) z.2)
      (Ioo T' T ×ˢ Metric.ball 0 R) := by
  apply (H.sequence.flow k).flow.contDiffOn_pullbackCoefficients
    isOpen_Ioo Metric.isOpen_ball
  simpa only [cover.source i] using (cover.chart i).contMDiffOn

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
