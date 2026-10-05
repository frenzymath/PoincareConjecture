import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallChartCapture
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallChartCoefficients

/-!
# Retained source data on one fixed backward chart

A single finite prefix makes the original neck scale and closed chart
capture valid for every source index. Each selected raw rescaling belongs
to that same original neck. Morgan--Tian Claims 10.10-10.11,
pp. 254-255; M28 derivation 76.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 1800000 in
-- The fields retain dependent original slices through both subsequences and the offset.
/-- Actual original necks on one retained spatial chart, after one finite
prefix. All capture bounds hold on the closed larger ball; derivative
estimates will be tested on a smaller ball (Claims 10.10-10.11; derivation 76). -/
structure CriticalBallBackwardChartData
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k)))
    (q : G.limitCarrier.carrier) (a : ℝ) where
  /-- One prefix for the finite list of geometric capture conditions. -/
  offset : ℕ
  /-- The smaller coordinate radius. -/
  radius : ℝ
  /-- Both the larger source chart and smaller tested chart are nonempty. -/
  radius_pos : 0 < radius
  /-- The limiting normalized squared neck scale is positive. -/
  scale_pos : 0 < a
  /-- The source accuracy lies in the terminal neck ball-capture range. -/
  epsilon_small : epsilon < 1 / 2
  /-- The original source neck at the retained, shifted index. -/
  neck : ∀ k, GeneralizedStrongNeck
    (E (phi (G.subsequence (k + offset)) + H.shift)).flow
    (E (phi (G.subsequence (k + offset)) + H.shift)).time epsilon
  /-- One selected raw cylinder and its ordinary rescaling for each neck. -/
  raw : ∀ k, RescaledRawCylinderData
    (C := (E (phi (G.subsequence (k + offset)) + H.shift)).flow.slice
      (E (phi (G.subsequence (k + offset)) + H.shift)).time)
    (U := strongNeckOpen (neck k)) (J := strongNeckBackwardInterval)
    (strongNeckCylinder (neck k)) (GeneralizedStrongNeck.physical_interval_subset (neck k))
  /-- The neck center is the retained image of the chosen limit point. -/
  center_eq : ∀ k, (neck k).center = (G.embedding (k + offset) q).val.val
  /-- The larger closed ball stays in the genuine inverse-chart domain. -/
  target : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    closedBall (extChartAt (𝓡 3) q q) (2 * radius) ⊆ (extChartAt (𝓡 3) q).target
  /-- The retained source maps are smooth on the whole larger ball. -/
  exhaustion : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    ∀ k, (extChartAt (𝓡 3) q).symm ''
      closedBall (extChartAt (𝓡 3) q q) (2 * radius) ⊆ G.exhaustion (k + offset)
  /-- A common positive lower bound gives a common backward time interval. -/
  scale_lower : ∀ k, a / 2 ≤
    (E (phi (G.subsequence (k + offset)) + H.shift)).flow.scalar
      ⟨(E (phi (G.subsequence (k + offset)) + H.shift)).time,
        (E (phi (G.subsequence (k + offset)) + H.shift)).basepoint⟩ * (neck k).scale ^ 2
  /-- The same normalized scales retain their finite upper bound. -/
  scale_upper : ∀ k,
    (E (phi (G.subsequence (k + offset)) + H.shift)).flow.scalar
      ⟨(E (phi (G.subsequence (k + offset)) + H.shift)).time,
        (E (phi (G.subsequence (k + offset)) + H.shift)).basepoint⟩ * (neck k).scale ^ 2 ≤ 2 * a
  /-- Original physical-ball capture, with the same neck and raw source. -/
  capture : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    ∀ k z, z ∈ closedBall (extChartAt (𝓡 3) q q) (2 * radius) →
      (G.embedding (k + offset) ((extChartAt (𝓡 3) q).symm z)).val.val ∈
        ((E (phi (G.subsequence (k + offset)) + H.shift)).flow.metric
          (E (phi (G.subsequence (k + offset)) + H.shift)).time).ball
          (neck k).center ((neck k).scale * (epsilon⁻¹ / 16))

set_option maxHeartbeats 1800000 in
-- The constructor preserves every dependent source index in the capture theorem.
/-- The proved original-neck capture constructs all the fixed-chart data.
The accuracy is chosen before the source, limit, and limit point; one
finite prefix retains the original index order (derivation 76). -/
theorem exists_source_criticalBall_backward_chart_data_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            Nonempty (CriticalBallBackwardChartData H T A1 hA1 phi G q
              (D₀.scalarCurvature q)⁻¹) := by
  classical
  obtain ⟨epsilon₀, hpos, hsmall, hsource⟩ :=
    exists_source_criticalBall_neck_chart_capture_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q
  obtain ⟨S, hcenter, ha, _, r, hr, htarget, htail⟩ :=
    hsource H T hepsilon A1 hA1 phi G D₀ q
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have htail' (k : ℕ) := hN (k + N) (by omega)
  exact ⟨{
    offset := N
    radius := r
    radius_pos := hr
    scale_pos := ha
    epsilon_small := lt_of_le_of_lt (hepsilon.trans hsmall) (by norm_num)
    neck := fun k => S (k + N)
    raw := fun k => Classical.choice
      (GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow (S (k + N)))
    center_eq := fun k => hcenter (k + N)
    target := htarget
    exhaustion := fun k => (htail' k).2.2.1
    scale_lower := fun k => (htail' k).1
    scale_upper := fun k => (htail' k).2.1
    capture := fun k => (htail' k).2.2.2 }⟩

end PoincareMT.M28.CounterexampleNeckFamily
