import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallRawStage
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallMetricIdentity

/-!
# Normalized raw-stage coefficients on their actual open germs

The raw-stage map is the retained critical embedding followed by two
open inclusions. Its whole-slice normalized coefficients therefore agree
with the convergence coefficients on an open chart domain. This equality
can be differentiated at boundary points of a compact test region.
Source: Morgan--Tian Proposition 10.7, p. 253; M28 derivation 106.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E)
  (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
  (phi : ℕ → ℕ)
  (G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ)

set_option maxHeartbeats 2400000 in
-- Reduction retains both actual inclusions and the dependent original source index.
/-- The normalized raw coefficients are exactly the original critical
embedding coefficients wherever the chart inverse lies in the stage.
Source: Proposition 10.7, p. 253; M28 derivation 106. -/
theorem regularRawStage_coefficients_eq :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (y : EuclideanSpace ℝ (Fin 3)),
      y ∈ (extChartAt (𝓡 3) q).target →
      (extChartAt (𝓡 3) q).symm y ∈ G.exhaustion k →
      (H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
          (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
            (extChartAt (𝓡 3) q).symm) y =
        (H.tubeCriticalMetric T A1 (phi (G.subsequence k))).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) y := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q y hy hstage
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hy)
  have he := (G.embedding_smooth k ⟨(extChartAt (𝓡 3) q).symm y, hstage⟩).contMDiffAt
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3)
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) y :=
    (he.comp y hc).mdifferentiableAt (by simp)
  symm
  convert H.tubeCriticalMetric_pullbackCoefficients T A1 (phi (G.subsequence k))
    (f := G.embedding k ∘ (extChartAt (𝓡 3) q).symm) (x := y) hf using 1
  ext v w
  rfl

/-- Equality holds on an open neighborhood of every valid chart point,
so it identifies every iterated derivative without a compact-interior
assumption. Source: Proposition 10.7, p. 253; M28 derivation 106. -/
theorem regularRawStage_coefficients_germ :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (y : EuclideanSpace ℝ (Fin 3)),
      y ∈ (extChartAt (𝓡 3) q).target →
      (extChartAt (𝓡 3) q).symm y ∈ G.exhaustion k →
      (H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
          (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
            (extChartAt (𝓡 3) q).symm) =ᶠ[𝓝 y]
        (H.tubeCriticalMetric T A1 (phi (G.subsequence k))).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q y hy hstage
  let c := extChartAt (𝓡 3) q
  have hU : IsOpen (c.target ∩ c.symm ⁻¹' G.exhaustion k) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open k)
  filter_upwards [hU.mem_nhds ⟨hy, hstage⟩] with z hz
  exact H.regularRawStage_coefficients_eq T A1 hA1 phi G k q z hz.1 hz.2

end PoincareMT.M28.CounterexampleNeckFamily
