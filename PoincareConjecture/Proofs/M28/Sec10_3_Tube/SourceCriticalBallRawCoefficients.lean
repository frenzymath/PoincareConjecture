import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawStage
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallMetricIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

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

end PoincareConjecture.M28.CounterexampleNeckFamily
