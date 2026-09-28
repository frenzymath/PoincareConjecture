import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardCurvature
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardPinching
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching.OperatorPositivity
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}
  {D : CriticalBallBackwardChartData H T A1 hA1 phi G q a}

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in

theorem BackwardChartLimit.nonnegativeCurvatureOperator (L : BackwardChartLimit D)
    (P : RicciFlowCurvatureTheory.{u}) (hphi : StrictMono phi)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k t, t ∈ Icc (-(a / 8)) 0 → ∀ x : strongNeckOpen (D.neck k),
      ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K) :
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-(a / 8)) 0, ∀ x : D.limitDomain,
      (L.flow.connection t).NonnegativeCurvatureOperator x := by
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t ht x
  apply (L.flow.connection t).nonnegativeCurvatureOperator_of_plane_nonneg
    (L.flow.connection t).normalization_curvatureTensorCalculus x
  intro v w
  let f (k : ℕ) := D.limitParametrization (L.subsequence k)
  let g (k : ℕ) := (D.sourceFlow (L.subsequence k)).metric t
  let V (k : ℕ) := mfderiv (𝓡 3) (𝓡 3) (f k) x v
  let W (k : ℕ) := mfderiv (𝓡 3) (𝓡 3) (f k) x w
  have herr : Tendsto (fun k => D.pinchingError (L.subsequence k) t ht (f k x))
      atTop (𝓝 0) :=
    (D.pinchingError_tendsto_zero P hphi hK hcurv t ht
      (fun k => D.limitParametrization k x)).comp L.subsequence_strictMono.tendsto_atTop
  have hcoeff : Tendsto (fun k => (g k).pullbackCoefficients (f k) x) atTop
      (𝓝 (L.coefficients (t, x))) := by
    simpa only [SpacetimeBounds.metricTwoJet] using
      (L.spatial_twoJets t ht x.property).fst_nhds
  have heval (u z : EuclideanSpace ℝ (Fin 3)) :
      Tendsto (fun k => (g k).pullbackCoefficients (f k) x u z) atTop
        (𝓝 (L.coefficients (t, x) u z)) :=
    ((ContinuousLinearMap.apply ℝ ℝ z).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) u).continuous.tendsto _).comp hcoeff)
  have hgram : Tendsto (fun k => M04.metricGram (g k) (f k x) (V k) (W k)) atTop
      (𝓝 (L.coefficients (t, x) v v * L.coefficients (t, x) w w -
        L.coefficients (t, x) v w ^ 2)) := by
    exact ((heval v v).mul (heval w w)).sub ((heval v w).pow 2)
  have hlower : Tendsto
      (fun k => -D.pinchingError (L.subsequence k) t ht (f k x) *
        M04.metricGram (g k) (f k x) (V k) (W k)) atTop (𝓝 0) := by
    simpa only [neg_zero, zero_mul] using herr.neg.mul hgram
  exact le_of_tendsto_of_tendsto hlower (L.curvatureTensor_tendsto t ht x v w v w)
    (Eventually.of_forall fun k =>
      D.sourceFlow_plane_lower P (L.subsequence k) t ht (f k x) (V k) (W k))

end PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
