import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateGerms











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture.ChartDistance
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
  (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)



def limitNeckMap (k : ℕ) : D.limitDomain → strongNeckOpen (D.neck k) :=
  fun x => D.neckMap k ⟨x.val, D.limitDomain_subset_domain x.property⟩

set_option maxHeartbeats 1400000 in



theorem limitNeckMap_localDiffeomorph (k : ℕ) :
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (D.limitNeckMap k) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let e : D.limitDomain → H.tubeCriticalRegion T A1 (D.sourceIndex k) :=
    fun x => G.embedding (k + D.offset) ((extChartAt (𝓡 3) q).symm x.val)
  have he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
    apply G.chart_embedding_localDiffeomorph q (k + D.offset)
      D.limitDomain D.limitDomain_open
    · exact D.limitDomain_subset_domain.trans (Metric.ball_subset_closedBall.trans D.target)
    · exact (image_mono (D.limitDomain_subset_domain.trans
        Metric.ball_subset_closedBall)).trans (D.exhaustion k)
  have hcapture : ∀ x : D.limitDomain, (e x).val.val ∈ (D.neck k).carrier :=
    fun x => D.sourceMap_mem_neck k ⟨x.val, D.limitDomain_subset_domain x.property⟩
  exact GeneralizedStrongNeck.captured_chart_map_localDiffeomorph (D.neck k)
    D.limitDomain D.limitDomain_open (fun x => (e x).val.val)
    (H.tubeCritical_chart_original_localDiffeomorph T A1 (D.sourceIndex k)
      D.limitDomain D.limitDomain_open e he) hcapture



def limitParametrization (k : ℕ) : EuclideanSpace ℝ (Fin 3) → strongNeckOpen (D.neck k) :=
  chartParametrization (fun _ : Unit => D.limitDomain) (fun _ => D.limitDomain_open)
    (i := ()) (D.limitNeckMap k)



theorem limitParametrization_eq (k : ℕ) :
    EqOn (D.limitParametrization k) (D.parametrization k) D.limitDomain := by
  intro x hx
  calc
    D.limitParametrization k x = D.limitNeckMap k ⟨x, hx⟩ :=
      chartParametrization_apply (fun _ : Unit => D.limitDomain)
        (fun _ => D.limitDomain_open) (D.limitNeckMap k) ⟨x, hx⟩
    _ = D.neckMap k ⟨x, D.limitDomain_subset_domain hx⟩ := rfl
    _ = D.parametrization k x :=
      (D.parametrization_apply k ⟨x, D.limitDomain_subset_domain hx⟩).symm

set_option maxHeartbeats 1400000 in




theorem limitParametrization_coefficients_eq (k : ℕ) (t : ℝ) :
    EqOn (((D.sourceFlow k).metric t).pullbackCoefficients (D.limitParametrization k))
      (((D.sourceFlow k).metric t).pullbackCoefficients (D.parametrization k))
      D.limitDomain := by
  intro x hx
  have hnear : D.limitParametrization k =ᶠ[𝓝 x] D.parametrization k := by
    filter_upwards [D.limitDomain_open.mem_nhds hx] with y hy
    exact D.limitParametrization_eq k hy
  exact ((D.sourceFlow k).metric t).pullbackCoefficients_eq_of_eventuallyEq hnear

end PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
