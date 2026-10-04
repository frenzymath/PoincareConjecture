import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallBackwardCoefficients
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.CoordinateGerms

/-!
# The smaller canonical chart in the same original neck flow

Restricting the captured source map changes its arbitrary totalization
outside the smaller chart but preserves its coefficient germs inside.
This identifies the analytic coefficient limit with the canonical
pullback-flow construction. Morgan--Tian Proposition 5.14 and
Claims 10.10-10.11, pp. 90-91 and 254-255; M28 derivation 76.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

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

/-- Restriction of the same captured neck map to the smaller limit chart
(Proposition 5.14; derivation 76). -/
def limitNeckMap (k : ℕ) : D.limitDomain → strongNeckOpen (D.neck k) :=
  fun x => D.neckMap k ⟨x.val, D.limitDomain_subset_domain x.property⟩

set_option maxHeartbeats 1400000 in
-- Both canonical chart domains retain the same dependent original slice map.
/-- The smaller source map is a local diffeomorphism into the same
original full neck, suitable for canonical flow pullback (derivation 76). -/
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

/-- Canonical totalization on the smaller chart used to reconstruct the
actual limit flow (derivation 76). -/
def limitParametrization (k : ℕ) : EuclideanSpace ℝ (Fin 3) → strongNeckOpen (D.neck k) :=
  chartParametrization (fun _ : Unit => D.limitDomain) (fun _ => D.limitDomain_open)
    (i := ()) (D.limitNeckMap k)

/-- The two canonical totalizations agree on the smaller chart. Values
outside that open set are immaterial (derivation 76). -/
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
-- Germ equality compares the actual dependent source bilinear forms.
/-- Germ equality of the two spatial totalizations gives identical actual
pullback coefficients throughout the smaller open chart, at every total
metric time (derivation 76). -/
theorem limitParametrization_coefficients_eq (k : ℕ) (t : ℝ) :
    EqOn (((D.sourceFlow k).metric t).pullbackCoefficients (D.limitParametrization k))
      (((D.sourceFlow k).metric t).pullbackCoefficients (D.parametrization k))
      D.limitDomain := by
  intro x hx
  have hnear : D.limitParametrization k =ᶠ[𝓝 x] D.parametrization k := by
    filter_upwards [D.limitDomain_open.mem_nhds hx] with y hy
    exact D.limitParametrization_eq k hy
  exact ((D.sourceFlow k).metric t).pullbackCoefficients_eq_of_eventuallyEq hnear

end PoincareMT.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
