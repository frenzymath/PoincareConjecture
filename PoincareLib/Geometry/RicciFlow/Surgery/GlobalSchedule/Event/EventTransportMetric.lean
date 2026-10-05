import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareLib.Geometry.RicciFlow.Diffeomorph
import PoincareLib.Geometry.Riemannian.Homothety.Assembly

/-!
# Metric data for nonempty event transport

The source pre-flow is pulled back by the inverse of the fixed map at the
event's initial time.  This file records the resulting factor-one metric
calculus and the chart-sensitive transport of `SurgeryMetricLimitOn`.
`EventTransportMetricCovariance` constructs the displayed data from the source
event by compact-uniform source-chart transport.
This is the regular-limit clause of Morgan--Tian Definition 15.8,
pp. 361-362, used in Section 17.2, pp. 409-411.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

namespace M51EventTransport

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- The target metric is the source metric pulled back by `e`;
Definition 15.8, pp. 361-362. -/
theorem pullback_metric_homothety
    {slice' : ℝ → GeneralizedSliceCarrier.{u}}
    (E : SurgeryEventData g₀ K P slice metric T)
    (e : Diffeomorph (𝓡 3) (𝓡 3)
      (slice' E.tMinus).carrier (slice E.tMinus).carrier ∞)
    (t : Set.Ico E.tMinus T) :
    MetricHomothety ((E.pre_flow.pullbackDiffeomorph e).metric t.1)
      (E.pre_flow.metric t.1) e 1 := by
  intro x v w
  simpa only [one_mul] using
    (E.pre_flow.pullbackDiffeomorph_inner e t.1 x v w).symm

/-- Assemble the factor-one calculus for a pulled-back metric;
Definition 15.8, pp. 361-362. -/
theorem pullback_metric_calculus
    {M N : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric 3 N) (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hf : MetricHomothety (g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph)
      g e 1) :
    MetricHomothetyCalculus
      (g.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph) g e 1 :=
  M13.metricHomothetyCalculus _ _ e 1 (by norm_num) hf

/-- Internal producer data for the chart-sensitive metric-limit field.

`metric_converges` is the only part of event transport that does not reduce to
the checked pullback and image identities. `MetricLimitTransportData.of_source`
in `EventTransportMetricCovariance` constructs it from the source limit; this
record is not a new public hypothesis of the M51 contract.
It packages the regular-limit clause of Definition 15.8, pp. 361-362.
-/
structure MetricLimitTransportData
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)
    (p : Diffeomorph (𝓡 3) (𝓡 3)
      (slice E.tMinus).carrier (slice' E.tMinus).carrier ∞) where
  metric_converges :
    SurgeryMetricLimitOn (slice' E.tMinus) E.terminal
      (E.pre_flow.pullbackDiffeomorph p.symm).metric E.limit_metric
      (fun x => E.limit_identify.map (p.symm x))
      (p.symm ⁻¹' E.regular_limit) T

/-- Read the transported regular-limit convergence; Definition 15.8, pp. 361-362. -/
theorem MetricLimitTransportData.metricConverges
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)
    (p : Diffeomorph (𝓡 3) (𝓡 3)
      (slice E.tMinus).carrier (slice' E.tMinus).carrier ∞)
    (D : MetricLimitTransportData E p) :
    SurgeryMetricLimitOn (slice' E.tMinus) E.terminal
      (E.pre_flow.pullbackDiffeomorph p.symm).metric E.limit_metric
      (fun x => E.limit_identify.map (p.symm x))
      (p.symm ⁻¹' E.regular_limit) T :=
  D.metric_converges

/-- The terminal image is unchanged after pulling back the pre-carrier;
Definition 15.8, pp. 361-362. -/
theorem limit_identify_image_preimage
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice slice' : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier}
    {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)
    (p : Diffeomorph (𝓡 3) (𝓡 3)
      (slice E.tMinus).carrier (slice' E.tMinus).carrier ∞)
    (U : Set (slice E.tMinus).carrier) :
    (fun x => E.limit_identify.map (p.symm x)) '' (p.symm ⁻¹' U) =
      E.limit_identify.map '' U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨p.symm x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨p x, ?_, ?_⟩
    · change p.symm (p x) ∈ U
      simpa using hx
    · simp

end M51EventTransport

end PoincareMT
