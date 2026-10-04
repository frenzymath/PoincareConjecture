import PoincareLib.Geometry.RicciFlow.Compactness.Subsequence
import PoincareLib.Geometry.RicciFlow.Completeness
import PoincareLib.Topology.MetricSpace.Completeness

/-!
# Producer interfaces for pointed compactness

The compactness theorem has two independent geometric outputs: a smooth
exhaustion limit and completeness of its interior time slices.  These
interfaces make that split explicit and provide a checked assembly into the
frozen M07 conclusion.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareMT

/-- Certificate for the smooth pointed exhaustion limit. -/
structure PointedRicciFlowGeometricProducer
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) where
  geometric_limit : PointedGeometricConvergence H.sequence

/-- Certificate for completeness at every interior time of a produced limit. -/
structure PointedRicciFlowCompletenessProducer
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (G : PointedGeometricConvergence H.sequence) where
  complete_interior : ∀ t ∈ Set.Ioo T' T,
    FlowCarrier.metricComplete G.limitCarrier (G.limitFlow.metricAt t)

/-- Curvature control on the constructed limit supplies its completeness
producer. Zero-time completeness and curvature transfer remain obligations of
the geometric limit construction. -/
theorem PointedRicciFlowCompletenessProducer.of_curvature_bound
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (G : PointedGeometricConvergence H.sequence)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hcurv : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      ∀ s ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
        ∀ x ∈ G.limitFlow.ballAt s A,
          (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤ K) :
    PointedRicciFlowCompletenessProducer H G where
  complete_interior := G.limitFlow.complete_interior_of_two_time_curvature_bound
    H.time_bounds hcomplete hcurv

/-! The following input is the exact metric boundary left by the geometric
compactness construction. Its reference completeness must come from the
construction of the limit: an arbitrary `PointedGeometricConvergence` can
restrict a flat Euclidean limit to an incomplete open ball. The comparison
fields still require curvature transfer and curve-length estimates using
the all-time curvature hypothesis. -/

/-- Metric data sufficient to transfer zero-time completeness to every
interior slice of a pointed geometric limit. -/
structure PointedRicciFlowInteriorCompletenessInput
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (G : PointedGeometricConvergence H.sequence) where
  reference_complete :
    @CompleteSpace G.limitCarrier.carrier
      (FlowCarrier.metricEMetricSpace G.limitCarrier
        (G.limitFlow.metricAt 0)).toUniformSpace
  ball_containment : ∀ t : Set.Ioo T' T, ∀ R : ℝ≥0, ∃ S : ℝ≥0,
    ∀ x : G.limitCarrier.carrier,
    (FlowCarrier.metricEMetricSpace G.limitCarrier
      (G.limitFlow.metricAt t.1)).edist x G.limitFlow.base ≤ R →
      (FlowCarrier.metricEMetricSpace G.limitCarrier
        (G.limitFlow.metricAt 0)).edist x G.limitFlow.base ≤ S
  metric_comparison : ∀ t : Set.Ioo T' T, ∀ R : ℝ≥0, ∃ C : ℝ≥0,
    ∀ x y : G.limitCarrier.carrier,
    (FlowCarrier.metricEMetricSpace G.limitCarrier
      (G.limitFlow.metricAt 0)).edist x G.limitFlow.base ≤ R →
    (FlowCarrier.metricEMetricSpace G.limitCarrier
      (G.limitFlow.metricAt 0)).edist y G.limitFlow.base ≤ R →
      (FlowCarrier.metricEMetricSpace G.limitCarrier
        (G.limitFlow.metricAt t.1)).edist x y ≤
          C * (FlowCarrier.metricEMetricSpace G.limitCarrier
            (G.limitFlow.metricAt 0)).edist x y ∧
      (FlowCarrier.metricEMetricSpace G.limitCarrier
        (G.limitFlow.metricAt 0)).edist x y ≤
          C * (FlowCarrier.metricEMetricSpace G.limitCarrier
            (G.limitFlow.metricAt t.1)).edist x y

/-- Apply the checked local metric-comparison transfer to the actual Riemannian
metrics of a pointed flow. -/
theorem PointedRicciFlowInteriorCompletenessInput.toProducer
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {G : PointedGeometricConvergence H.sequence}
    (P : PointedRicciFlowInteriorCompletenessInput G) :
    PointedRicciFlowCompletenessProducer H G := by
  let d₀ : PseudoEMetricSpace G.limitCarrier.carrier :=
    (FlowCarrier.metricEMetricSpace G.limitCarrier
      (G.limitFlow.metricAt 0)).toPseudoEMetricSpace
  let d₁ : Set.Ioo T' T → PseudoEMetricSpace G.limitCarrier.carrier :=
    fun t ↦ (FlowCarrier.metricEMetricSpace G.limitCarrier
      (G.limitFlow.metricAt t.1)).toPseudoEMetricSpace
  have hfamily : ∀ t : Set.Ioo T' T,
      @CompleteSpace G.limitCarrier.carrier (d₁ t).toUniformSpace := by
    apply Poincare.completeSpace_family_of_preconnected_local_emetric_comparison
      d₀ d₁ G.limitFlow.base P.reference_complete
    · intro t
      exact FlowCarrier.preconnected_metricEMetricSpace G.limitCarrier
        (G.limitFlow.metricAt t.1)
    · exact P.ball_containment
    · exact P.metric_comparison
  refine { complete_interior := ?_ }
  intro t ht
  have h := hfamily ⟨t, ht⟩
  change @CompleteSpace G.limitCarrier.carrier
    (FlowCarrier.metricEMetricSpace G.limitCarrier
      (G.limitFlow.metricAt t)).toUniformSpace
  simpa [d₁] using h

/-- Reindex a geometric producer along a strictly increasing subsequence. -/
def PointedRicciFlowGeometricProducer.ofSubsequence
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (P : PointedRicciFlowGeometricProducer (H.subsequence φ hφ)) :
    PointedRicciFlowGeometricProducer H where
  geometric_limit := P.geometric_limit.ofSubsequence hφ

/-- Reindex a completeness producer along the same subsequence. -/
theorem PointedRicciFlowCompletenessProducer.ofSubsequence
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {P : PointedRicciFlowGeometricProducer (H.subsequence φ hφ)}
    (C : PointedRicciFlowCompletenessProducer (H.subsequence φ hφ) P.geometric_limit) :
    PointedRicciFlowCompletenessProducer H (P.geometric_limit.ofSubsequence hφ) where
  complete_interior := C.complete_interior

/-- Assemble the frozen M07 conclusion from its two producer certificates. -/
def PointedRicciFlowGeometricProducer.assemble
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (P : PointedRicciFlowGeometricProducer H)
    (C : PointedRicciFlowCompletenessProducer H P.geometric_limit) :
    PointedRicciFlowCompactnessConclusion H where
  geometric_limit := P.geometric_limit
  complete_interior := C.complete_interior

/-- Nonemptiness form of the producer assembly. -/
theorem pointedRicciFlowCompactness_of_producers
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (P : PointedRicciFlowGeometricProducer H)
    (C : PointedRicciFlowCompletenessProducer H P.geometric_limit) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) :=
  ⟨P.assemble C⟩

end PoincareMT
