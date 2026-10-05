import PoincareLib.Geometry.Spacetime.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M11SpacetimeSlices.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Actual slices and supplied slice identifications

The level sets keep the specified spacetime subspace topology. Their charts,
metrics and derivative identifications are outputs of M11. Supplied labels
are compared by actual diffeomorphisms, not equality of chosen atlas records.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- Boundaryless geometry on the actual time fiber, including boundary times
and the empty fibers outside the time image. -/
structure SpacetimeSliceGeometry (F : GeneralizedFlowSpacetime n X time I) (t : ℝ) where
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) (F.Slice t)
  isManifold : IsManifold (𝓡 n) ∞ (F.Slice t)
  t3Space : T3Space (F.Slice t)
  secondCountable : SecondCountableTopology (F.Slice t)
  measurableSpace : MeasurableSpace (F.Slice t)
  borelSpace : BorelSpace (F.Slice t)
  inclusion_smooth : ContMDiff (𝓡 n) (spacetimeModel n) ∞
    (Subtype.val : F.Slice t → F.Point)
  inclusion_embedding : Topology.IsEmbedding (Subtype.val : F.Slice t → F.Point)
  inclusion_differential_injective : ∀ x : F.Slice t,
    Function.Injective
      (mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : F.Slice t → F.Point) x)
  tangentEquiv : ∀ x : F.Slice t,
    TangentSpace (𝓡 n) x ≃L[ℝ] F.Horizontal x.val
  tangentEquiv_eq : ∀ x v, (tangentEquiv x v).val =
    mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : F.Slice t → F.Point) x v
  metric : RiemannianMetric n (F.Slice t)
  metric_eq : ∀ x v w, metric.inner x v w =
    F.horizontalMetric.inner x.val (tangentEquiv x v) (tangentEquiv x w)

namespace SpacetimeSliceGeometry

variable {F : GeneralizedFlowSpacetime n X time I} {t : ℝ}

/-- The exact fiber subtype with this slice witness's chart instances. -/
abbrev Point (_S : SpacetimeSliceGeometry F t) := F.Slice t

instance (S : SpacetimeSliceGeometry F t) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace

instance (S : SpacetimeSliceGeometry F t) : IsManifold (𝓡 n) ∞ S.Point := S.isManifold

instance (S : SpacetimeSliceGeometry F t) : T3Space S.Point := S.t3Space

instance (S : SpacetimeSliceGeometry F t) :
    SecondCountableTopology S.Point := S.secondCountable

instance (S : SpacetimeSliceGeometry F t) : MeasurableSpace S.Point := S.measurableSpace

instance (S : SpacetimeSliceGeometry F t) : BorelSpace S.Point := S.borelSpace

/-- The slice metric with this witness's selected charts explicit. -/
noncomputable abbrev metricOnPoints (S : SpacetimeSliceGeometry F t) :
    RiemannianMetric n S.Point := S.metric

end SpacetimeSliceGeometry

/-- A previously supplied smooth metric manifold labeling exactly one time fiber.
The map into the raw spacetime is only assumed to be a topological embedding. -/
structure SpacetimeSliceLabel (n : ℕ) (X : Type u) [TopologicalSpace X]
    (time : X → ℝ) (t : ℝ) where
  carrier : Type u
  topologicalSpace : TopologicalSpace carrier
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier
  isManifold : IsManifold (𝓡 n) ∞ carrier
  measurableSpace : MeasurableSpace carrier
  borelSpace : BorelSpace carrier
  metric : RiemannianMetric n carrier
  toSpacetime : carrier → X
  embedding : Topology.IsEmbedding toSpacetime
  time_eq : ∀ x, time (toSpacetime x) = t
  range_eq : Set.range toSpacetime = {p | time p = t}

attribute [instance] SpacetimeSliceLabel.topologicalSpace
  SpacetimeSliceLabel.chartedSpace SpacetimeSliceLabel.isManifold
  SpacetimeSliceLabel.measurableSpace SpacetimeSliceLabel.borelSpace

/-- Labels compatible with the actual box maps and their selected metric forms. -/
structure SpacetimeSliceLabeling (A : AdaptedMetricAtlas n X) where
  slice : ∀ t, SpacetimeSliceLabel n X A.time t
  boxMap : ∀ b t, t ∈ (A.box b).interval.domain →
    (A.box b).spatial → (slice t).carrier
  boxMap_smooth : ∀ b t ht, ContMDiff (𝓡 n) (𝓡 n) ∞ (boxMap b t ht)
  boxMap_eq : ∀ b t ht x,
    (slice t).toSpacetime (boxMap b t ht x) = (A.box b).toSpacetime (⟨t, ht⟩, x)
  metric_eq : ∀ b t ht x v w,
    (slice t).metric.inner (boxMap b t ht x)
      (mfderiv (𝓡 n) (𝓡 n) (boxMap b t ht) x v)
      (mfderiv (𝓡 n) (𝓡 n) (boxMap b t ht) x w) =
      (A.box b).metric (t, x) v w

/-- An actual supplied-label-to-level-set diffeomorphism and its metric/tangent
identities. Its inverse smoothness is an output, obtained from full rank. -/
structure SpacetimeSliceIdentification (F : GeneralizedFlowSpacetime n X time I)
    (t : ℝ) (S : SpacetimeSliceGeometry F t) (L : SpacetimeSliceLabel n X time t) where
  identification : Diffeomorph (𝓡 n) (𝓡 n) L.carrier S.Point ∞
  identification_eq : ∀ x, (identification x).val = L.toSpacetime x
  tangent_eq : ∀ x v,
    (S.tangentEquiv (identification x)
      (mfderiv (𝓡 n) (𝓡 n) identification x v)).val =
      mfderiv (𝓡 n) (spacetimeModel n)
        (show L.carrier → F.Point from L.toSpacetime) x v
  metric_eq : ∀ x v w,
    S.metricOnPoints.inner (identification x)
      (mfderiv (𝓡 n) (𝓡 n) identification x v)
      (mfderiv (𝓡 n) (𝓡 n) identification x w) = L.metric.inner x v w
  measurable : Measurable identification ∧ Measurable identification.symm

end PoincareMT
