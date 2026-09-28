import PoincareConjecture.Statements.M11CompatibleOperations









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X]



structure GeneralizedFlowCarrierConclusion (A : AdaptedMetricAtlas n X) where
  timeIntervals : SpacetimeIntervalSystem


  interval_localDiffeomorph : ∀ (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain),
    IsOpen {t : K.domain | t.val ∈ L.domain} →
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞
      (spacetimeIntervalInclusion (timeIntervals.interval L) (timeIntervals.interval K) h)
  spacetime : GeneralizedFlowSpacetime n X A.time A.interval
  slices : ∀ t, SpacetimeSliceGeometry spacetime t
  boxCylinder : ∀ b, CompatibleSpacetimeCylinder spacetime
    (timeIntervals.interval (A.box b).interval) (A.box b).spatial
  boxCylinder_eq : ∀ b p, (boxCylinder b).toSpacetime p = (A.box b).toSpacetime p
  box_localDiffeomorph : ∀ b, IsLocalDiffeomorph (spacetimeModel n) (spacetimeModel n) ∞
    (boxCylinder b).toSpacetime
  boxMetric : ∀ b, SpacetimeCylinderMetric (boxCylinder b)
  boxMetric_eq : ∀ b (t : (timeIntervals.interval (A.box b).interval).Point) x v w,
    ((boxMetric b).metric t.val).inner x v w = (A.box b).metric (t.val, x) v w
  sliceBox : ∀ b t, t ∈ (A.box b).interval.domain →
    (A.box b).spatial → (slices t).Point
  sliceBox_eq : ∀ b t ht x,
    (sliceBox b t ht x).val = (A.box b).toSpacetime (⟨t, ht⟩, x)
  sliceBox_localDiffeomorph : ∀ b t ht,
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (sliceBox b t ht)
  sliceBox_metric : ∀ b t ht x v w,
    (slices t).metricOnPoints.inner (sliceBox b t ht x)
      (mfderiv (𝓡 n) (𝓡 n) (sliceBox b t ht) x v)
      (mfderiv (𝓡 n) (𝓡 n) (sliceBox b t ht) x w) = (A.box b).metric (t, x) v w
  supplied_labels : ∀ L : SpacetimeSliceLabeling A, ∀ t,
    Nonempty (SpacetimeSliceIdentification spacetime t (slices t) (L.slice t))
  horizontalBracket : ∀ (U : ∀ p : spacetime.Point, spacetime.Horizontal p)
    (O : Set spacetime.Point), IsOpen O →
    ContMDiffOn (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : spacetime.Point ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := spacetime.Horizontal) p (U p)) O →
    ∀ p ∈ O, mfderiv (spacetimeModel n) 𝓘(ℝ) spacetime.timeFunction p
      (VectorField.mlieBracket (spacetimeModel n)
        (show ∀ q : spacetime.Point, TangentSpace (spacetimeModel n) q from spacetime.timeVector)
        (fun q : spacetime.Point ↦ (U q).val) p) = 0
  compatible : CompatibleSpacetimeTheory.{u, u} spacetime timeIntervals
  coordinate_compatible : CompatibleSpacetimeTheory.{u, 0} spacetime timeIntervals




structure OrdinaryProductSpacetimeConclusion {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval) where
  timeIntervals : SpacetimeIntervalSystem
  spacetime : GeneralizedFlowSpacetime n (I.domain × M) (fun p ↦ p.1.val) I
  slices : ∀ t, SpacetimeSliceGeometry spacetime t
  productIdentification : Diffeomorph (spacetimeModel n) (spacetimeModel n)
    ((timeIntervals.interval I).Point × M) spacetime.Point ∞
  productIdentification_eq : ∀ p, productIdentification p = p
  product_timeVector : ∀ p,
    mfderiv (spacetimeModel n) (spacetimeModel n) productIdentification p
      ((timeIntervals.interval I).positiveTangent p.1, 0) =
      spacetime.timeVector (productIdentification p)
  productCylinder : CompatibleSpacetimeCylinder spacetime (timeIntervals.interval I) M
  productCylinder_eq : ∀ p, productCylinder.toSpacetime p = p
  productMetric : SpacetimeCylinderMetric productCylinder
  productMetric_eq : productMetric.metric = g
  sliceIdentification : ∀ t : I.domain,
    Diffeomorph (𝓡 n) (𝓡 n) M (slices t.val).Point ∞
  sliceIdentification_eq : ∀ t x, (sliceIdentification t x).val = (t, x)
  sliceMetric_eq : ∀ t x v w,
    (slices t.val).metricOnPoints.inner (sliceIdentification t x)
      (mfderiv (𝓡 n) (𝓡 n) (sliceIdentification t) x v)
      (mfderiv (𝓡 n) (𝓡 n) (sliceIdentification t) x w) = (g t.val).inner x v w
  compatible : CompatibleSpacetimeTheory.{u, u} spacetime timeIntervals
  coordinate_compatible : CompatibleSpacetimeTheory.{u, 0} spacetime timeIntervals



structure GeneralizedSpacetimeGeometryTheory (n : ℕ) : Prop where
  realize : ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (A : AdaptedMetricAtlas n X), Nonempty (GeneralizedFlowCarrierConclusion A)
  ordinary_product : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval),
    RiemannianMetric.IsSmoothFamilyOn g I.domain →
      Nonempty (OrdinaryProductSpacetimeConclusion g I)

end PoincareConjecture
