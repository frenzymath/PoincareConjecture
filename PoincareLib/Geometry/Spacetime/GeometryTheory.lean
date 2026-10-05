import PoincareLib.Geometry.Spacetime.Cylinder.Theory

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Statements/M11GeneralizedFlow.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# M11 spacetime realization

The construction keeps the exact raw carrier, topology and time. Every box,
slice, supplied label and cylinder is compared using one selected realization.
The ordinary product is geometric; its Ricci equation belongs to M12.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]

/-- Realization of the specified adapted metric atlas, with actual box/slice
comparisons and all geometric domain operations required by later owners. -/
structure GeneralizedFlowCarrierConclusion (A : AdaptedMetricAtlas n X) where
  timeIntervals : SpacetimeIntervalSystem
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

/-- Ordinary product geometry on exactly I times the supplied manifold.
All identifications retain the given metric family, even when interval charts
and the realized spacetime charts are different chosen records. -/
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

/-- M11's complete geometric construction problem in arbitrary dimension.
No analytic milestone, Ricci equation, global product or completeness is an input. -/
structure GeneralizedSpacetimeGeometryTheory (n : ℕ) : Prop where
  realize : ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (A : AdaptedMetricAtlas n X), Nonempty (GeneralizedFlowCarrierConclusion A)
  ordinary_product : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval),
    RiemannianMetric.IsSmoothFamilyOn g I.domain →
      Nonempty (OrdinaryProductSpacetimeConclusion g I)

end PoincareMT
