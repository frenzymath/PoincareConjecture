import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryProductGeometry

/-!
# Actual ordinary-product metric and curvature transport

The retained total metric-family equality allows M12's local-isometry
identities to be applied to the actual ordinary connection family.
Source: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}

/-- The supplied tangent equivalence preserves the actual ordinary metric
(Proposition 12.13, pp. 304-306). -/
theorem ordinaryProduct_inner_eq (R : OrdinaryProductSpacetimeConclusion g I)
    (t : (R.timeIntervals.interval I).Point) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (g t.val).inner x v w = R.spacetime.horizontalMetric.inner
      (R.productCylinder.toSpacetime (t, x))
      (R.productMetric.spatialTangentEquiv t x v) (R.productMetric.spatialTangentEquiv t x w) := by
  have h := R.productMetric.metric_eq t x v w
  rw [R.productMetric_eq] at h
  exact h

/-- The actual scalar curvature transports through the retained product
(Proposition 12.13, pp. 304-306). -/
theorem ordinaryProduct_scalar_eq (R : OrdinaryProductRicciGeometry g I)
    (c : MetricLeviCivitaFamily g) (t : (R.product.timeIntervals.interval I).Point) (x : M) :
    (c t.val).scalarCurvature x = horizontalScalarCurvature R.leafwiseConnection
      (R.product.productCylinder.toSpacetime (t, x)) := by
  have h : ∀ (h : ℝ → RiemannianMetric n M) (c' : MetricLeviCivitaFamily h),
      R.product.productMetric.metric = h → (c' t.val).scalarCurvature x =
        horizontalScalarCurvature R.leafwiseConnection
          (R.product.productCylinder.toSpacetime (t, x)) := by
    intro h c' hh
    subst h
    exact (movingGaugeCurvatureTransportFields R.leafwiseConnection
      R.product.productCylinder.toMovingSpacetimeGauge
      R.product.productMetric.toMovingSpacetimeGaugeGeometry c').scalar_eq t x
  exact h g c R.product.productMetric_eq

/-- The actual Ricci form transports through the retained product
(Proposition 12.13, pp. 304-306). -/
theorem ordinaryProduct_ricci_eq (R : OrdinaryProductRicciGeometry g I)
    (c : MetricLeviCivitaFamily g) (t : (R.product.timeIntervals.interval I).Point) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (c t.val).ricci x v w = horizontalRicci R.leafwiseConnection
      (R.product.productCylinder.toSpacetime (t, x))
      (R.product.productMetric.spatialTangentEquiv t x v)
      (R.product.productMetric.spatialTangentEquiv t x w) := by
  have h : ∀ (h : ℝ → RiemannianMetric n M) (c' : MetricLeviCivitaFamily h),
      R.product.productMetric.metric = h → (c' t.val).ricci x v w =
        horizontalRicci R.leafwiseConnection (R.product.productCylinder.toSpacetime (t, x))
          (R.product.productMetric.spatialTangentEquiv t x v)
          (R.product.productMetric.spatialTangentEquiv t x w) := by
    intro h c' hh
    subst h
    exact (movingGaugeCurvatureTransportFields R.leafwiseConnection
      R.product.productCylinder.toMovingSpacetimeGauge
      R.product.productMetric.toMovingSpacetimeGaugeGeometry c').ricci_eq t x v w
  exact h g c R.product.productMetric_eq

/-- The full curvature norm transports through the same retained metric,
as required by the eventual actual cylinder (Proposition 12.13). -/
theorem ordinaryProduct_curvatureNorm_eq (R : OrdinaryProductRicciGeometry g I)
    (c : MetricLeviCivitaFamily g) (t : (R.product.timeIntervals.interval I).Point) (x : M) :
    (c t.val).curvatureTensorNorm x = horizontalCurvatureNorm R.leafwiseConnection
      (R.product.productCylinder.toSpacetime (t, x)) := by
  have h : ∀ (h : ℝ → RiemannianMetric n M) (c' : MetricLeviCivitaFamily h),
      R.product.productMetric.metric = h → (c' t.val).curvatureTensorNorm x =
        horizontalCurvatureNorm R.leafwiseConnection
          (R.product.productCylinder.toSpacetime (t, x)) := by
    intro h c' hh
    subst h
    exact (movingGaugeCurvatureTransportFields R.leafwiseConnection
      R.product.productCylinder.toMovingSpacetimeGauge
      R.product.productMetric.toMovingSpacetimeGaugeGeometry c').curvature_norm_eq t x
  exact h g c R.product.productMetric_eq

set_option backward.isDefEq.respectTransparency false in
/-- On every actual horizontal fiber the projection preserves its metric,
with the ordinary metric taken at that point's physical clock
(Proposition 12.13, pp. 304-306). -/
theorem ordinaryProductProjection_inner (R : OrdinaryProductSpacetimeConclusion g I)
    (z : R.spacetime.Point) (v w : R.spacetime.Horizontal z) :
    (g z.1.val).inner (ordinaryProductProjection R z)
      (mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R) z v.val)
      (mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R) z w.val) =
      R.spacetime.horizontalMetric.inner z v w := by
  have h (t : (R.timeIntervals.interval I).Point) (x : M)
      (v w : R.spacetime.Horizontal (R.productCylinder.toSpacetime (t, x))) :
      (g t.val).inner (ordinaryProductProjection R (R.productCylinder.toSpacetime (t, x)))
        (mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R)
          (R.productCylinder.toSpacetime (t, x)) v.val)
        (mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R)
          (R.productCylinder.toSpacetime (t, x)) w.val) =
      R.spacetime.horizontalMetric.inner (R.productCylinder.toSpacetime (t, x)) v w := by
    obtain ⟨v', rfl⟩ := (R.productMetric.spatialTangentEquiv t x).surjective v
    obtain ⟨w', rfl⟩ := (R.productMetric.spatialTangentEquiv t x).surjective w
    rw [ordinaryProductProjection_spatialTangent, ordinaryProductProjection_spatialTangent,
      ordinaryProductProjection_cylinder]
    exact ordinaryProduct_inner_eq R t x v' w'
  have hz := h z.1 z.2
  rw [R.productCylinder_eq] at hz
  exact hz v w

end PoincareMT.M34
