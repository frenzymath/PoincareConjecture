import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryProductGeometry









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}



theorem ordinaryProduct_inner_eq (R : OrdinaryProductSpacetimeConclusion g I)
    (t : (R.timeIntervals.interval I).Point) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (g t.val).inner x v w = R.spacetime.horizontalMetric.inner
      (R.productCylinder.toSpacetime (t, x))
      (R.productMetric.spatialTangentEquiv t x v) (R.productMetric.spatialTangentEquiv t x w) := by
  have h := R.productMetric.metric_eq t x v w
  rw [R.productMetric_eq] at h
  exact h



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

end PoincareConjecture.M34
