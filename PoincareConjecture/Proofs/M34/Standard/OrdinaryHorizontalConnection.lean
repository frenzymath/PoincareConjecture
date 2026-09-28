import PoincareConjecture.Proofs.M34.Standard.OrdinaryHorizontalLift
import PoincareConjecture.Proofs.M34.Standard.CompatibleCylinderDifferential
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SectionTransport
import PoincareConjecture.Statements.M12GeneralizedEquation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

variable {n : ℕ} {I : SpacetimeInterval}
  {g : ℝ → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

set_option backward.isDefEq.respectTransparency false in


theorem ordinaryProductHorizontalLift_timeDerivative
    (R : OrdinaryProductSpacetimeConclusion g I) (v : EuclideanSpace ℝ (Fin n))
    (t : (R.timeIntervals.interval I).Point) (x : EuclideanSpace ℝ (Fin n)) :
    movingGaugeSectionTimeDerivative R.productMetric.toMovingSpacetimeGaugeGeometry
      (fun z => ordinaryProductHorizontalLift R z v) t x = 0 := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨(R.productMetric.toMovingSpacetimeGaugeGeometry.metric t.val).toRiemannianMetric⟩
  unfold movingGaugeSectionTimeDerivative
  have heq : (fun s : (R.timeIntervals.interval I).Point =>
      pullbackHorizontalSection R.productMetric.toMovingSpacetimeGaugeGeometry
        (fun z => ordinaryProductHorizontalLift R z v) s x) = fun _ => v :=
    funext (fun s => ordinaryProductHorizontalLift_pullback R v s x)
  rw [heq, mfderiv_const]
  rfl

set_option backward.isDefEq.respectTransparency false in



theorem ordinaryProductHorizontalLift_rawDerivative
    (R : OrdinaryProductRicciGeometry g I) (c : MetricLeviCivitaFamily g)
    (v : EuclideanSpace ℝ (Fin n)) (t : (R.product.timeIntervals.interval I).Point)
    (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) (u : TangentSpace (𝓡 n) x) :
    rawHorizontalCovariantDerivative R.leafwiseConnection
      (fun z => ordinaryProductHorizontalLift R.product z v)
      (R.product.productCylinder.toSpacetime (t, x))
      (a • R.product.spacetime.timeVector (R.product.productCylinder.toSpacetime (t, x)) +
        (R.product.productMetric.spatialTangentEquiv t x u).val) =
      R.product.productMetric.spatialTangentEquiv t x
        ((c t.val).connection (fun _ => v) x u) := by
  have h : ∀ (h : ℝ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (c' : MetricLeviCivitaFamily h), R.product.productMetric.metric = h →
      rawHorizontalCovariantDerivative R.leafwiseConnection
        (fun z => ordinaryProductHorizontalLift R.product z v)
        (R.product.productCylinder.toSpacetime (t, x))
        (a • R.product.spacetime.timeVector (R.product.productCylinder.toSpacetime (t, x)) +
          (R.product.productMetric.spatialTangentEquiv t x u).val) =
        R.product.productMetric.spatialTangentEquiv t x
          ((c' t.val).connection (fun _ => v) x u) := by
    intro h c' hh
    subst h
    have hd := (movingGaugeSectionTransportFields R.leafwiseConnection
      R.product.productCylinder.toMovingSpacetimeGauge
      R.product.productMetric.toMovingSpacetimeGaugeGeometry c').horizontal_derivative_eq
      (fun z => ordinaryProductHorizontalLift R.product z v) univ isOpen_univ
      (ordinaryProductHorizontalLift_smooth R.product v) t x (mem_univ _) a u
    have hpull : pullbackHorizontalSection
        R.product.productMetric.toMovingSpacetimeGaugeGeometry
        (fun z => ordinaryProductHorizontalLift R.product z v) t = fun _ => v :=
      funext (ordinaryProductHorizontalLift_pullback R.product v t)
    have hzero : movingGaugeDrift R.product.productMetric.toMovingSpacetimeGaugeGeometry t =
        0 := funext (compatibleMovingGaugeDrift_zero R.product.productCylinder
          R.product.productMetric t)
    change rawHorizontalCovariantDerivative R.leafwiseConnection _ _
      (mfderiv (spacetimeModel n) (spacetimeModel n)
        R.product.productCylinder.toSpacetime (t, x)
        (a • (R.product.timeIntervals.interval I).positiveTangent t, u)) = _ at hd
    rw [compatibleCylinder_mfderiv_prod R.product.productCylinder
      R.product.productMetric] at hd
    rw [ordinaryProductHorizontalLift_timeDerivative, hpull, hzero,
      CovariantDerivative.zero] at hd
    simpa only [smul_zero, zero_add, Pi.zero_apply, zero_apply, sub_zero] using! hd
  exact h g c R.product.productMetric_eq

end PoincareConjecture.M34
