import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import PoincareConjecture.Statements.M12GeneralizedEquation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}



noncomputable def ordinaryProductTransport
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    GeneralizedLGeometryTransport n (I.domain × M) (fun q => q.1.val) I where
  spacetime := P.product.spacetime
  slices := P.product.slices
  timeIntervals := P.product.timeIntervals
  gaugeCover := P.cover
  leafwise := P.leafwiseConnection
  ricciEquation := (P.equation_iff F.connection).mpr F.equation




noncomputable def ordinaryProductCylinderMetric
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    SpacetimeCylinderMetric P.product.productCylinder where
  metric := F.metric
  smooth := F.smooth
  spatialTangentEquiv := P.product.productMetric.spatialTangentEquiv
  spatialTangentEquiv_eq := P.product.productMetric.spatialTangentEquiv_eq
  metric_eq := fun t x v w => by
    have h := P.product.productMetric.metric_eq t x v w
    simpa only [P.product.productMetric_eq] using h




theorem ordinaryProduct_moving_calculus
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    MovingGaugeCalculus (ordinaryProductTransport F P).leafwise
      (ordinaryProductCylinderMetric F P).toMovingSpacetimeGaugeGeometry F.connection := by
  have H := hM12.gauges (I.domain × M) (fun q => q.1.val) I P.product.spacetime
    P.product.slices P.product.timeIntervals P.cover P.leafwiseConnection
  exact H.moving_calculus M I P.product.productCylinder.toMovingSpacetimeGauge
    (ordinaryProductCylinderMetric F P).toMovingSpacetimeGaugeGeometry F.connection



theorem ordinaryProductCylinder_range
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    range P.product.productCylinder.toSpacetime = univ := by
  apply range_eq_univ.mpr
  intro q
  exact ⟨q, P.product.productCylinder_eq q⟩




theorem ordinaryProduct_spatial_smooth
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    ContMDiff (spacetimeModel n) (𝓡 n) ∞
      (fun q : (ordinaryProductTransport F P).Point => q.2) := by
  have h := contMDiff_snd.comp P.product.productIdentification.symm.contMDiff
  have heq : (fun q : (ordinaryProductTransport F P).Point =>
      (P.product.productIdentification.symm q).2) = (fun q => q.2) := by
    funext q
    have hi := P.product.productIdentification_eq (P.product.productIdentification.symm q)
    rw [P.product.productIdentification.apply_symm_apply] at hi
    exact congrArg Prod.snd hi.symm
  simpa only [Function.comp_def, heq] using! h

end PoincareConjecture.Proofs.M15
