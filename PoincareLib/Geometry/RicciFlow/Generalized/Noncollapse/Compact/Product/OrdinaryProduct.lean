import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Thm8_10_OrdinaryProduct.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# The actual ordinary-product geometry for compact noncollapsing

Morgan-Tian Remark 3.37 and Definition 3.38, pp. 60-61, as used in
Theorem 8.10, pp. 176-177. These adapters retain M12's exact carrier,
charts and metric while exposing the original ordinary connection.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-ordinary-product.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}

/-- The original ordinary flow determines M14 geometry on its exact
M12 product. Source: Remark 3.37, p. 60, used in Theorem 8.10, p. 177. -/
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

/-- The product cylinder metric uses the exact original metric
representative and the supplied tangent equivalences. Source:
Definition 3.38, p. 61, in Theorem 8.10, p. 177. -/
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

/-- M12's product calculus applies to the original ordinary connection.
Source: Remark 3.37, p. 60, used for the action comparison in
Theorem 8.10, p. 177. -/
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

/-- The ordinary product cylinder covers the full spacetime. Source:
Remark 3.37, p. 60, used for capture in Theorem 8.10, p. 177. -/
theorem ordinaryProductCylinder_range
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    range P.product.productCylinder.toSpacetime = univ := by
  apply range_eq_univ.mpr
  intro q
  exact ⟨q, P.product.productCylinder_eq q⟩

/-- The actual ordinary spatial projection is smooth for M12's chosen
spacetime charts. Source: Remark 3.37, p. 60, and the path comparison
in Theorem 8.10, p. 177. -/
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

end PoincareMT.Generalized.Noncollapse
