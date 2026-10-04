import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryCaptureData
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.PartialFlowCompleteness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceTheory

/-!
# Actual ordinary capture on the partial standard-cap flow

The original half-open lifetime interval is retained. For every included
positive terminal time, capture uses precisely the complete bounded-
curvature window from time zero to that terminal time.
Source: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The actual half-open lifetime domain, as a nondegenerate spacetime
interval (Proposition 12.13, pp. 304-306). -/
def partialFlowSpacetimeInterval {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0) :
    SpacetimeInterval where
  domain := Ico 0 F.lifetime
  ordConnected := ordConnected_Ico
  nontrivial := ⟨0, ⟨le_rfl, F.lifetime_pos⟩, F.lifetime / 2,
    ⟨by linarith [F.lifetime_pos], by linarith [F.lifetime_pos]⟩,
    by linarith [F.lifetime_pos]⟩

/-- The predecessor supplies one retained ordinary product on the actual
partial flow, with its intrinsic equation (Proposition 12.13). -/
theorem partialFlow_ordinary_product {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors) :
    ∃ R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F),
      IntrinsicGeneralizedRicciEquation R.leafwiseConnection :=
  P.ordinary_product StandardCapSpace (partialFlowSpacetimeInterval F) F.flow

set_option backward.isDefEq.respectTransparency false in
/-- Each positive included terminal time has actual consistent ordinary
capture outputs on its complete closed backward window (Proposition 12.13). -/
theorem partialFlow_ordinary_capture {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors)
    (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {t : ℝ} (ht : t ∈ Ioo 0 F.lifetime) :
    Nonempty (M14OrdinaryCaptureOutput (ordinaryProductLGeometry R hRicci)
      StandardCapSpace (partialFlowSpacetimeInterval F)
      R.product.productCylinder R.product.productMetric F.flow t t
      (ordinaryProductCaptureData (I := partialFlowSpacetimeInterval F)
        (F := F.flow) R hRicci ⟨ht.1.le, ht.2⟩ t)) := by
  have hwindow : Icc (t - t) t ⊆ (partialFlowSpacetimeInterval F).domain := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans_lt ht.2⟩
  have hcurv : CompleteBoundedCurvatureOn F.flow (Icc (t - t) t) := by
    constructor
    · intro u hu
      exact partialFlow_complete F P.curvature (hwindow hu)
    · simpa only [sub_self] using F.curvature_locally_bounded t ht.1.le ht.2
  obtain ⟨out, _⟩ := P.ordinary_capture
    ((partialFlowSpacetimeInterval F).domain × StandardCapSpace) (fun p => p.1.val)
    (partialFlowSpacetimeInterval F) (ordinaryProductLGeometry R hRicci) P.ordinary_windows
    StandardCapSpace (partialFlowSpacetimeInterval F) R.product.productCylinder
    R.product.productMetric F.flow t t ⟨ht.1.le, ht.2⟩ ht.1 hwindow hcurv
    (ordinaryProductCaptureData (I := partialFlowSpacetimeInterval F)
      (F := F.flow) R hRicci ⟨ht.1.le, ht.2⟩ t)
  exact ⟨out⟩

end PoincareMT.M34
