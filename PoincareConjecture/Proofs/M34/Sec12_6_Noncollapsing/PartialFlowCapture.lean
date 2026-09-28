import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryCaptureData
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowCompleteness
import PoincareConjecture.Statements.M34StandardCapExistence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34



def partialFlowSpacetimeInterval {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0) :
    SpacetimeInterval where
  domain := Ico 0 F.lifetime
  ordConnected := ordConnected_Ico
  nontrivial := ⟨0, ⟨le_rfl, F.lifetime_pos⟩, F.lifetime / 2,
    ⟨by linarith [F.lifetime_pos], by linarith [F.lifetime_pos]⟩,
    by linarith [F.lifetime_pos]⟩



theorem partialFlow_ordinary_product {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors) :
    ∃ R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F),
      IntrinsicGeneralizedRicciEquation R.leafwiseConnection :=
  P.ordinary_product StandardCapSpace (partialFlowSpacetimeInterval F) F.flow

set_option backward.isDefEq.respectTransparency false in


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

end PoincareConjecture.M34
