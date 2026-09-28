import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryNoncollapse
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryPinching
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.PartialFlowCapture
import PoincareConjecture.Proofs.M34.Lemma12_6_Curvature.Nonnegative

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

theorem partialFlow_chapter11_calculus {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors)
    (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))
    (t : (partialFlowSpacetimeInterval F).domain) :
    MetricHomothetyCalculus (F.flow.metric t.val) (R.product.slices t.val).metricOnPoints
      (R.product.sliceIdentification t) 1 :=
  P.metric_homothety StandardCapSpace (R.product.slices t.val).Point
    (F.flow.metric t.val) (R.product.slices t.val).metricOnPoints
    (R.product.sliceIdentification t) 1 zero_lt_one
    (ordinarySlice_metricHomothety R.product t)

theorem partialFlow_chapter11_compact_ball {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors)
    (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))
    (p : (ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F)
      (F := F.flow) R).point) (r : ℝ) :
    IsCompact (closure (((ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F)
      (F := F.flow) R).metric p.1).ball p.2 r)) := by
  let t : (partialFlowSpacetimeInterval F).domain :=
    ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have h := ordinarySlice_compact_ball R.product t (partialFlow_chapter11_calculus F P R t)
    (partialFlow_complete F P.curvature t.property) p.2.val.2 r
  rw [ordinaryChapter11_identification_projection R t p.2] at h
  exact h

theorem partialFlow_chapter11_branch {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : M34StandardCapPredecessors)
    (E0 : StandardCapEstimate g0)
    (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F)) :
    generalizedPinchedOrNonnegative (ordinaryChapter11Flow
      (I := partialFlowSpacetimeInterval F) (F := F.flow) R) := by
  apply Or.inr
  exact ordinaryChapter11_nonnegative (I := partialFlowSpacetimeInterval F) (F := F.flow)
    R (partialFlow_chapter11_calculus F P R)
    (fun _ ht => ht.1) (partialFlow_nonnegativeSectionalCurvature P.curvature E0 F)

theorem standardFlow_chapter11_noncollapsed {g0 : StandardInitialMetric}
    (F : MaximalStandardCapFlow g0) (P : M34StandardCapPredecessors)
    (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))
    (H : StandardFlowNoncollapsingCertificate F) {r0 : ℝ} (hr0 : r0 ≤ H.radius)
    (p : (ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F.base)
      (F := F.base.flow) R).point) (htime : r0 ^ 2 ≤ p.1) :
    GeneralizedKappaNoncollapsedAt (ordinaryChapter11Flow
      (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R) p H.kappa r0 := by
  apply ordinaryChapter11_noncollapsed (I := partialFlowSpacetimeInterval F.base)
    (F := F.base.flow) R (partialFlow_chapter11_calculus F.base P R) p H.kappa r0
  intro r hr hrr _ hcurv
  apply H.bound p.1 (ordinaryChapter11Point_time_mem R p)
    (ordinaryChapter11Projection R p) r hr (hrr.trans hr0) _ hcurv
  exact (pow_le_pow_left₀ hr.le hrr 2).trans htime

end PoincareConjecture.M34
