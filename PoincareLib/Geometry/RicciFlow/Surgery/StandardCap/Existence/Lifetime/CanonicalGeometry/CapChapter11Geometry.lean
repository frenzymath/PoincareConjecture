import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryNoncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryPinching
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.PartialFlowCapture
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Curvature.Nonnegative

/-!
# Actual standard-cap geometry for the Chapter 11 blow-up hypotheses

The supplied homothety service applies to the retained slice maps.
Completeness gives compact intrinsic balls, the proved sectional sign
gives the nonnegative branch, and the ordinary noncollapse certificate
applies at all points of a fixed positive-time tail.
Source: Morgan-Tian Theorem 12.28, pp. 323-324; unit lifetime derivation,
section 3 and bad-point selection derivation, section 7.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M34

/-- Actual factor-one homothety calculus for every retained cap-flow
slice (Theorem 12.28). -/
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

/-- Every finite intrinsic ball in a retained cap-flow slice has compact
closure, as required by the Chapter 11 blow-up controls (Theorem 12.28). -/
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

/-- The actual cap-flow realization satisfies the full nonnegative branch
of the Chapter 11 hypotheses (Theorem 12.28). -/
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

/-- The frozen cap noncollapse certificate controls every Chapter 11
cylinder whenever the chosen radius fits below the physical time
(Proposition 12.13 and Theorem 12.28). -/
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

end PoincareMT.M34
