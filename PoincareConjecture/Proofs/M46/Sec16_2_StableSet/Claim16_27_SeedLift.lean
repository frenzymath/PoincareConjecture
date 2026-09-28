import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderTail
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricComparison
import PoincareConjecture.Proofs.M46.RegularSpacetime
import PoincareConjecture.Proofs.M13.GeneralizedSlices
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M33.GuardedCylinders











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

variable {F : SurgeryFlowData.{u}} {window : M33RegularHistoryWindow F}



theorem exists_realized_seed_cylinder (R : M46RegularSpacetimeData window)
    {C : GeneralizedSliceCarrier.{u}} {origin d duration : ℝ}
    (hd : 0 < d) (hduration : d < duration)
    {J : SpacetimeInterval} (hJ : J.domain = Icc (-d) 0)
    {U : TopologicalSpace.Opens C.carrier}
    (e : SurgeryFlowCylinder F C origin 1 (Icc (-duration) 0) U)
    (htime : ∀ s ∈ J.domain, origin + s / 1 ∈ R.history.generalized.interval) :
    ∃ lifted : GeneralizedFlowCylinder R.history.generalized C origin 1 J.domain U,
      (∀ s hs x, x ∈ U →
        R.history.history.forward (origin + s / 1) (htime s hs)
          (lifted.forward s hs x) = e.forward s
            (show s ∈ Icc (-duration) 0 from by
              have h := hJ ▸ hs; exact ⟨by linarith [h.1], h.2⟩) x) ∧
      (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
        lifted.pullbackInner s hs x v w = e.pullbackInner s
          (show s ∈ Icc (-duration) 0 from by
            have h := hJ ▸ hs; exact ⟨by linarith [h.1], h.2⟩) x v w) := by
  have hsub : J.domain ⊆ Icc (-duration) 0 := by
    rw [hJ]
    exact Icc_subset_Icc (by linarith) le_rfl
  let short := e.restrict hsub J.ordConnected (Subset.refl (U : Set C.carrier))
  have hregular (s : ℝ) (hs : s ∈ J.domain) :
      short.forward s hs '' U ⊆ m33RegularRegion F (origin + s / 1) := by
    have hsJ : s ∈ Icc (-d) 0 := hJ ▸ hs
    exact e.regular_image_of_earlier (hsub hs)
      ⟨-duration, ⟨le_rfl, by linarith⟩, by linarith [hsJ.1]⟩
  exact R.history.cylinders_from_surgery C origin 1 J.domain U U.isOpen htime short hregular



theorem realized_seed_cylinder_scalar (P : M46Predecessors.{u})
    (R : M46RegularSpacetimeData window)
    {C : GeneralizedSliceCarrier.{u}} {origin : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder R.history.generalized C origin 1 J.domain U)
    (s : ℝ) (hs : s ∈ J.domain) (htime : origin + s / 1 ∈ R.history.generalized.interval)
    (x : U) :
    horizontalScalarCurvature R.geometry.toLGeometry.leafwise (e.pointMap s hs x.val) =
      (F.connection (origin + s / 1)).scalarCurvature
        (R.history.history.forward (origin + s / 1) htime (e.forward s hs x.val)) := by
  change horizontalScalarCurvature R.geometry.leafwise
    (⟨origin + s / 1, e.forward s hs x.val⟩ : R.history.generalized.point) = _
  rw [M13.originalSlice_scalar R.geometry P.m13,
    ← R.history.scalar_pullback (origin + s / 1) htime]

end PoincareConjecture.Proofs.M46
