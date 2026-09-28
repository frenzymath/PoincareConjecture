import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonCapExteriorFilling
import Mathlib.Tactic












set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D








theorem exists_saddle_nested_pair_common_cap_inputs
    (hP : PlanarSchoenfliesService)
    (BInner BOuter : BallNeighborhoodChart E2 E2)
    (cInner cOuter : UnitCircle → E2)
    (hcInner : IsPlanarEmbedding cInner)
    (hcOuter : IsPlanarEmbedding cOuter)
    (KInner OInner TInner DeltaInner : Set E2)
    (hKInner : IsPreconnected KInner)
    (hOutsideInner : ∃ x ∈ KInner, x ∉ BInner.closedRegion)
    (hCurveInner : range cInner ⊆ BInner.closedRegion)
    (hCurveKInner : Disjoint (range cInner) KInner)
    (hOtherInner : OInner ⊆ BInner.closedRegionᶜ)
    (hTailInner : TInner ⊆ BInner.boundary)
    (hMeetInner : range cInner ∩ TInner ⊆ DeltaInner)
    (KOuter OOuter TOuter DeltaOuter : Set E2)
    (hKOuter : IsPreconnected KOuter)
    (hOutsideOuter : ∃ x ∈ KOuter, x ∉ BOuter.closedRegion)
    (hCurveOuter : range cOuter ⊆ BOuter.closedRegion)
    (hCurveKOuter : Disjoint (range cOuter) KOuter)
    (hOtherOuter : OOuter ⊆ BOuter.closedRegionᶜ)
    (hTailOuter : TOuter ⊆ BOuter.boundary)
    (hMeetOuter : range cOuter ∩ TOuter ⊆ DeltaOuter) :
    ∃ (DInner DOuter : BallNeighborhoodChart E2 E2)
      (WInner WOuter : Set E2),
      DInner.boundary = range cInner ∧
      DInner.closedRegion ⊆ BInner.closedRegion ∧
      DInner.closedRegion ∩ (KInner ∪ OInner ∪ TInner) ⊆ DeltaInner ∧
      WInner = DInner.closedRegionᶜ ∧
      IsOpen WInner ∧ IsConnected WInner ∧ ¬ Bornology.IsBounded WInner ∧
      Disjoint WInner (range cInner) ∧
      (KInner ∪ OInner ∪ TInner) \ DeltaInner ⊆ WInner ∧
      DOuter.boundary = range cOuter ∧
      DOuter.closedRegion ⊆ BOuter.closedRegion ∧
      DOuter.closedRegion ∩ (KOuter ∪ OOuter ∪ TOuter) ⊆ DeltaOuter ∧
      WOuter = DOuter.closedRegionᶜ ∧
      IsOpen WOuter ∧ IsConnected WOuter ∧ ¬ Bornology.IsBounded WOuter ∧
      Disjoint WOuter (range cOuter) ∧
      (KOuter ∪ OOuter ∪ TOuter) \ DeltaOuter ⊆ WOuter := by
  obtain ⟨DInner, hDInnerBoundary, hDInnerSubset, hDInnerProtect, hDInnerW⟩ :=
    exists_saddle_common_cap_exterior_filling hP BInner cInner hcInner
      KInner OInner TInner DeltaInner hKInner hOutsideInner hCurveInner hCurveKInner
      hOtherInner hTailInner hMeetInner
  obtain ⟨DOuter, hDOuterBoundary, hDOuterSubset, hDOuterProtect, hDOuterW⟩ :=
    exists_saddle_common_cap_exterior_filling hP BOuter cOuter hcOuter
      KOuter OOuter TOuter DeltaOuter hKOuter hOutsideOuter hCurveOuter hCurveKOuter
      hOtherOuter hTailOuter hMeetOuter
  dsimp only at hDInnerW hDOuterW
  rcases hDInnerW with
    ⟨hInnerOpen, hInnerConnected, hInnerUnbounded, hInnerDisjoint, hInnerOutside⟩
  rcases hDOuterW with
    ⟨hOuterOpen, hOuterConnected, hOuterUnbounded, hOuterDisjoint, hOuterOutside⟩
  refine ⟨DInner, DOuter, DInner.closedRegionᶜ, DOuter.closedRegionᶜ, ?_⟩
  exact ⟨hDInnerBoundary, hDInnerSubset, hDInnerProtect, rfl, hInnerOpen,
    hInnerConnected, hInnerUnbounded, hInnerDisjoint, hInnerOutside,
    hDOuterBoundary, hDOuterSubset, hDOuterProtect, rfl, hOuterOpen,
    hOuterConnected, hOuterUnbounded, hOuterDisjoint, hOuterOutside⟩

end PoincareConjecture.M25.Topology3D
