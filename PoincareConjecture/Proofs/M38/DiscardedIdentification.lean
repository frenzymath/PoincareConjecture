import PoincareConjecture.Proofs.M38.CappingRegions
import PoincareConjecture.Proofs.M38.RegionEquivalences









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)



noncomputable def cappedDiscardedRegionEquivalence (i : Fin (F.event T hT).cap_count) :
    SurgeryRegionEquivalence (cappedDiscardedCarrier F T hT P)
      (F.slice (F.event T hT).tMinus)
      ((⋃ j, (cappedCapBall F T hT P j).closedBall)ᶜ) (F.event T hT).retained_preᶜ := by
  let E := cappedOldRegionEquivalence F T hT P
  let E' : SurgeryRegionEquivalence (cappedDiscardedCarrier F T hT P)
      (openCarrier (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT))
      ((⋃ j, (cappedCapBall F T hT P j).closedBall)ᶜ) Set.univ := {
    map := E.inverse
    inverse := E.map
    map_image := E.inverse_image
    inverse_image := E.map_image
    left_inverse := E.right_inverse
    right_inverse := E.left_inverse
    map_smooth := E.inverse_smooth
    inverse_smooth := E.map_smooth }
  exact composeRegions E' (openRegionEquivalence
    (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT)
    (Classical.choice (P i).discarded_nonempty))



theorem cappedDiscardedRegionEquivalence_map (i : Fin (F.event T hT).cap_count)
    (q : (cappedDiscardedCarrier F T hT P).carrier) :
    (cappedDiscardedRegionEquivalence F T hT P i).map q =
      (cappedOldInverse F T hT P q).val := rfl



theorem cappedDiscardedRegionEquivalence_positive
    (i : Fin (F.event T hT).cap_count) (z : UnitTwoSphere) (s : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (P i).collar (z, s) = (cappedDiscardedRegionEquivalence F T hT P i).map
      ((cappedCapBall F T hT P i).map ((1 + s) • z.val)) := by
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := ⟨Set.mem_univ _, hs⟩
  have hnorm : ‖(1 + s) • z.val‖ = 1 + s := by
    simp [norm_smul, abs_of_pos (by linarith [hs.1] : 0 < 1 + s)]
  let x : capDoubleBall := ⟨(1 + s) • z.val, by
    change dist ((1 + s) • z.val) 0 < 2
    rw [dist_zero_right, hnorm]
    linarith [hs.2]⟩
  have hx : 1 < ‖x.val‖ := by
    change 1 < ‖(1 + s) • z.val‖
    rw [hnorm]
    linarith [hs.1]
  change (P i).collar (z, s) = (cappedDiscardedRegionEquivalence F T hT P i).map
    ((cappedCapBall F T hT P i).map x.val)
  rw [cappedDiscardedRegionEquivalence_map, cappedCapBall_attachment F T hT P i x hx,
    cappedOldInverse_apply, (P i).attachmentChart_apply hx]
  change (P i).collar (z, s) = (P i).collar (capAttachCoordinates (capAttachVector (z, s)))
  rw [capAttachCoordinates_vector hz]

end PoincareConjecture.M38
