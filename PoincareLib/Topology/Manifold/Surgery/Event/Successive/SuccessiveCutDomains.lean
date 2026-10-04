import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutOverlap

/-!
# Old-domain and signed-index inclusions for successive actual cuts

Enlarging the selected family removes exactly the newly selected spheres.
The old-domain inclusion and shared signed indices preserve actual points
and attaching coordinates on their strict annular domains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S R : Set (Fin (F.event T hT).cap_count)) (hSR : S ⊆ R)

include hSR

/-- Inclusion of selections preserves the literal central sphere union. -/
theorem eventCutSpheres_mono : eventCutSpheres F T hT P S ⊆ eventCutSpheres F T hT P R := by
  rintro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨i.val, hSR i.property⟩, hi⟩

/-- The larger selection consists of the previous spheres and exactly the new ones. -/
theorem eventCutSpheres_difference :
    eventCutSpheres F T hT P R =
      eventCutSpheres F T hT P S ∪ eventCutSpheres F T hT P (R \ S) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    by_cases hs : i.val ∈ S
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i.val, hs⟩, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i.val, i.property, hs⟩, hi⟩)
  · rintro x (hx | hx)
    · exact eventCutSpheres_mono F T hT P S R hSR hx
    · exact eventCutSpheres_mono F T hT P (R \ S) R Set.diff_subset hx

/-- The old domain of the larger selection lies in the old domain of the smaller one. -/
theorem eventCutOpen_antitone : eventCutOpen F T hT P R ≤ eventCutOpen F T hT P S :=
  Set.compl_subset_compl.mpr (eventCutSpheres_mono F T hT P S R hSR)

/-- This inherited inclusion keeps the same actual pre-surgery point. -/
noncomputable def successiveOldInclusion :
    eventCutOpen F T hT P R → eventCutOpen F T hT P S :=
  TopologicalSpace.Opens.inclusion (eventCutOpen_antitone F T hT P S R hSR)

/-- The old-domain inclusion is an open embedding for the inherited topologies. -/
theorem successiveOldInclusion_openEmbedding :
    IsOpenEmbedding (successiveOldInclusion F T hT P S R hSR) :=
  .inclusion (eventCutOpen_antitone F T hT P S R hSR)
    ((eventCutOpen F T hT P R).isOpen.preimage continuous_subtype_val)

/-- Every shared ball index retains its exact surgery index and side. -/
def successiveCapIndex (a : S × Bool) : R × Bool :=
  (⟨a.1.val, hSR a.1.property⟩, a.2)

/-- Distinct shared signed balls stay distinct after enlarging the selection. -/
theorem successiveCapIndex_injective :
    Function.Injective (successiveCapIndex F T hT S R hSR) := by
  intro a b h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun z => z.1.val) h)
  · exact congrArg (fun z : R × Bool => z.2) h

/-- The annular attachments agree at exactly their specified outer ball coordinates. -/
theorem successive_attachment (a : S × Bool) (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    successiveOldInclusion F T hT P S R hSR
      (cutAttachmentChart F T hT P R (successiveCapIndex F T hT S R hSR a) x) =
        cutAttachmentChart F T hT P S a x := by
  apply Subtype.ext
  change (cutAttachmentChart F T hT P R (successiveCapIndex F T hT S R hSR a) x).val = _
  rw [cutAttachmentChart_apply F T hT P R _ hx,
    cutAttachmentChart_apply F T hT P S _ hx]
  rfl

/-- Membership in the smaller old domain fails to survive precisely at a newly removed sphere. -/
theorem successive_old_mem_iff (y : eventCutOpen F T hT P S) :
    y.val ∈ eventCutOpen F T hT P R ↔ y.val ∉ eventCutSpheres F T hT P (R \ S) := by
  change y.val ∉ eventCutSpheres F T hT P R ↔ _
  rw [eventCutSpheres_difference F T hT P S R hSR]
  exact not_or.trans (and_iff_right y.property)

end PoincareMT.M38
