import PoincareLib.Topology.Manifold.Surgery.Event.Partial.PartialCutSmooth

/-!
# Empty partial capping is the actual pre-slice

With no selected spheres there are only ordinary charts. Their old
inclusion is surjective and its actual inverse identifies the quotient
smoothly with the stored pre-surgery slice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance partialEmptyChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P ∅) :=
  partialCappedChartedSpace F T hT P ∅

/-- With no new patches, the old inclusion covers the entire actual quotient. -/
theorem partialOldInclusion_empty_surjective :
    Function.Surjective (partialOldInclusion F T hT P ∅) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      cases j with
      | inl y => exact ⟨partialCappingMap F T hT P ∅ (.inl y) x,
          partialOldInclusion_patch F T hT P ∅ y x⟩
      | inr a => exact (Set.notMem_empty a.1.val a.1.property).elim

/-- Every pre-slice point belongs to the empty-selection old domain. -/
noncomputable def emptyCutLift (x : (F.slice (F.event T hT).tMinus).carrier) :
    eventCutOpen F T hT P ∅ :=
  ⟨x, by
    change x ∈ (eventCutOpen F T hT P ∅ : Set (F.slice (F.event T hT).tMinus).carrier)
    rw [eventCutOpen_empty]
    exact Set.mem_univ x⟩

/-- This lift is the identity on the underlying pre-slice points. -/
@[simp] theorem emptyCutLift_val (x : (F.slice (F.event T hT).tMinus).carrier) :
    (emptyCutLift F T hT P x).val = x := rfl

/-- Lifting the underlying point of an old-domain element recovers that element. -/
@[simp] theorem emptyCutLift_subtype (x : eventCutOpen F T hT P ∅) :
    emptyCutLift F T hT P x.val = x := Subtype.ext rfl

/-- The empty-domain lift is smooth in the inherited open atlas. -/
theorem emptyCutLift_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (emptyCutLift F T hT P) :=
  (ContMDiff.subtypeVal_comp_iff (eventCutOpen F T hT P ∅) (emptyCutLift F T hT P)).mp
    contMDiff_id

/-- The actual old inverse is smooth everywhere when there are no added balls. -/
theorem partialOldInverse_empty_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (partialOldInverse F T hT P ∅) := by
  apply contMDiffOn_univ.mp
  have h := partialOldInverse_smooth F T hT P ∅
  rwa [Set.range_eq_univ.mpr (partialOldInclusion_empty_surjective F T hT P)] at h

/-- The empty-selection capped carrier is smoothly identified with the literal pre-slice. -/
noncomputable def partialEmptyDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) (partialCappedCarrier F T hT P ∅).carrier
      (F.slice (F.event T hT).tMinus).carrier ∞ where
  toFun := Subtype.val ∘ partialOldInverse F T hT P ∅
  invFun := partialOldInclusion F T hT P ∅ ∘ emptyCutLift F T hT P
  left_inv := by
    intro q
    simp only [Function.comp_apply, emptyCutLift_subtype]
    exact partialOldInverse_right F T hT P ∅ (partialOldInclusion_empty_surjective F T hT P q)
  right_inv := by
    intro x
    simp only [Function.comp_apply, partialOldInverse_apply, emptyCutLift_val]
  contMDiff_toFun := contMDiff_subtype_val.comp (partialOldInverse_empty_smooth F T hT P)
  contMDiff_invFun := (partialOldInclusion_smooth F T hT P ∅).comp (emptyCutLift_smooth F T hT P)

/-- The forward empty-selection identification is the actual old inverse followed by inclusion. -/
theorem partialEmptyDiffeomorph_apply (q : (partialCappedCarrier F T hT P ∅).carrier) :
    partialEmptyDiffeomorph F T hT P q = (partialOldInverse F T hT P ∅ q).val := rfl

/-- The inverse empty-selection identification is the same actual old inclusion. -/
theorem partialEmptyDiffeomorph_symm_apply (x : (F.slice (F.event T hT).tMinus).carrier) :
    (partialEmptyDiffeomorph F T hT P).symm x =
      partialOldInclusion F T hT P ∅ (emptyCutLift F T hT P x) := rfl

end PoincareMT.M38
