import PoincareConjecture.Proofs.M38.PartialCutSmooth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance partialEmptyChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P ∅) :=
  partialCappedChartedSpace F T hT P ∅


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


noncomputable def emptyCutLift (x : (F.slice (F.event T hT).tMinus).carrier) :
    eventCutOpen F T hT P ∅ :=
  ⟨x, by
    change x ∈ (eventCutOpen F T hT P ∅ : Set (F.slice (F.event T hT).tMinus).carrier)
    rw [eventCutOpen_empty]
    exact Set.mem_univ x⟩


@[simp] theorem emptyCutLift_val (x : (F.slice (F.event T hT).tMinus).carrier) :
    (emptyCutLift F T hT P x).val = x := rfl


@[simp] theorem emptyCutLift_subtype (x : eventCutOpen F T hT P ∅) :
    emptyCutLift F T hT P x.val = x := Subtype.ext rfl


theorem emptyCutLift_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (emptyCutLift F T hT P) :=
  (ContMDiff.subtypeVal_comp_iff (eventCutOpen F T hT P ∅) (emptyCutLift F T hT P)).mp
    contMDiff_id


theorem partialOldInverse_empty_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (partialOldInverse F T hT P ∅) := by
  apply contMDiffOn_univ.mp
  have h := partialOldInverse_smooth F T hT P ∅
  rwa [Set.range_eq_univ.mpr (partialOldInclusion_empty_surjective F T hT P)] at h


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


theorem partialEmptyDiffeomorph_apply (q : (partialCappedCarrier F T hT P ∅).carrier) :
    partialEmptyDiffeomorph F T hT P q = (partialOldInverse F T hT P ∅ q).val := rfl


theorem partialEmptyDiffeomorph_symm_apply (x : (F.slice (F.event T hT).tMinus).carrier) :
    (partialEmptyDiffeomorph F T hT P).symm x =
      partialOldInclusion F T hT P ∅ (emptyCutLift F T hT P x) := rfl

end PoincareConjecture.M38
