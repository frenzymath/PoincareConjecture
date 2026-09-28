import PoincareConjecture.Proofs.M38.PartialCutCharts
import PoincareConjecture.Proofs.M38.CappingInclusions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

noncomputable def partialCappingInclude (j : PartialCappingIndex F T hT P S)
    (x : partialCappingDomain F T hT P S j) : PartialCappedSpace F T hT P S :=
  (partialCappingOverlap F T hT P S).include j x

theorem partialCappingInclude_openEmbedding (j : PartialCappingIndex F T hT P S) :
    IsOpenEmbedding (partialCappingInclude F T hT P S j) :=
  (partialCappingOverlap F T hT P S).include_isOpenEmbedding j

theorem partialCappingMap_old_center (x : eventCutOpen F T hT P S) :
    partialCappingMap F T hT P S (.inl x)
      ⟨chartAt StandardCapSpace x x,
        (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩ = x :=
  (chartAt StandardCapSpace x).left_inv (mem_chart_source _ x)

theorem partialCappingMap_old_cover :
    (⋃ x : eventCutOpen F T hT P S,
      Set.range (partialCappingMap F T hT P S (.inl x))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨x, ?_⟩
  exact ⟨⟨chartAt StandardCapSpace x x,
    (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩,
      partialCappingMap_old_center F T hT P S x⟩

theorem exists_partialOldInclusion :
    ∃ f : eventCutOpen F T hT P S → PartialCappedSpace F T hT P S,
      IsOpenEmbedding f ∧ ∀ x z,
        f (partialCappingMap F T hT P S (.inl x) z) =
          partialCappingInclude F T hT P S (.inl x) z := by
  let q : ∀ x : eventCutOpen F T hT P S,
      partialCappingDomain F T hT P S (.inl x) → eventCutOpen F T hT P S :=
    fun x => partialCappingMap F T hT P S (.inl x)
  let f := fun x : eventCutOpen F T hT P S => partialCappingInclude F T hT P S (.inl x)
  obtain ⟨G, hG, hGq⟩ := Poincare.Gluing.exists_isOpenEmbedding_iUnion_ranges
    (q := q) (partialCappingMap_old_openEmbedding F T hT P S)
    (f := f) (fun x => partialCappingInclude_openEmbedding F T hT P S (.inl x))
    (fun x y a b => cappingOverlap_include_iff_image (partialCappingMap F T hT P S)
      (i := .inl x) (j := .inl y) (x := a) (y := b)
      (by rw [partialCappingMap_old_source]; exact Set.mem_univ _)
      (by rw [partialCappingMap_old_source]; exact Set.mem_univ _))
  let H : eventCutOpen F T hT P S ≃ₜ (⋃ x, Set.range (q x)) :=
    (Homeomorph.Set.univ _).symm.trans
      (Homeomorph.setCongr (partialCappingMap_old_cover F T hT P S).symm)
  refine ⟨G ∘ H, hG.comp H.isOpenEmbedding, ?_⟩
  intro x z
  have hH : H (q x z) = ⟨q x z, Set.mem_iUnion.mpr ⟨x, Set.mem_range_self z⟩⟩ :=
    Subtype.ext rfl
  rw [Function.comp_apply, hH]
  exact hGq x z

noncomputable def partialOldInclusion :
    eventCutOpen F T hT P S → PartialCappedSpace F T hT P S :=
  Classical.choose (exists_partialOldInclusion F T hT P S)

theorem partialOldInclusion_openEmbedding : IsOpenEmbedding (partialOldInclusion F T hT P S) :=
  (Classical.choose_spec (exists_partialOldInclusion F T hT P S)).1

theorem partialOldInclusion_patch (x : eventCutOpen F T hT P S)
    (z : partialCappingDomain F T hT P S (.inl x)) :
    partialOldInclusion F T hT P S (partialCappingMap F T hT P S (.inl x) z) =
      partialCappingInclude F T hT P S (.inl x) z :=
  (Classical.choose_spec (exists_partialOldInclusion F T hT P S)).2 x z

theorem partialOldInclusion_cap (a : S × Bool) (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    partialOldInclusion F T hT P S (cutAttachmentChart F T hT P S a x) =
      partialCappingInclude F T hT P S (.inr a) x := by
  let y := cutAttachmentChart F T hT P S a x
  let z : partialCappingDomain F T hT P S (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  have hz := partialOldInclusion_patch F T hT P S y z
  rw [show partialCappingMap F T hT P S (.inl y) z = y from
    partialCappingMap_old_center F T hT P S y] at hz
  apply hz.trans
  apply (cappingOverlap_include_iff_image (partialCappingMap F T hT P S)
    (i := .inl y) (j := .inr a)
    (by rw [partialCappingMap_old_source]; exact Set.mem_univ _)
    (by change x ∈ (cutAttachmentChart F T hT P S a).source
        rwa [cutAttachmentChart_source])).mpr
  exact partialCappingMap_old_center F T hT P S y

end PoincareConjecture.M38
