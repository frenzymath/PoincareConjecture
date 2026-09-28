import PoincareConjecture.Proofs.M38.EventCappingCharts
import PoincareConjecture.Proofs.M07.Topology.Gluing.Embedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.M38

theorem cappingOverlap_include_iff_image {I : Type u} {P : I → Type v} {O : Type w}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace O]
    (e : ∀ i, OpenPartialHomeomorph (P i) O) {i j : I} {x : P i} {y : P j}
    (hx : x ∈ (e i).source) (hy : y ∈ (e j).source) :
    (cappingOverlap e).include i x = (cappingOverlap e).include j y ↔ e i x = e j y := by
  by_cases hij : i = j
  · subst j
    constructor
    · intro h
      exact congrArg (e i) ((cappingOverlap e).include_injective i h)
    · intro h
      exact congrArg ((cappingOverlap e).include i) ((e i).injOn hx hy h)
  · rw [(cappingOverlap e).include_eq_iff]
    change (x ∈ (cappingTransition e i j).source ∧ cappingTransition e i j x = y) ↔ _
    rw [cappingTransition_graph e hij]
    exact ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable def eventCappingInclude (j : EventCappingIndex F T hT)
    (x : eventCappingDomain F T hT j) : CappedDiscardedSpace F T hT P :=
  (eventCappingOverlap F T hT P).include j x

theorem eventCappingInclude_openEmbedding (j : EventCappingIndex F T hT) :
    IsOpenEmbedding (eventCappingInclude F T hT P j) :=
  (eventCappingOverlap F T hT P).include_isOpenEmbedding j

theorem eventCappingMap_old_center (x : eventDiscardedOpen F T hT) :
    eventCappingMap F T hT P (.inl x)
      ⟨chartAt StandardCapSpace x x,
        (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩ = x :=
  (chartAt StandardCapSpace x).left_inv (mem_chart_source _ x)

theorem eventCappingMap_old_cover :
    (⋃ x : eventDiscardedOpen F T hT,
      Set.range (eventCappingMap F T hT P (.inl x))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨x, ?_⟩
  exact ⟨⟨chartAt StandardCapSpace x x,
    (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩,
      eventCappingMap_old_center F T hT P x⟩

theorem exists_cappedOldInclusion :
    ∃ f : eventDiscardedOpen F T hT → CappedDiscardedSpace F T hT P,
      IsOpenEmbedding f ∧ ∀ x z,
        f (eventCappingMap F T hT P (.inl x) z) = eventCappingInclude F T hT P (.inl x) z := by
  let q : ∀ x : eventDiscardedOpen F T hT,
      eventCappingDomain F T hT (.inl x) → eventDiscardedOpen F T hT :=
    fun x => eventCappingMap F T hT P (.inl x)
  let f := fun x : eventDiscardedOpen F T hT => eventCappingInclude F T hT P (.inl x)
  obtain ⟨G, hG, hGq⟩ := Poincare.Gluing.exists_isOpenEmbedding_iUnion_ranges
    (q := q) (eventCappingMap_old_openEmbedding F T hT P)
    (f := f) (fun x => eventCappingInclude_openEmbedding F T hT P (.inl x))
    (fun x y a b => cappingOverlap_include_iff_image (eventCappingMap F T hT P)
      (i := .inl x) (j := .inl y) (x := a) (y := b)
      (by rw [eventCappingMap_old_source]; exact Set.mem_univ _)
      (by rw [eventCappingMap_old_source]; exact Set.mem_univ _))
  let H : eventDiscardedOpen F T hT ≃ₜ (⋃ x, Set.range (q x)) :=
    (Homeomorph.Set.univ _).symm.trans
      (Homeomorph.setCongr (eventCappingMap_old_cover F T hT P).symm)
  refine ⟨G ∘ H, hG.comp H.isOpenEmbedding, ?_⟩
  intro x z
  have hH : H (q x z) = ⟨q x z, Set.mem_iUnion.mpr ⟨x, Set.mem_range_self z⟩⟩ :=
    Subtype.ext rfl
  rw [Function.comp_apply, hH]
  exact hGq x z

noncomputable def cappedOldInclusion :
    eventDiscardedOpen F T hT → CappedDiscardedSpace F T hT P :=
  Classical.choose (exists_cappedOldInclusion F T hT P)

theorem cappedOldInclusion_openEmbedding : IsOpenEmbedding (cappedOldInclusion F T hT P) :=
  (Classical.choose_spec (exists_cappedOldInclusion F T hT P)).1

theorem cappedOldInclusion_patch (x : eventDiscardedOpen F T hT)
    (z : eventCappingDomain F T hT (.inl x)) :
    cappedOldInclusion F T hT P (eventCappingMap F T hT P (.inl x) z) =
      eventCappingInclude F T hT P (.inl x) z :=
  (Classical.choose_spec (exists_cappedOldInclusion F T hT P)).2 x z

end PoincareConjecture.M38
