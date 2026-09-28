import PoincareConjecture.Proofs.M38.FullCutSides

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable def fullCutDiscardedPatch (j : EventCappingIndex F T hT) :
    eventCappingDomain F T hT j → PartialCappedSpace F T hT P Set.univ :=
  match j with
  | .inl y => partialOldInclusion F T hT P Set.univ ∘
      fullCutDiscarded F T hT P ∘ eventCappingMap F T hT P (.inl y)
  | .inr i => partialCappingInclude F T hT P Set.univ
      (.inr (⟨i, Set.mem_univ i⟩, true))

theorem fullCutDiscardedPatch_openEmbedding (j : EventCappingIndex F T hT) :
    IsOpenEmbedding (fullCutDiscardedPatch F T hT P j) := by
  cases j with
  | inl y =>
      exact (partialOldInclusion_openEmbedding F T hT P Set.univ).comp
        ((fullCutDiscarded_openEmbedding F T hT P).comp
          (eventCappingMap_old_openEmbedding F T hT P y))
  | inr i => exact partialCappingInclude_openEmbedding F T hT P Set.univ _

theorem fullCutDiscarded_old_cap_iff (y : eventDiscardedOpen F T hT)
    (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    partialOldInclusion F T hT P Set.univ (fullCutDiscarded F T hT P y) =
      partialCappingInclude F T hT P Set.univ (.inr (⟨i, Set.mem_univ i⟩, true)) x ↔
        cappedOldInclusion F T hT P y = eventCappingInclude F T hT P (.inr i) x := by
  rw [partialOldInclusion_eq_cap_iff, cappedOldInclusion_eq_cap_iff]
  apply and_congr_right
  intro hx
  rw [fullCut_positive_attachment F T hT P i x hx]
  exact (fullCutDiscarded_openEmbedding F T hT P).injective.eq_iff

theorem fullCutDiscardedPatch_eq_iff (j k : EventCappingIndex F T hT)
    (x : eventCappingDomain F T hT j) (y : eventCappingDomain F T hT k) :
    fullCutDiscardedPatch F T hT P j x = fullCutDiscardedPatch F T hT P k y ↔
      eventCappingInclude F T hT P j x = eventCappingInclude F T hT P k y := by
  cases j with
  | inl a =>
      cases k with
      | inl b =>
          rw [← cappedOldInclusion_patch F T hT P a x,
            ← cappedOldInclusion_patch F T hT P b y]
          change partialOldInclusion F T hT P Set.univ
            (fullCutDiscarded F T hT P (eventCappingMap F T hT P (.inl a) x)) =
              partialOldInclusion F T hT P Set.univ
                (fullCutDiscarded F T hT P (eventCappingMap F T hT P (.inl b) y)) ↔ _
          rw [(partialOldInclusion_openEmbedding F T hT P Set.univ).injective.eq_iff,
            (fullCutDiscarded_openEmbedding F T hT P).injective.eq_iff,
            (cappedOldInclusion_openEmbedding F T hT P).injective.eq_iff]
      | inr b =>
          rw [← cappedOldInclusion_patch F T hT P a x]
          exact fullCutDiscarded_old_cap_iff F T hT P
            (eventCappingMap F T hT P (.inl a) x) b y
  | inr a =>
      cases k with
      | inl b =>
          rw [eq_comm, ← cappedOldInclusion_patch F T hT P b y]
          exact (fullCutDiscarded_old_cap_iff F T hT P
            (eventCappingMap F T hT P (.inl b) y) a x).trans eq_comm
      | inr b =>
          by_cases hab : a = b
          · subst b
            exact (fullCutDiscardedPatch_openEmbedding F T hT P (.inr a)).injective.eq_iff.trans
              (eventCappingInclude_openEmbedding F T hT P (.inr a)).injective.eq_iff.symm
          · constructor
            · intro h
              exfalso
              exact Set.disjoint_left.mp (partialCapPatch_disjoint F T hT P Set.univ
                (⟨a, Set.mem_univ a⟩, true) (⟨b, Set.mem_univ b⟩, true)
                (fun he => hab (congrArg (fun z => z.1.val) he)))
                  (Set.mem_range_self x) ⟨y, h.symm⟩
            · intro h
              exfalso
              exact Set.disjoint_left.mp (cappedCapPatch_disjoint F T hT P a b hab)
                (Set.mem_range_self x) (h.symm ▸ Set.mem_range_self y)

theorem fullCutDiscardedPatch_cover :
    (⋃ j, Set.range (eventCappingInclude F T hT P j)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      exact Set.mem_iUnion.mpr ⟨j, x, rfl⟩

theorem exists_fullCutDiscardedInclusion :
    ∃ f : CappedDiscardedSpace F T hT P → PartialCappedSpace F T hT P Set.univ,
      IsOpenEmbedding f ∧ ∀ j x,
        f (eventCappingInclude F T hT P j x) = fullCutDiscardedPatch F T hT P j x := by
  obtain ⟨G, hG, hGq⟩ := Poincare.Gluing.exists_isOpenEmbedding_iUnion_ranges
    (q := eventCappingInclude F T hT P) (eventCappingInclude_openEmbedding F T hT P)
    (f := fullCutDiscardedPatch F T hT P) (fullCutDiscardedPatch_openEmbedding F T hT P)
    (fullCutDiscardedPatch_eq_iff F T hT P)
  let H : CappedDiscardedSpace F T hT P ≃ₜ
      (⋃ j, Set.range (eventCappingInclude F T hT P j)) :=
    (Homeomorph.Set.univ _).symm.trans
      (Homeomorph.setCongr (fullCutDiscardedPatch_cover F T hT P).symm)
  refine ⟨G ∘ H, hG.comp H.isOpenEmbedding, ?_⟩
  intro j x
  have hH : H (eventCappingInclude F T hT P j x) =
      ⟨eventCappingInclude F T hT P j x, Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩⟩ :=
    Subtype.ext rfl
  rw [Function.comp_apply, hH]
  exact hGq j x

noncomputable def fullCutDiscardedInclusion :
    CappedDiscardedSpace F T hT P → PartialCappedSpace F T hT P Set.univ :=
  Classical.choose (exists_fullCutDiscardedInclusion F T hT P)

theorem fullCutDiscardedInclusion_openEmbedding :
    IsOpenEmbedding (fullCutDiscardedInclusion F T hT P) :=
  (Classical.choose_spec (exists_fullCutDiscardedInclusion F T hT P)).1

theorem fullCutDiscardedInclusion_patch (j : EventCappingIndex F T hT)
    (x : eventCappingDomain F T hT j) :
    fullCutDiscardedInclusion F T hT P (eventCappingInclude F T hT P j x) =
      fullCutDiscardedPatch F T hT P j x :=
  (Classical.choose_spec (exists_fullCutDiscardedInclusion F T hT P)).2 j x

theorem fullCutDiscardedInclusion_old (y : eventDiscardedOpen F T hT) :
    fullCutDiscardedInclusion F T hT P (cappedOldInclusion F T hT P y) =
      partialOldInclusion F T hT P Set.univ (fullCutDiscarded F T hT P y) := by
  let z : eventCappingDomain F T hT (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  have h := fullCutDiscardedInclusion_patch F T hT P (.inl y) z
  rw [← cappedOldInclusion_patch F T hT P y z] at h
  change fullCutDiscardedInclusion F T hT P
    (cappedOldInclusion F T hT P (eventCappingMap F T hT P (.inl y) z)) =
      partialOldInclusion F T hT P Set.univ
        (fullCutDiscarded F T hT P (eventCappingMap F T hT P (.inl y) z)) at h
  rwa [eventCappingMap_old_center] at h

theorem fullCutDiscardedInclusion_cap (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    fullCutDiscardedInclusion F T hT P (eventCappingInclude F T hT P (.inr i) x) =
      partialCappingInclude F T hT P Set.univ (.inr (⟨i, Set.mem_univ i⟩, true)) x :=
  fullCutDiscardedInclusion_patch F T hT P (.inr i) x

end PoincareConjecture.M38
