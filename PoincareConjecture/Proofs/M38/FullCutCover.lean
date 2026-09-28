import PoincareConjecture.Proofs.M38.FullCutPost
import PoincareConjecture.Proofs.M38.FullCutDiscarded
import PoincareConjecture.Proofs.M38.OneCapAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

theorem fullCutPostInclusion_cases (p : (F.slice T).carrier) :
    (∃ y : eventCapComplementOpen F T hT, fullCutPostInclusion F T hT P p =
      partialOldInclusion F T hT P Set.univ (fullCutPostOld F T hT P y)) ∨
    ∃ i : Fin (F.event T hT).cap_count, ∃ x : capDoubleBall,
      fullCutPostInclusion F T hT P p = partialCappingInclude F T hT P Set.univ
        (.inr (⟨i, Set.mem_univ i⟩, false)) x := by
  obtain ⟨j, hj⟩ := retainedPatch_cover F T hT P p
  have hp := mem_of_mem_nhds hj
  cases j with
  | none => exact Or.inl ⟨⟨p, hp⟩, fullCutPostInclusion_old F T hT P ⟨p, hp⟩⟩
  | some i =>
      obtain ⟨x, hx⟩ := (postBallPatchHomeomorph F T hT P i).surjective ⟨p, hp⟩
      have hval : (P i).ball.map x.val = p := congrArg Subtype.val hx
      exact Or.inr ⟨i, x, hval ▸ fullCutPostInclusion_cap F T hT P i x⟩

theorem fullCutDiscardedInclusion_cases (p : CappedDiscardedSpace F T hT P) :
    (∃ y : eventDiscardedOpen F T hT,
      fullCutDiscardedInclusion F T hT P p =
        partialOldInclusion F T hT P Set.univ (fullCutDiscarded F T hT P y)) ∨
    ∃ i : Fin (F.event T hT).cap_count, ∃ x : capDoubleBall,
      fullCutDiscardedInclusion F T hT P p = partialCappingInclude F T hT P Set.univ
        (.inr (⟨i, Set.mem_univ i⟩, true)) x := by
  induction p using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      cases j with
      | inl y => exact Or.inl ⟨eventCappingMap F T hT P (.inl y) x,
          fullCutDiscardedInclusion_patch F T hT P (.inl y) x⟩
      | inr i => exact Or.inr ⟨i, x, fullCutDiscardedInclusion_cap F T hT P i x⟩

theorem fullCutInclusions_disjoint :
    Disjoint (Set.range (fullCutPostInclusion F T hT P))
      (Set.range (fullCutDiscardedInclusion F T hT P)) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨p, rfl⟩ ⟨d, hd⟩
  have h := hd.symm
  rcases fullCutPostInclusion_cases F T hT P p with ⟨y, hy⟩ | ⟨i, x, hx⟩
  · rcases fullCutDiscardedInclusion_cases F T hT P d with ⟨z, hz⟩ | ⟨j, x, hx⟩
    · rw [hy, hz] at h
      have he := (partialOldInclusion_openEmbedding F T hT P Set.univ).injective h
      exact Set.disjoint_left.mp (fullCut_old_sides_disjoint F T hT P)
        (Set.mem_range_self y) (he.symm ▸ Set.mem_range_self z)
    · rw [hy, hx] at h
      obtain ⟨hn, he⟩ := (partialOldInclusion_eq_cap_iff F T hT P Set.univ
        (fullCutPostOld F T hT P y) (⟨j, Set.mem_univ j⟩, true) x).mp h
      rw [fullCut_positive_attachment F T hT P j x hn] at he
      exact Set.disjoint_left.mp (fullCut_old_sides_disjoint F T hT P)
        (Set.mem_range_self y) (he.symm ▸ Set.mem_range_self ((P j).attachmentChart x))
  · rcases fullCutDiscardedInclusion_cases F T hT P d with ⟨z, hz⟩ | ⟨j, y, hy⟩
    · rw [hx, hz] at h
      obtain ⟨hn, he⟩ := (partialOldInclusion_eq_cap_iff F T hT P Set.univ
        (fullCutDiscarded F T hT P z) (⟨i, Set.mem_univ i⟩, false) x).mp h.symm
      rw [fullCut_negative_attachment F T hT P i x hn] at he
      exact Set.disjoint_left.mp (fullCut_old_sides_disjoint F T hT P)
        (he.symm ▸ Set.mem_range_self
          (⟨(P i).ball.map x.val, ((P i).ball_mem_cap_complement_iff x.property).mpr hn⟩ :
            eventCapComplementOpen F T hT)) (Set.mem_range_self z)
    · rw [hx, hy] at h
      exact Set.disjoint_left.mp (partialCapPatch_disjoint F T hT P Set.univ
        (⟨i, Set.mem_univ i⟩, false) (⟨j, Set.mem_univ j⟩, true) (by simp))
          (Set.mem_range_self x) (h.symm ▸ Set.mem_range_self y)

theorem fullCutInclusions_cover :
    Set.range (fullCutPostInclusion F T hT P) ∪
      Set.range (fullCutDiscardedInclusion F T hT P) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      cases j with
      | inl y =>
          let z := partialCappingMap F T hT P Set.univ (.inl y) x
          have hz : z ∈ Set.range (fullCutPostOld F T hT P) ∪
              Set.range (fullCutDiscarded F T hT P) := by
            rw [fullCut_old_cover]
            exact Set.mem_univ z
          rcases hz with ⟨r, hr⟩ | ⟨d, hd⟩
          · refine Or.inl ⟨r.val, ?_⟩
            rw [fullCutPostInclusion_old, hr]
            exact partialOldInclusion_patch F T hT P Set.univ y x
          · refine Or.inr ⟨cappedOldInclusion F T hT P d, ?_⟩
            rw [fullCutDiscardedInclusion_old, hd]
            exact partialOldInclusion_patch F T hT P Set.univ y x
      | inr a =>
          rcases a with ⟨i, positive⟩
          cases positive with
          | false => exact Or.inl ⟨(P i.val).ball.map x.val,
              fullCutPostInclusion_cap F T hT P i.val x⟩
          | true => exact Or.inr ⟨eventCappingInclude F T hT P (.inr i.val) x,
              fullCutDiscardedInclusion_cap F T hT P i.val x⟩

noncomputable def fullCutSumMap :
    (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier →
      (partialCappedCarrier F T hT P Set.univ).carrier :=
  Sum.elim (fullCutPostInclusion F T hT P) (fullCutDiscardedInclusion F T hT P)

theorem fullCutSumMap_injective : Function.Injective (fullCutSumMap F T hT P) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl
            ((fullCutPostInclusion_openEmbedding F T hT P).injective h)
      | inr y =>
          exact (Set.disjoint_left.mp (fullCutInclusions_disjoint F T hT P)
            (Set.mem_range_self x) ⟨y, h.symm⟩).elim
  | inr x =>
      cases y with
      | inl y =>
          exact (Set.disjoint_left.mp (fullCutInclusions_disjoint F T hT P)
            ⟨y, h.symm⟩ (Set.mem_range_self x)).elim
      | inr y =>
          exact congrArg Sum.inr
            ((fullCutDiscardedInclusion_openEmbedding F T hT P).injective h)

theorem fullCutSumMap_surjective : Function.Surjective (fullCutSumMap F T hT P) := by
  intro q
  have hq : q ∈ Set.range (fullCutPostInclusion F T hT P) ∪
      Set.range (fullCutDiscardedInclusion F T hT P) := by
    rw [fullCutInclusions_cover]
    exact Set.mem_univ q
  rcases hq with ⟨p, hp⟩ | ⟨d, hd⟩
  · exact ⟨.inl p, hp⟩
  · exact ⟨.inr d, hd⟩

theorem fullCutSumMap_openEmbedding : IsOpenEmbedding (fullCutSumMap F T hT P) :=
  (fullCutPostInclusion_openEmbedding F T hT P).sumElim
    (fullCutDiscardedInclusion_openEmbedding F T hT P) (fullCutSumMap_injective F T hT P)

noncomputable def fullCutSumHomeomorph :
    (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier ≃ₜ
      (partialCappedCarrier F T hT P Set.univ).carrier :=
  (fullCutSumMap_openEmbedding F T hT P).isEmbedding.toHomeomorphOfSurjective
    (fullCutSumMap_surjective F T hT P)

theorem fullCutSumHomeomorph_apply
    (x : (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier) :
    fullCutSumHomeomorph F T hT P x = fullCutSumMap F T hT P x := rfl

end PoincareConjecture.M38
