import PoincareConjecture.Proofs.M38.FullCutSides
import PoincareConjecture.Proofs.M38.EventBallSeparation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)


noncomputable def postBallPatchHomeomorph (i : Fin (F.event T hT).cap_count) :
    capDoubleBall ≃ₜ retainedPatch F T hT P (some i) :=
  (P i).ball.open_embedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (by
    change Set.range ((P i).ball.map ∘
      (Subtype.val : capDoubleBall → StandardCapSpace)) =
        (P i).ball.map '' Metric.ball (0 : StandardCapSpace) 2
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩))


@[simp] theorem postBallPatchHomeomorph_val (i : Fin (F.event T hT).cap_count)
    (x : capDoubleBall) :
    (postBallPatchHomeomorph F T hT P i x).val = (P i).ball.map x.val := rfl


noncomputable def fullCutPostPatch (j : Option (Fin (F.event T hT).cap_count)) :
    retainedPatch F T hT P j → PartialCappedSpace F T hT P Set.univ :=
  match j with
  | none => partialOldInclusion F T hT P Set.univ ∘ fullCutPostOld F T hT P
  | some i => partialCappingInclude F T hT P Set.univ
      (.inr (⟨i, Set.mem_univ i⟩, false)) ∘ (postBallPatchHomeomorph F T hT P i).symm


theorem fullCutPostPatch_old (y : eventCapComplementOpen F T hT) :
    fullCutPostPatch F T hT P none y =
      partialOldInclusion F T hT P Set.univ (fullCutPostOld F T hT P y) := rfl


theorem fullCutPostPatch_cap (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    fullCutPostPatch F T hT P (some i) (postBallPatchHomeomorph F T hT P i x) =
      partialCappingInclude F T hT P Set.univ (.inr (⟨i, Set.mem_univ i⟩, false)) x := by
  simp only [fullCutPostPatch, Function.comp_apply, Homeomorph.symm_apply_apply]


theorem fullCutPostPatch_openEmbedding (j : Option (Fin (F.event T hT).cap_count)) :
    IsOpenEmbedding (fullCutPostPatch F T hT P j) := by
  cases j with
  | none =>
      exact (partialOldInclusion_openEmbedding F T hT P Set.univ).comp
        (fullCutPostOld_openEmbedding F T hT P)
  | some i =>
      exact (partialCappingInclude_openEmbedding F T hT P Set.univ _).comp
        (postBallPatchHomeomorph F T hT P i).symm.isOpenEmbedding


theorem fullCutPost_old_cap_iff (y : eventCapComplementOpen F T hT)
    (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    partialOldInclusion F T hT P Set.univ (fullCutPostOld F T hT P y) =
      partialCappingInclude F T hT P Set.univ (.inr (⟨i, Set.mem_univ i⟩, false)) x ↔
        y.val = (P i).ball.map x.val := by
  rw [partialOldInclusion_eq_cap_iff]
  constructor
  · rintro ⟨hx, heq⟩
    rw [fullCut_negative_attachment F T hT P i x hx] at heq
    exact congrArg Subtype.val ((fullCutPostOld_openEmbedding F T hT P).injective heq)
  · intro heq
    have hx : 1 < ‖x.val‖ := ((P i).ball_mem_cap_complement_iff x.property).mp
      (heq ▸ y.property)
    refine ⟨hx, ?_⟩
    rw [fullCut_negative_attachment F T hT P i x hx]
    exact congrArg (fullCutPostOld F T hT P) (Subtype.ext heq)


theorem fullCutPostPatch_eq_iff (j k : Option (Fin (F.event T hT).cap_count))
    (x : retainedPatch F T hT P j) (y : retainedPatch F T hT P k) :
    fullCutPostPatch F T hT P j x = fullCutPostPatch F T hT P k y ↔ x.val = y.val := by
  cases j with
  | none =>
      cases k with
      | none =>
          exact (fullCutPostPatch_openEmbedding F T hT P none).injective.eq_iff.trans
            Subtype.ext_iff
      | some i =>
          obtain ⟨z, rfl⟩ := (postBallPatchHomeomorph F T hT P i).surjective y
          rw [fullCutPostPatch_old, fullCutPostPatch_cap, postBallPatchHomeomorph_val]
          exact fullCutPost_old_cap_iff F T hT P x i z
  | some i =>
      cases k with
      | none =>
          obtain ⟨z, rfl⟩ := (postBallPatchHomeomorph F T hT P i).surjective x
          rw [fullCutPostPatch_cap, fullCutPostPatch_old, postBallPatchHomeomorph_val,
            eq_comm, fullCutPost_old_cap_iff]
          exact eq_comm
      | some k =>
          by_cases hik : i = k
          · subst k
            exact (fullCutPostPatch_openEmbedding F T hT P (some i)).injective.eq_iff.trans
              Subtype.ext_iff
          · obtain ⟨a, rfl⟩ := (postBallPatchHomeomorph F T hT P i).surjective x
            obtain ⟨b, rfl⟩ := (postBallPatchHomeomorph F T hT P k).surjective y
            rw [fullCutPostPatch_cap, fullCutPostPatch_cap,
              postBallPatchHomeomorph_val, postBallPatchHomeomorph_val]
            constructor
            · intro h
              exfalso
              exact Set.disjoint_left.mp (partialCapPatch_disjoint F T hT P Set.univ
                (⟨i, Set.mem_univ i⟩, false) (⟨k, Set.mem_univ k⟩, false)
                (fun he => hik (congrArg (fun z => z.1.val) he)))
                  (Set.mem_range_self a) (h.symm ▸ Set.mem_range_self b)
            · intro h
              exfalso
              exact Set.disjoint_left.mp (retained_ball_patches_disjoint F T hT P i k hik)
                ⟨a.val, a.property, rfl⟩ ⟨b.val, b.property, h.symm⟩


theorem fullCutPostPatch_cover :
    (⋃ j, Set.range (Subtype.val : retainedPatch F T hT P j → (F.slice T).carrier)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, hj⟩ := retainedPatch_cover F T hT P x
  exact Set.mem_iUnion.mpr ⟨j, ⟨x, mem_of_mem_nhds hj⟩, rfl⟩


theorem exists_fullCutPostInclusion :
    ∃ f : (F.slice T).carrier → PartialCappedSpace F T hT P Set.univ,
      IsOpenEmbedding f ∧ ∀ j (x : retainedPatch F T hT P j),
        f x.val = fullCutPostPatch F T hT P j x := by
  let q := fun j => (Subtype.val : retainedPatch F T hT P j → (F.slice T).carrier)
  obtain ⟨G, hG, hGq⟩ := Poincare.Gluing.exists_isOpenEmbedding_iUnion_ranges
    (q := q) (fun j => (retainedPatch F T hT P j).isOpen.isOpenEmbedding_subtypeVal)
    (f := fullCutPostPatch F T hT P) (fullCutPostPatch_openEmbedding F T hT P)
    (fullCutPostPatch_eq_iff F T hT P)
  let H : (F.slice T).carrier ≃ₜ (⋃ j, Set.range (q j)) :=
    (Homeomorph.Set.univ _).symm.trans
      (Homeomorph.setCongr (fullCutPostPatch_cover F T hT P).symm)
  refine ⟨G ∘ H, hG.comp H.isOpenEmbedding, ?_⟩
  intro j x
  have hH : H (q j x) = ⟨q j x, Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩⟩ :=
    Subtype.ext rfl
  rw [Function.comp_apply, hH]
  exact hGq j x


noncomputable def fullCutPostInclusion :
    (F.slice T).carrier → PartialCappedSpace F T hT P Set.univ :=
  Classical.choose (exists_fullCutPostInclusion F T hT P)


theorem fullCutPostInclusion_openEmbedding : IsOpenEmbedding (fullCutPostInclusion F T hT P) :=
  (Classical.choose_spec (exists_fullCutPostInclusion F T hT P)).1


theorem fullCutPostInclusion_patch (j : Option (Fin (F.event T hT).cap_count))
    (x : retainedPatch F T hT P j) :
    fullCutPostInclusion F T hT P x.val = fullCutPostPatch F T hT P j x :=
  (Classical.choose_spec (exists_fullCutPostInclusion F T hT P)).2 j x


theorem fullCutPostInclusion_old (y : eventCapComplementOpen F T hT) :
    fullCutPostInclusion F T hT P y.val =
      partialOldInclusion F T hT P Set.univ (fullCutPostOld F T hT P y) :=
  fullCutPostInclusion_patch F T hT P none y


theorem fullCutPostInclusion_cap (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    fullCutPostInclusion F T hT P ((P i).ball.map x.val) =
      partialCappingInclude F T hT P Set.univ (.inr (⟨i, Set.mem_univ i⟩, false)) x :=
  (fullCutPostInclusion_patch F T hT P (some i)
    (postBallPatchHomeomorph F T hT P i x)).trans (fullCutPostPatch_cap F T hT P i x)

end PoincareConjecture.M38
