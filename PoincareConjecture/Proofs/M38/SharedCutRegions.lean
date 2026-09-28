import PoincareConjecture.Proofs.M38.SharedCutComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S R : Set (Fin (F.event T hT).cap_count)) (hSR : S ⊆ R)

noncomputable def newCutBalls : Set (partialCappedCarrier F T hT P R).carrier :=
  ⋃ a : {a : R × Bool // a.1.val ∉ S}, (partialCapBall F T hT P R a.val).closedBall

theorem sharedCutInclude_disjoint_new (j : SharedCutIndex F T hT P S R)
    (b : {a : R × Bool // a.1.val ∉ S}) :
    Disjoint (Set.range (sharedCutInclude F T hT P S R hSR j))
      (partialCapBall F T hT P R b.val).closedBall := by
  cases j with
  | inl y =>
      apply (partialCapBall_disjoint_old F T hT P R b.val).symm.mono_left
      rintro q ⟨x, rfl⟩
      exact ⟨partialCappingMap F T hT P R (.inl y) x,
        partialOldInclusion_patch F T hT P R y x⟩
  | inr a =>
      have hab : successiveCapIndex F T hT S R hSR a ≠ b.val := by
        intro h
        exact b.property ((congrArg (fun z : R × Bool => z.1.val) h) ▸ a.1.property)
      exact (partialCapPatch_disjoint F T hT P R _ b.val hab).mono_right
        (partialCapBall_subset_patch F T hT P R b.val)

theorem sharedCutOpen_eq_compl_newBalls :
    (sharedCutOpen F T hT P S R hSR : Set (partialCappedCarrier F T hT P R).carrier) =
      (newCutBalls F T hT P S R)ᶜ := by
  classical
  apply Set.Subset.antisymm
  · intro q hq hnew
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hnew
    exact Set.disjoint_left.mp (sharedCutInclude_disjoint_new F T hT P S R hSR j b) hj hb
  · intro q
    induction q using Quotient.inductionOn with
    | h z =>
        rcases z with ⟨j, x⟩
        cases j with
        | inl y =>
            intro _
            exact Set.mem_iUnion.mpr ⟨Sum.inl y, Set.mem_range_self x⟩
        | inr a =>
            intro hnew
            by_cases ha : a.1.val ∈ S
            · let b : S × Bool := (⟨a.1.val, ha⟩, a.2)
              have hab : successiveCapIndex F T hT S R hSR b = a := Prod.ext (Subtype.ext rfl) rfl
              refine Set.mem_iUnion.mpr ⟨Sum.inr b, x, ?_⟩
              change partialCappingInclude F T hT P R
                (.inr (successiveCapIndex F T hT S R hSR b)) x = _
              rw [hab]
              rfl
            · have hx : 1 < ‖x.val‖ := by
                by_contra hn
                apply hnew
                refine Set.mem_iUnion.mpr ⟨⟨a, ha⟩, ?_⟩
                rw [partialCapBall_closedBall]
                exact ⟨x, le_of_not_gt hn, rfl⟩
              have hmem := partialOldInclusion_mem_shared F T hT P S R hSR
                (cutAttachmentChart F T hT P R a x)
              change partialCappingInclude F T hT P R (.inr a) x ∈
                sharedCutOpen F T hT P S R hSR
              rw [← partialOldInclusion_cap F T hT P R a x hx]
              exact hmem

noncomputable def newCutSphereImage : Set (partialCappedCarrier F T hT P S).carrier :=
  partialOldInclusion F T hT P S ''
    {y : eventCutOpen F T hT P S | y.val ∈ eventCutSpheres F T hT P (R \ S)}

theorem sharedCutPatch_disjoint_newSpheres (j : SharedCutIndex F T hT P S R) :
    Disjoint (Set.range (sharedCutPatch F T hT P S R hSR j))
      (newCutSphereImage F T hT P S R) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨x, rfl⟩ ⟨y, hy, heq⟩
  cases j with
  | inl z =>
      have h := (partialOldInclusion_openEmbedding F T hT P S).injective heq
      have hmem : y.val ∈ eventCutOpen F T hT P R := by
        rw [h]
        exact (partialCappingMap F T hT P R (.inl z) x).property
      exact (successive_old_mem_iff F T hT P S R hSR y).mp hmem hy
  | inr a =>
      obtain ⟨hx, hxy⟩ := (partialOldInclusion_eq_cap_iff F T hT P S y a x).mp heq
      rw [← successive_attachment F T hT P S R hSR a x hx] at hxy
      have hmem : y.val ∈ eventCutOpen F T hT P R := by
        rw [hxy]
        exact (cutAttachmentChart F T hT P R (successiveCapIndex F T hT S R hSR a) x).property
      exact (successive_old_mem_iff F T hT P S R hSR y).mp hmem hy

theorem sharedCutComparison_range_eq_compl_spheres :
    Set.range (sharedCutComparison F T hT P S R hSR) = (newCutSphereImage F T hT P S R)ᶜ := by
  apply Set.Subset.antisymm
  · intro q hq hnew
    rw [sharedCutComparison_range] at hq
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    exact Set.disjoint_left.mp (sharedCutPatch_disjoint_newSpheres F T hT P S R hSR j) hj hnew
  · intro q
    induction q using Quotient.inductionOn with
    | h z =>
        rcases z with ⟨j, x⟩
        cases j with
        | inl y =>
            intro hnew
            let p := partialCappingMap F T hT P S (.inl y) x
            have hp : p.val ∉ eventCutSpheres F T hT P (R \ S) := by
              intro hbad
              exact hnew ⟨p, hbad, partialOldInclusion_patch F T hT P S y x⟩
            let r : eventCutOpen F T hT P R :=
              ⟨p.val, (successive_old_mem_iff F T hT P S R hSR p).mpr hp⟩
            refine ⟨⟨partialOldInclusion F T hT P R r,
              partialOldInclusion_mem_shared F T hT P S R hSR r⟩, ?_⟩
            rw [sharedCutComparison_old]
            have heq : successiveOldInclusion F T hT P S R hSR r = p := Subtype.ext rfl
            rw [heq]
            exact partialOldInclusion_patch F T hT P S y x
        | inr a =>
            intro _
            exact ⟨⟨partialCappingInclude F T hT P R
              (.inr (successiveCapIndex F T hT S R hSR a)) x,
                Set.mem_iUnion.mpr ⟨Sum.inr a, Set.mem_range_self x⟩⟩,
                  sharedCutComparison_cap F T hT P S R hSR a x⟩

end PoincareConjecture.M38
