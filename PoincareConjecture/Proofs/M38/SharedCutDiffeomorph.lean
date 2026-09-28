import PoincareConjecture.Proofs.M38.SharedCutSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S R : Set (Fin (F.event T hT).cap_count)) (hSR : S ⊆ R)

noncomputable def sharedCutTargetOpen :
    TopologicalSpace.Opens (partialCappedCarrier F T hT P S).carrier :=
  ⟨(newCutSphereImage F T hT P S R)ᶜ, by
    rw [← sharedCutComparison_range_eq_compl_spheres F T hT P S R hSR]
    exact (sharedCutComparison_openEmbedding F T hT P S R hSR).isOpen_range⟩

noncomputable def sharedCutRangeMap :
    sharedCutOpen F T hT P S R hSR → sharedCutTargetOpen F T hT P S R hSR :=
  fun p => ⟨sharedCutComparison F T hT P S R hSR p, by
    change sharedCutComparison F T hT P S R hSR p ∈ (newCutSphereImage F T hT P S R)ᶜ
    rw [← sharedCutComparison_range_eq_compl_spheres F T hT P S R hSR]
    exact Set.mem_range_self p⟩

theorem sharedCutRangeMap_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sharedCutRangeMap F T hT P S R hSR) := by
  intro p
  exact openCodomain_localDiffeomorphAt (partialCappedCarrier F T hT P S)
    (sharedCutTargetOpen F T hT P S R hSR) (sharedCutRangeMap F T hT P S R hSR) p
      (sharedCutComparison_localDiffeomorph F T hT P S R hSR p)

theorem sharedCutRangeMap_bijective : Function.Bijective (sharedCutRangeMap F T hT P S R hSR) := by
  constructor
  · intro x y h
    exact (sharedCutComparison_openEmbedding F T hT P S R hSR).injective
      (congrArg Subtype.val h)
  · intro q
    have hq := q.property
    change q.val ∈ (newCutSphereImage F T hT P S R)ᶜ at hq
    rw [← sharedCutComparison_range_eq_compl_spheres F T hT P S R hSR] at hq
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩

noncomputable def sharedCutDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) (sharedCutOpen F T hT P S R hSR)
      (sharedCutTargetOpen F T hT P S R hSR) ∞ :=
  (sharedCutRangeMap_localDiffeomorph F T hT P S R hSR).diffeomorphOfBijective
    (sharedCutRangeMap_bijective F T hT P S R hSR)

theorem sharedCutDiffeomorph_apply (p : sharedCutOpen F T hT P S R hSR) :
    (sharedCutDiffeomorph F T hT P S R hSR p).val = sharedCutComparison F T hT P S R hSR p := rfl

theorem sharedCutDiffeomorph_old (y : eventCutOpen F T hT P R) :
    (sharedCutDiffeomorph F T hT P S R hSR
      ⟨partialOldInclusion F T hT P R y, partialOldInclusion_mem_shared F T hT P S R hSR y⟩).val =
        partialOldInclusion F T hT P S (successiveOldInclusion F T hT P S R hSR y) :=
  sharedCutComparison_old F T hT P S R hSR y

theorem partialCapBall_annulus_mem_shared (a : R × Bool) (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    (partialCapBall F T hT P R a).map x.val ∈ sharedCutOpen F T hT P S R hSR := by
  rw [partialCapBall_attachment F T hT P R a x hx]
  exact partialOldInclusion_mem_shared F T hT P S R hSR _

theorem sharedCutDiffeomorph_annulus (a : R × Bool) (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    (sharedCutDiffeomorph F T hT P S R hSR
      ⟨(partialCapBall F T hT P R a).map x.val,
        partialCapBall_annulus_mem_shared F T hT P S R hSR a x hx⟩).val =
      partialOldInclusion F T hT P S (successiveOldInclusion F T hT P S R hSR
        (cutAttachmentChart F T hT P R a x)) := by
  have heq : (⟨(partialCapBall F T hT P R a).map x.val,
      partialCapBall_annulus_mem_shared F T hT P S R hSR a x hx⟩ : sharedCutOpen F T hT P S R hSR) =
      ⟨partialOldInclusion F T hT P R (cutAttachmentChart F T hT P R a x),
        partialOldInclusion_mem_shared F T hT P S R hSR _⟩ :=
    Subtype.ext (partialCapBall_attachment F T hT P R a x hx)
  rw [heq]
  exact sharedCutDiffeomorph_old F T hT P S R hSR _

end PoincareConjecture.M38
