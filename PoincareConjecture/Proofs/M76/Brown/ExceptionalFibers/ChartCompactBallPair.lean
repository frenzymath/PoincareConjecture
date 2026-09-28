import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.AmbientBallPairTransport









set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace X] [T2Space X]




theorem exists_compact_ballPair_enclosing (C : OpenPartialHomeomorph X E)
    (hCt : C.target = univ) {A : Set X} (hA : IsCompact A) (hAs : A ⊆ C.source) :
    ∃ Q : Set X, IsCompact Q ∧ A ⊆ interior Q ∧ Q ⊆ C.source ∧
      IsUnitBallPair E Q (frontier Q) := by
  have hCA : IsCompact (C '' A) := hA.image_of_continuousOn (C.continuousOn.mono hAs)
  obtain ⟨r, hr, hAr⟩ := hCA.isBounded.subset_ball_lt 0 (0 : E)
  have hballPair : IsUnitBallPair E (closedBall (0 : E) r) (frontier (closedBall 0 r)) :=
    isUnitBallPair_of_compact_convex (isCompact_closedBall 0 r) (convex_closedBall 0 r)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self hr)⟩
  have htarget (z : E) : z ∈ C.symm.source := by
    change z ∈ C.target
    rw [hCt]
    trivial
  obtain ⟨hQ, hQpair⟩ := C.symm.image_compact_ballPair (isCompact_closedBall 0 r)
    (fun z _ => htarget z) hballPair
  have hIopen : IsOpen (C.symm '' ball (0 : E) r) :=
    C.symm.isOpen_image_of_subset_source isOpen_ball (fun z _ => htarget z)
  have hIQ : C.symm '' ball (0 : E) r ⊆ interior (C.symm '' closedBall 0 r) :=
    interior_maximal (image_mono ball_subset_closedBall) hIopen
  refine ⟨C.symm '' closedBall 0 r, hQ, ?_, ?_, hQpair⟩
  · intro x hx
    exact hIQ ⟨C x, hAr ⟨x, hx, rfl⟩, C.left_inv (hAs hx)⟩
  · rintro x ⟨z, _, rfl⟩
    exact C.map_target (htarget z)

end OpenPartialHomeomorph
