import PoincareConjecture.Proofs.M38.BallCoordinatePatch








set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38



noncomputable def transportSurgeryBall {A D : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) : SurgeryBallEmbedding D where
  map := e ∘ B.map
  inverse := B.inverse ∘ e.symm
  map_smooth := e.contMDiff.comp_contMDiffOn B.map_smooth
  inverse_smooth := B.inverse_smooth.comp e.symm.contMDiff.contMDiffOn (by
    rintro y ⟨x, hx, rfl⟩
    change e.symm (e (B.map x)) ∈ B.map '' Metric.ball 0 2
    rw [e.symm_apply_apply]
    exact Set.mem_image_of_mem B.map hx)
  left_inverse := by
    intro x hx
    change B.inverse (e.symm (e (B.map x))) = x
    rw [e.symm_apply_apply, B.left_inverse hx]
  right_inverse := by
    rintro y ⟨x, hx, rfl⟩
    change e (B.map (B.inverse (e.symm (e (B.map x))))) = e (B.map x)
    rw [e.symm_apply_apply, B.left_inverse hx]
  open_embedding := e.toHomeomorph.isOpenEmbedding.comp B.open_embedding


theorem transportSurgeryBall_map {A D : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) (x : StandardCapSpace) :
    (transportSurgeryBall B e).map x = e (B.map x) := rfl


theorem transportSurgeryBall_inverse {A D : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) (x : D.carrier) :
    (transportSurgeryBall B e).inverse x = B.inverse (e.symm x) := rfl


theorem transportSurgeryBall_image {A D : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) (s : Set StandardCapSpace) :
    (transportSurgeryBall B e).map '' s = e '' (B.map '' s) := by
  change (e ∘ B.map) '' s = e '' (B.map '' s)
  exact Set.image_comp _ _ _


theorem transportSurgeryBall_closedBall {A D : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞) :
    (transportSurgeryBall B e).closedBall = e '' B.closedBall :=
  transportSurgeryBall_image B e _


theorem surgeryBall_image_ball_open {A : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A) (r : ℝ) (hr : r ≤ 2) :
    IsOpen (B.map '' Metric.ball 0 r) := by
  have hsmall : Metric.ball (0 : StandardCapSpace) r ⊆ Metric.ball 0 2 :=
    Metric.ball_subset_ball hr
  have h := B.open_embedding.isOpenMap
    (Subtype.val ⁻¹' Metric.ball 0 r)
    (Metric.isOpen_ball.preimage continuous_subtype_val)
  have heq : (fun z : Metric.ball (0 : StandardCapSpace) 2 => B.map z.val) ''
      (Subtype.val ⁻¹' Metric.ball 0 r) = B.map '' Metric.ball 0 r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hsmall hz⟩, hz, rfl⟩
  rwa [heq] at h

end PoincareConjecture.M38
