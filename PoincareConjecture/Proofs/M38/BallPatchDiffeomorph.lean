import PoincareConjecture.Proofs.M38.BallCoordinatePatch

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (e : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞)
  (houter : ∀ x : StandardCapSpace, 3 / 2 ≤ ‖x‖ → e x = x)

include houter

theorem euclideanOuterDiffeomorph_symm (x : StandardCapSpace) (hx : 3 / 2 ≤ ‖x‖) :
    e.symm x = x := by
  apply e.injective
  change e (e.symm x) = e x
  rw [e.apply_symm_apply, houter x hx]

theorem euclideanOuterDiffeomorph_mapsTo :
    Set.MapsTo e (Metric.ball 0 2) (Metric.ball 0 2) := by
  intro x hx
  have hxnorm : ‖x‖ < 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  change dist (e x) 0 < 2
  rw [dist_zero_right]
  by_contra! hbound
  have hfix : e (e x) = e x := houter (e x) (by linarith)
  have heq : e x = x := e.injective hfix
  rw [heq] at hbound
  exact (not_le_of_gt hxnorm) hbound

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

theorem surgeryBallPatch_left_inverse :
    Function.LeftInverse (surgeryBallPatch B e.symm) (surgeryBallPatch B e) := by
  intro x
  by_cases hx : x ∈ B.map '' Metric.ball 0 2
  · have hm := euclideanOuterDiffeomorph_mapsTo e houter (surgeryBall_inverse_mem B hx)
    rw [surgeryBallPatch_of_mem B e hx,
      surgeryBallPatch_of_mem B e.symm (Set.mem_image_of_mem B.map hm),
      B.left_inverse hm, e.symm_apply_apply, B.right_inverse hx]
  · rw [surgeryBallPatch_of_not_mem B e hx,
      surgeryBallPatch_of_not_mem B e.symm hx]

theorem surgeryBallPatch_right_inverse :
    Function.LeftInverse (surgeryBallPatch B e) (surgeryBallPatch B e.symm) := by
  exact surgeryBallPatch_left_inverse e.symm (euclideanOuterDiffeomorph_symm e houter) B

theorem surgeryBallPatch_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (surgeryBallPatch B e) := by
  apply contMDiffOn_univ.mp
  exact surgeryBallPatch_smooth B e (S := Metric.ball 0 2) Metric.isOpen_ball
    e.contDiff.contDiffOn (euclideanOuterDiffeomorph_mapsTo e houter) houter Set.univ
    (fun _ _ hx => surgeryBall_inverse_mem B hx)

noncomputable def surgeryBallPatchDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞ where
  toFun := surgeryBallPatch B e
  invFun := surgeryBallPatch B e.symm
  left_inv := surgeryBallPatch_left_inverse e houter B
  right_inv := surgeryBallPatch_right_inverse e houter B
  contMDiff_toFun := surgeryBallPatch_contMDiff e houter B
  contMDiff_invFun := surgeryBallPatch_contMDiff e.symm
    (euclideanOuterDiffeomorph_symm e houter) B

theorem surgeryBallPatchDiffeomorph_apply (x : A.carrier) :
    surgeryBallPatchDiffeomorph e houter B x = surgeryBallPatch B e x := rfl

theorem surgeryBallPatchDiffeomorph_symm_apply (x : A.carrier) :
    (surgeryBallPatchDiffeomorph e houter B).symm x = surgeryBallPatch B e.symm x := rfl

theorem surgeryBallPatchDiffeomorph_map {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 2) :
    surgeryBallPatchDiffeomorph e houter B (B.map x) = B.map (e x) := by
  rw [surgeryBallPatchDiffeomorph_apply,
    surgeryBallPatch_of_mem B e (Set.mem_image_of_mem B.map hx), B.left_inverse hx]

theorem surgeryBallPatchDiffeomorph_symm_map {x : StandardCapSpace}
    (hx : x ∈ Metric.ball 0 2) :
    (surgeryBallPatchDiffeomorph e houter B).symm (B.map x) = B.map (e.symm x) := by
  rw [surgeryBallPatchDiffeomorph_symm_apply,
    surgeryBallPatch_of_mem B e.symm (Set.mem_image_of_mem B.map hx), B.left_inverse hx]

theorem surgeryBallPatchDiffeomorph_eq_self_off_compact {x : A.carrier}
    (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    surgeryBallPatchDiffeomorph e houter B x = x :=
  surgeryBallPatch_eq_self_off_compact B e houter hx

theorem surgeryBallPatchDiffeomorph_symm_eq_self_off_compact {x : A.carrier}
    (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    (surgeryBallPatchDiffeomorph e houter B).symm x = x :=
  surgeryBallPatch_eq_self_off_compact B e.symm
    (euclideanOuterDiffeomorph_symm e houter) hx

end PoincareConjecture.M38
