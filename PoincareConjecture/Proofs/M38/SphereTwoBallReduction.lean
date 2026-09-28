import PoincareConjecture.Proofs.M38.BallRegionTransport
import PoincareConjecture.Proofs.M38.SpherePunctureCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

noncomputable def sphereBallComplementEquivalence
    (B : SurgeryBallEmbedding sphereCarrier.{u}) :
    SurgeryRegionEquivalence sphereCarrier.{u} euclideanCarrier.{u} B.closedBallᶜ Set.univ :=
  composeRegions (surgeryBallPunctureEquivalence B) (spherePunctureEquivalence (B.map 0))

theorem sphereBallComplementEquivalence_map (B : SurgeryBallEmbedding sphereCarrier.{u})
    (x : sphereCarrier.{u}.carrier) :
    (sphereBallComplementEquivalence B).map x =
      spherePunctureMap (B.map 0) (surgeryBallCollapse B x) := rfl

theorem sphereBallComplementEquivalence_inverse (B : SurgeryBallEmbedding sphereCarrier.{u})
    (y : euclideanCarrier.{u}.carrier) :
    (sphereBallComplementEquivalence B).inverse y =
      surgeryBallExpand B (spherePunctureInverse (B.map 0) y) := rfl

variable (B₀ B₁ : SurgeryBallEmbedding sphereCarrier.{u})
  (hdisjoint : Disjoint (B₀.map '' Metric.ball 0 2) (B₁.map '' Metric.ball 0 2))

noncomputable def sphereSecondEuclideanBall : SurgeryBallEmbedding euclideanCarrier.{u} :=
  transportSurgeryBallRegion B₁ (sphereBallComplementEquivalence B₀)
    (surgeryBall_closedImage_compact B₀ 1 (by norm_num)).isClosed.isOpen_compl
    isOpen_univ (disjoint_ball_image_subset_complement B₀ B₁ hdisjoint)

theorem sphereSecondEuclideanBall_map (x : StandardCapSpace) (hx : x ∈ Metric.ball 0 2) :
    (sphereSecondEuclideanBall B₀ B₁ hdisjoint).map x =
      spherePunctureMap (B₀.map 0) (B₁.map x) := by
  change spherePunctureMap (B₀.map 0) (surgeryBallPatch B₀ punctureCollapse (B₁.map x)) = _
  rw [surgeryBallPatch_of_not_mem B₀ punctureCollapse (fun hfirst =>
    Set.disjoint_left.mp hdisjoint hfirst ⟨x, hx, rfl⟩)]

theorem sphereTwoBall_map_image :
    (sphereBallComplementEquivalence B₀).map '' (B₀.closedBall ∪ B₁.closedBall)ᶜ =
      (sphereSecondEuclideanBall B₀ B₁ hdisjoint).closedBallᶜ := by
  have hsource : B₀.closedBallᶜ \ B₁.closedBall = (B₀.closedBall ∪ B₁.closedBall)ᶜ := by
    ext x
    exact not_or.symm
  have h := transportSurgeryBallRegion_complement_image B₁ (sphereBallComplementEquivalence B₀)
    (surgeryBall_closedImage_compact B₀ 1 (by norm_num)).isClosed.isOpen_compl
    isOpen_univ (disjoint_ball_image_subset_complement B₀ B₁ hdisjoint)
  rw [hsource, ← Set.compl_eq_univ_sdiff] at h
  exact h

noncomputable def sphereTwoBallEquivalence :
    SurgeryRegionEquivalence sphereCarrier.{u} euclideanCarrier.{u}
      (B₀.closedBall ∪ B₁.closedBall)ᶜ
      (sphereSecondEuclideanBall B₀ B₁ hdisjoint).closedBallᶜ := by
  let E := sphereBallComplementEquivalence B₀
  have hsub : (B₀.closedBall ∪ B₁.closedBall)ᶜ ⊆ B₀.closedBallᶜ :=
    fun _ hx h => hx (Or.inl h)
  refine {
    map := E.map
    inverse := E.inverse
    map_image := sphereTwoBall_map_image B₀ B₁ hdisjoint
    inverse_image := ?_
    left_inverse := E.left_inverse.mono hsub
    right_inverse := E.right_inverse.mono (Set.subset_univ _)
    map_smooth := E.map_smooth.mono hsub
    inverse_smooth := E.inverse_smooth.mono (Set.subset_univ _) }
  rw [← sphereTwoBall_map_image B₀ B₁ hdisjoint]
  exact E.left_inverse.image_image' hsub

theorem sphereTwoBallEquivalence_map (x : sphereCarrier.{u}.carrier) :
    (sphereTwoBallEquivalence B₀ B₁ hdisjoint).map x =
      spherePunctureMap (B₀.map 0) (surgeryBallCollapse B₀ x) := rfl

theorem sphereTwoBallEquivalence_inverse (y : euclideanCarrier.{u}.carrier) :
    (sphereTwoBallEquivalence B₀ B₁ hdisjoint).inverse y =
      surgeryBallExpand B₀ (spherePunctureInverse (B₀.map 0) y) := rfl

end PoincareConjecture.M38
