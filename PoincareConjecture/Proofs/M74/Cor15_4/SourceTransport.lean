import PoincareConjecture.Definitions.Ch15.SurgeryTopology

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

noncomputable def SurgeryBallEmbedding.transport
    {A A' : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    SurgeryBallEmbedding A' where
  map := d ∘ B.map
  inverse := B.inverse ∘ d.symm
  map_smooth := d.contMDiff.comp_contMDiffOn B.map_smooth
  inverse_smooth := by
    rw [Set.image_comp, d.image_eq_preimage_symm]
    exact B.inverse_smooth.comp d.symm.contMDiff.contMDiffOn (fun _ hx => hx)
  left_inverse := by
    intro x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using B.left_inverse hx
  right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
    exact congrArg d (B.right_inverse (Set.mem_image_of_mem B.map hx))
  open_embedding := d.toHomeomorph.isOpenEmbedding.comp B.open_embedding

@[simp] theorem SurgeryBallEmbedding.transport_closedBall
    {A A' : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    (B.transport d).closedBall = d.symm ⁻¹' B.closedBall := by
  change (d ∘ B.map) '' Metric.closedBall 0 1 = d.symm ⁻¹' B.closedBall
  rw [Set.image_comp, d.image_eq_preimage_symm]
  rfl

noncomputable def SurgeryRegionEquivalence.transportSource
    {A A' C : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set C.carrier}
    (E : SurgeryRegionEquivalence A C U V)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    SurgeryRegionEquivalence A' C (d.symm ⁻¹' U) V where
  map := E.map ∘ d.symm
  inverse := d ∘ E.inverse
  map_image := by
    rw [Set.image_comp, ← d.image_eq_preimage_symm, d.symm_image_image, E.map_image]
  inverse_image := by
    rw [Set.image_comp, E.inverse_image, d.image_eq_preimage_symm]
  left_inverse := by
    intro x hx
    change d (E.inverse (E.map (d.symm x))) = x
    rw [E.left_inverse hx, d.apply_symm_apply]
  right_inverse := by
    intro x hx
    simpa only [Function.comp_apply, Diffeomorph.symm_apply_apply] using E.right_inverse hx
  map_smooth := E.map_smooth.comp d.symm.contMDiff.contMDiffOn (fun _ hx => hx)
  inverse_smooth := d.contMDiff.comp_contMDiffOn E.inverse_smooth

noncomputable def SmoothConnectedSumData.transportFirst
    {A A' B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A'.carrier ∞) :
    SmoothConnectedSumData A' B C where
  first_ball := S.first_ball.transport d
  second_ball := S.second_ball
  first_region := S.first_region
  second_region := S.second_region
  first_open := S.first_open
  second_open := S.second_open
  first_identify := {
    S.first_identify.transportSource d with
    map_image := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.first_identify.transportSource d).map_image
    inverse_image := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.first_identify.transportSource d).inverse_image
    left_inverse := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.first_identify.transportSource d).left_inverse
    map_smooth := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.first_identify.transportSource d).map_smooth }
  second_identify := S.second_identify
  regions_disjoint := S.regions_disjoint
  sphere_gluing := S.sphere_gluing
  collar := S.collar
  collar_inverse := S.collar_inverse
  collar_smooth := S.collar_smooth
  collar_inverse_smooth := S.collar_inverse_smooth
  collar_left_inverse := S.collar_left_inverse
  collar_right_inverse := S.collar_right_inverse
  collar_open := S.collar_open
  negative_gluing := by
    intro z s hs
    change S.collar (z, s) =
      S.first_identify.map (d.symm (d (S.first_ball.map ((1 - s) • z.1))))
    rw [d.symm_apply_apply]
    exact S.negative_gluing z s hs
  positive_gluing := S.positive_gluing
  central_disjoint := S.central_disjoint
  cover := S.cover

noncomputable def SmoothConnectedSumData.transportSecond
    {A B B' C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)
    (d : Diffeomorph (𝓡 3) (𝓡 3) B.carrier B'.carrier ∞) :
    SmoothConnectedSumData A B' C where
  first_ball := S.first_ball
  second_ball := S.second_ball.transport d
  first_region := S.first_region
  second_region := S.second_region
  first_open := S.first_open
  second_open := S.second_open
  first_identify := S.first_identify
  second_identify := {
    S.second_identify.transportSource d with
    map_image := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.second_identify.transportSource d).map_image
    inverse_image := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.second_identify.transportSource d).inverse_image
    left_inverse := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.second_identify.transportSource d).left_inverse
    map_smooth := by
      rw [SurgeryBallEmbedding.transport_closedBall, ← Set.preimage_compl]
      exact (S.second_identify.transportSource d).map_smooth }
  regions_disjoint := S.regions_disjoint
  sphere_gluing := S.sphere_gluing
  collar := S.collar
  collar_inverse := S.collar_inverse
  collar_smooth := S.collar_smooth
  collar_inverse_smooth := S.collar_inverse_smooth
  collar_left_inverse := S.collar_left_inverse
  collar_right_inverse := S.collar_right_inverse
  collar_open := S.collar_open
  negative_gluing := S.negative_gluing
  positive_gluing := by
    intro z s hs
    change S.collar (z, s) = S.second_identify.map
      (d.symm (d (S.second_ball.map ((1 + s) • (S.sphere_gluing z).1))))
    rw [d.symm_apply_apply]
    exact S.positive_gluing z s hs
  central_disjoint := S.central_disjoint
  cover := S.cover

noncomputable def SmoothDisjointUnionData.transportPieces
    {n : ℕ} {pieces pieces' : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (S : SmoothDisjointUnionData pieces C)
    (d : ∀ i, Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier (pieces' i).carrier ∞) :
    SmoothDisjointUnionData pieces' C where
  region := S.region
  region_open := S.region_open
  region_closed := S.region_closed
  identify := fun i => {
    (S.identify i).transportSource (d i) with
    map_image := by
      simpa only [Set.preimage_univ] using ((S.identify i).transportSource (d i)).map_image
    inverse_image := by
      simpa only [Set.preimage_univ] using ((S.identify i).transportSource (d i)).inverse_image
    left_inverse := by
      simpa only [Set.preimage_univ] using ((S.identify i).transportSource (d i)).left_inverse
    map_smooth := by
      simpa only [Set.preimage_univ] using ((S.identify i).transportSource (d i)).map_smooth }
  pairwise_disjoint := S.pairwise_disjoint
  cover := S.cover

end PoincareConjecture
