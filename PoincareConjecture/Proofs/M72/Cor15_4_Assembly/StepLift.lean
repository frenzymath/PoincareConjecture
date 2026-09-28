import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.DisjointUnionSum

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Topology

universe u

namespace PoincareConjecture

namespace SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}}

noncomputable def sumInl (B : SurgeryBallEmbedding A) (Z : GeneralizedSliceCarrier.{u}) :
    SurgeryBallEmbedding (A.sum Z) where
  map := Sum.inl ∘ B.map
  inverse := Sum.elim B.inverse (fun _ => 0)
  map_smooth := ContMDiff.inl.comp_contMDiffOn B.map_smooth
  inverse_smooth := by
    rw [Set.image_comp]
    exact m72ContMDiffOn_sumElim_inl _ B.inverse_smooth
  left_inverse := by
    intro x hx
    exact B.left_inverse hx
  right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Sum.inl (B.right_inverse (Set.mem_image_of_mem _ hx))
  open_embedding := IsOpenEmbedding.inl.comp B.open_embedding

@[simp] theorem sumInl_closedBall (B : SurgeryBallEmbedding A)
    (Z : GeneralizedSliceCarrier.{u}) :
    (B.sumInl Z).closedBall = Sum.inl '' B.closedBall := by
  exact Set.image_comp Sum.inl B.map (Metric.closedBall 0 1)

theorem m72_closedBall_closed (B : SurgeryBallEmbedding A) : IsClosed B.closedBall :=
  ((isCompact_closedBall (0 : StandardCapSpace) 1).image_of_continuousOn
    (B.map_smooth.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num)))).isClosed

end SurgeryBallEmbedding

theorem m72SumInl_compl {A Z : GeneralizedSliceCarrier.{u}} (U : Set A.carrier) :
    (Sum.inl '' U : Set (A.sum Z).carrier)ᶜ =
      (Sum.inl '' Uᶜ) ∪ Set.range Sum.inr := by
  ext x
  cases x <;> simp

noncomputable def SmoothConnectedSumData.sumRight
    {A B C : GeneralizedSliceCarrier.{u}}
    (S : SmoothConnectedSumData A B C) (Z : GeneralizedSliceCarrier.{u}) :
    SmoothConnectedSumData A (B.sum Z) (C.sum Z) where
  first_ball := S.first_ball
  second_ball := S.second_ball.sumInl Z
  first_region := Sum.inl '' S.first_region
  second_region := (Sum.inl '' S.second_region) ∪ Set.range Sum.inr
  first_open := isOpenMap_inl _ S.first_open
  second_open := (isOpenMap_inl _ S.second_open).union isOpen_range_inr
  first_identify := S.first_identify.sumInl Z (S.first_ball.map 0)
  second_identify := {
    S.second_identify.sumRight Z S.second_ball.m72_closedBall_closed.isOpen_compl S.second_open with
    map_image := by
      rw [SurgeryBallEmbedding.sumInl_closedBall, m72SumInl_compl]
      exact (S.second_identify.sumRight Z
        S.second_ball.m72_closedBall_closed.isOpen_compl S.second_open).map_image
    inverse_image := by
      rw [SurgeryBallEmbedding.sumInl_closedBall, m72SumInl_compl]
      exact (S.second_identify.sumRight Z
        S.second_ball.m72_closedBall_closed.isOpen_compl S.second_open).inverse_image
    left_inverse := by
      rw [SurgeryBallEmbedding.sumInl_closedBall, m72SumInl_compl]
      exact (S.second_identify.sumRight Z
        S.second_ball.m72_closedBall_closed.isOpen_compl S.second_open).left_inverse
    map_smooth := by
      rw [SurgeryBallEmbedding.sumInl_closedBall, m72SumInl_compl]
      exact (S.second_identify.sumRight Z
        S.second_ball.m72_closedBall_closed.isOpen_compl S.second_open).map_smooth }
  regions_disjoint := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ (hy | hy)
    · rcases hy with ⟨y, hy, hxy⟩
      cases Sum.inl_injective hxy
      exact Set.disjoint_left.mp S.regions_disjoint hx hy
    · rcases hy with ⟨y, hy⟩
      cases hy
  sphere_gluing := S.sphere_gluing
  collar := Sum.inl ∘ S.collar
  collar_inverse := Sum.elim S.collar_inverse
    (fun _ => S.collar_inverse (S.first_identify.map (S.first_ball.map 0)))
  collar_smooth := ContMDiff.inl.comp_contMDiffOn S.collar_smooth
  collar_inverse_smooth := by
    rw [Set.image_comp]
    exact m72ContMDiffOn_sumElim_inl _ S.collar_inverse_smooth
  collar_left_inverse := by
    intro x hx
    exact S.collar_left_inverse hx
  collar_right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Sum.inl (S.collar_right_inverse (Set.mem_image_of_mem _ hx))
  collar_open := by
    rw [Set.image_comp]
    exact isOpenMap_inl _ S.collar_open
  negative_gluing := by
    intro z s hs
    exact congrArg Sum.inl (S.negative_gluing z s hs)
  positive_gluing := by
    intro z s hs
    exact congrArg Sum.inl (S.positive_gluing z s hs)
  central_disjoint := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ (hy | hy)
    · rcases hy with ⟨y, hy, hxy⟩
      cases Sum.inl_injective hxy
      exact Set.disjoint_left.mp S.central_disjoint (Set.mem_image_of_mem _ hx) (Or.inl hy)
    · rcases hy with hy | hy
      · rcases hy with ⟨y, hy, hxy⟩
        cases Sum.inl_injective hxy
        exact Set.disjoint_left.mp S.central_disjoint (Set.mem_image_of_mem _ hx) (Or.inr hy)
      · rcases hy with ⟨y, hy⟩
        cases hy
  cover := by
    apply Set.eq_univ_of_forall
    intro x
    cases x with
    | inl x =>
        have hx : x ∈ S.first_region ∪ S.second_region ∪
            S.collar '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
          rw [S.cover]
          trivial
        rcases hx with (hx | hx) | hx
        · exact Or.inl (Or.inl (Set.mem_image_of_mem _ hx))
        · exact Or.inl (Or.inr (Or.inl (Set.mem_image_of_mem _ hx)))
        · rcases hx with ⟨y, hy, rfl⟩
          exact Or.inr (Set.mem_image_of_mem _ hy)
    | inr x => exact Or.inl (Or.inr (Or.inr ⟨x, rfl⟩))

theorem SmoothConnectedSumStep.sumRight
    {X Y : GeneralizedSliceCarrier.{u}} (Z : GeneralizedSliceCarrier.{u})
    (h : SmoothConnectedSumStep X Y) :
    SmoothConnectedSumStep (X.sum Z) (Y.sum Z) := by
  rcases h with ⟨A, B, ⟨D⟩, ⟨S⟩⟩
  exact ⟨A, B.sum Z, ⟨D.sumRight Z (S.first_ball.map 0)⟩, ⟨S.sumRight Z⟩⟩

theorem SmoothConnectedSumStep.reflTransGen_sumRight
    {X Y : GeneralizedSliceCarrier.{u}} (Z : GeneralizedSliceCarrier.{u})
    (h : Relation.ReflTransGen SmoothConnectedSumStep X Y) :
    Relation.ReflTransGen SmoothConnectedSumStep (X.sum Z) (Y.sum Z) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.sumRight Z)

end PoincareConjecture
