import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.SurfaceIntersectionComponents

theorem components_meet_set_of_no_disjoint_piece
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} {f : E → X} {g : F → X} {Q B : Set F}
    (D : SurfaceIntersectionComponents S T f g Q)
    (h : ¬ ∃ i, Disjoint (D.pieces i) B) :
    ∀ x : (T ∩ g ⁻¹' (f '' S) : Set F),
      ∃ y : (T ∩ g ⁻¹' (f '' S) : Set F),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : F) ∈ B := by
  classical
  have hright : ∀ x : D.right.space, ∃ y : D.right.space,
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : F) ∈ B := by
    intro x
    let i := D.intrinsic (ConnectedComponents.mk x)
    obtain ⟨y, hy, hyB⟩ := not_disjoint_iff.mp (show ¬ Disjoint (D.pieces i) B from fun hi ↦ h ⟨i, hi⟩)
    have hyS := D.cover.symm.subset (mem_iUnion.mpr ⟨i, hy⟩)
    exact ⟨⟨y, hyS⟩, D.intrinsic.injective ((D.intrinsic_value ⟨y, hyS⟩ i).mpr hy).symm, hyB⟩
  have hs : D.right.space = T ∩ g ⁻¹' (f '' S) := D.right_space
  rw [hs] at hright
  exact hright

theorem ball_models_of_components_meet_rim
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} {f : E → X} {g : F → X} {Q : Set F}
    (D : SurfaceIntersectionComponents S T f g Q)
    (hboundary : ∀ x : (T ∩ g ⁻¹' (f '' S) : Set F),
      ∃ y : (T ∩ g ⁻¹' (f '' S) : Set F),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : F) ∈ Q) :
    ∀ i, IsFinitePLBallPair ℝ (D.pieces i) (D.pieces i ∩ Q) := by
  have hright : ∀ x : D.right.space, ∃ y : D.right.space,
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : F) ∈ Q := by
    have hs : D.right.space = T ∩ g ⁻¹' (f '' S) := D.right_space
    rw [hs]
    exact hboundary
  intro i
  rcases D.models i with hi | ⟨_, _, _, _, _, hd⟩
  · exact hi
  · obtain ⟨x, hx⟩ := (D.topology i).2.1.nonempty
    have hxS := D.cover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)
    obtain ⟨y, hxy, hyQ⟩ := hright ⟨x, hxS⟩
    have hxi := (D.intrinsic_value ⟨x, hxS⟩ i).mpr hx
    have hyi : (y : F) ∈ D.pieces i := (D.intrinsic_value y i).mp
      ((congrArg D.intrinsic hxy).symm.trans hxi)
    exact (disjoint_left.mp hd hyi hyQ).elim

end PoincareConjecture.M76.SurfaceIntersectionComponents
