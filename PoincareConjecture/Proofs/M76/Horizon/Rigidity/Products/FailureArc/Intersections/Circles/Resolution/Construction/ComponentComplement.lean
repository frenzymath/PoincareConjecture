import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

open Classical in
theorem SurfaceIntersectionComponents.isClosed_complement_piece
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} {f : E → X} {g : F → X} {rim : Set F}
    (D : SurfaceIntersectionComponents S T f g rim)
    (i : D.right.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    IsClosed ((T ∩ g ⁻¹' (f '' S)) \ D.pieces i) := by
  classical
  let := D.components_finite
  have heq : (T ∩ g ⁻¹' (f '' S)) \ D.pieces i =
      ⋃ j : {j // j ≠ i}, D.pieces j := by
    ext x
    constructor
    · rintro ⟨hx,hxi⟩
      have hx' : x ∈ D.right.space := D.right_space.symm.subset hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp (D.cover.subset hx')
      exact mem_iUnion.mpr ⟨⟨j,fun h => hxi (h ▸ hj)⟩,hj⟩
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact ⟨D.right_space.subset (D.cover.symm.subset (mem_iUnion.mpr ⟨j,hj⟩)),
        fun hi => disjoint_left.mp (D.disjoint j.property) hj hi⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun j => (D.topology j).1.isClosed

open Classical in
theorem SurfaceIntersectionComponents.components_meet_rim_of_no_closed_piece
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} {f : E → X} {g : F → X} {rim : Set F}
    (D : SurfaceIntersectionComponents S T f g rim)
    (h : ¬ ∃ i, Disjoint (D.pieces i) rim) :
    ∀ x : (T ∩ g ⁻¹' (f '' S) : Set F),
      ∃ y : (T ∩ g ⁻¹' (f '' S) : Set F),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : F) ∈ rim := by
  classical
  have hh : ∀ x : D.right.space, ∃ y : D.right.space,
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : F) ∈ rim := by
    intro x
    let i := D.intrinsic (ConnectedComponents.mk x)
    have hnot : ¬ Disjoint (D.pieces i) rim := fun hi => h ⟨i,hi⟩
    obtain ⟨y,hy,hyr⟩ := not_disjoint_iff.mp hnot
    have hyS := D.cover.symm.subset (mem_iUnion.mpr ⟨i,hy⟩)
    exact ⟨⟨y,hyS⟩,D.intrinsic.injective ((D.intrinsic_value ⟨y,hyS⟩ i).mpr hy).symm,hyr⟩
  have hs : D.right.space = T ∩ g ⁻¹' (f '' S) := D.right_space
  rw [hs] at hh
  exact hh

end PoincareConjecture.M76
