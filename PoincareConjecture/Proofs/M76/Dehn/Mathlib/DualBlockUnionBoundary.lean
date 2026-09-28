import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceDualBlockIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

noncomputable def vertexDualUnion (S : Set K.vertices) : Set E :=
  ⋃ p ∈ S, (K.barycentricDualBlock {p.val}).space

noncomputable def vertexDualRim (S : Set K.vertices) : Set E :=
  K.vertexDualUnion S ∩ K.vertexDualUnion Sᶜ

theorem vertexDualUnion_union (S T : Set K.vertices) :
    K.vertexDualUnion (S ∪ T) = K.vertexDualUnion S ∪ K.vertexDualUnion T := by
  ext x
  simp only [vertexDualUnion, mem_iUnion, mem_union]
  aesop

theorem vertexDualUnion_singleton (p : K.vertices) :
    K.vertexDualUnion {p} = (K.barycentricDualBlock {p.val}).space := by
  ext x
  simp [vertexDualUnion]

theorem vertexDualUnion_univ : K.vertexDualUnion univ = K.space := by
  rw [← K.iUnion_vertex_dualBlocks_space]
  ext x
  constructor
  · intro hx
    obtain ⟨p, _, hp⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨p.val, p.property, hp⟩
  · intro hx
    obtain ⟨p, hpK, hp⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨⟨p, hpK⟩, mem_univ _, hp⟩

theorem vertexDualUnion_insert (S : Set K.vertices) (p : K.vertices) :
    K.vertexDualUnion (insert p S) =
      (K.barycentricDualBlock {p.val}).space ∪ K.vertexDualUnion S := by
  rw [← singleton_union, K.vertexDualUnion_union, K.vertexDualUnion_singleton]

variable [DecidableEq E]

theorem vertexDualRim_singleton (p : K.vertices) :
    K.vertexDualRim {p} = (K.barycentricSubdivision.link p.val).space := by
  rw [vertexDualRim, K.vertexDualUnion_singleton]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨q, hqp, hxq⟩ := mem_iUnion₂.mp hx.2
    have hpq : p.val ≠ q.val := by
      intro h
      exact hqp (mem_singleton_iff.mpr (Subtype.ext h.symm))
    have hxe := (K.vertex_dualBlocks_space_inter p.val q.val).subset ⟨hx.1, hxq⟩
    exact (K.dualEdge_space_subset_vertex_links p.property q.property hpq hxe).1
  · intro x hx
    rw [K.barycentric_vertex_link_space_eq_iUnion_dualEdges p.property] at hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
    have hqK : q ∈ K.vertices :=
      K.face_subset_vertices hq.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    have hpair := (K.vertex_dualBlocks_space_inter p.val q).symm.subset hxq
    refine ⟨hpair.1, mem_iUnion₂.mpr ⟨⟨q, hqK⟩, ?_, hpair.2⟩⟩
    intro h
    exact hq.1 (congrArg Subtype.val (mem_singleton_iff.mp h))

theorem vertexDualRim_insert_of_contact
    {S : Set K.vertices} {p : K.vertices} (hp : p ∉ S) {I Q : Set E}
    (hinter : K.vertexDualUnion S ∩ (K.barycentricDualBlock {p.val}).space = I)
    (hcontact : I ∩ K.vertexDualUnion (insert p S)ᶜ = Q) :
    K.vertexDualRim (insert p S) =
      (K.vertexDualRim S ∪ (K.barycentricSubdivision.link p.val).space) \ (I \ Q) := by
  have hrest : Sᶜ = insert p (insert p S)ᶜ := by
    ext v
    simp only [mem_compl_iff, mem_insert_iff]
    by_cases hv : v = p
    · subst v
      tauto
    · tauto
  have hother : ({p}ᶜ : Set K.vertices) = S ∪ (insert p S)ᶜ := by
    ext v
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_insert_iff]
    by_cases hv : v = p
    · subst v
      tauto
    · tauto
  rw [← K.vertexDualRim_singleton p]
  unfold vertexDualRim
  rw [hrest, hother]
  simp only [K.vertexDualUnion_insert, K.vertexDualUnion_singleton,
    K.vertexDualUnion_union]
  ext x
  have hi : x ∈ I ↔
      x ∈ K.vertexDualUnion S ∧ x ∈ (K.barycentricDualBlock {p.val}).space := by
    rw [← hinter]
    rfl
  have hq : x ∈ Q ↔ x ∈ I ∧ x ∈ K.vertexDualUnion (insert p S)ᶜ := by
    rw [← hcontact]
    rfl
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  tauto

end Geometry.SimplicialComplex
