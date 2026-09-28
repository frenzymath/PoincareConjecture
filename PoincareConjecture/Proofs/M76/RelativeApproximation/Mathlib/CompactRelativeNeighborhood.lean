import PoincareConjecture.Proofs.M76.Mathlib.RelativePolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_compact_relative_polyhedral_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {A U : Set K.space} (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ (L : SimplicialComplex ℝ E) (V : Set K.space),
      L.faces.Finite ∧ L.space ⊆ K.space ∧ IsOpen V ∧ A ⊆ V ∧
      Subtype.val '' V ⊆ L.space ∧
      (Subtype.val : K.space → E) ⁻¹' L.space ⊆ U := by
  classical
  choose J V hJ hJK hV hxV hVJ hJU using fun x : A =>
    K.exists_relative_polyhedral_neighborhood hK x.val hU (hAU x.property)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  obtain ⟨L, hL, hLs, _⟩ := exists_finite_triangulation_iUnion
    (fun i : t => J i.val) (fun i => hJ i.val)
  refine ⟨L, ⋃ i : t, V i.val, hL, ?_,
    isOpen_iUnion (fun i => hV i.val), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hLs.subset hy)
    exact hJK i.val hi
  · intro x hx
    obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hit⟩, hxi⟩
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact hLs.symm.subset (mem_iUnion.mpr
      ⟨i, hVJ i.val (mem_image_of_mem Subtype.val hxi)⟩)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hLs.subset hx)
    exact hJU i.val hi

end Geometry.SimplicialComplex
