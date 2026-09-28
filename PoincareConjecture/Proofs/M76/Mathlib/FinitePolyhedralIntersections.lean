import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_finite_triangulation_inter (K J : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hJ : J.faces.Finite) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∩ J.space := by
  classical
  let : Finite J.faces := hJ.to_subtype
  choose H hH using fun t : J.faces =>
    t.val.exists_affine_halfspaces_convexHull (J.indep t.property)
  choose R hR hspace using fun t : J.faces =>
    K.exists_finite_triangulation_inter_halfspaces hK (H t)
  obtain ⟨L, hL, hLspace, _⟩ := exists_finite_triangulation_iUnion R hR
  refine ⟨L, hL, hLspace.trans ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨t, hxt⟩ := mem_iUnion.mp hx
    rw [hspace t, ← hH t] at hxt
    exact ⟨hxt.1, J.convexHull_subset_space t.property hxt.2⟩
  · rintro ⟨hxK, hxJ⟩
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxJ
    apply mem_iUnion.mpr
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hspace, ← hH]
    exact ⟨hxK, hxt⟩

end Geometry.SimplicialComplex
