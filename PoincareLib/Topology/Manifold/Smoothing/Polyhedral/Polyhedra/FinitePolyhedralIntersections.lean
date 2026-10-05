import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralUnions

/-!
# Exact finite triangulations of polyhedral intersections

Intersect the first complex with the affine inequalities of each
face of the second, then triangulate their finite union. This
supplies the shared disk boundaries in Alexander's attachment
argument, p. 7. See Hudson 1969, pp. 12--19 and derivation 126.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The intersection of two finite geometric carriers has an
actual finite triangulation, without compatibility of their
original faces. See Hudson pp. 12--14 and derivation 126. -/
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
