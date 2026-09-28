import PoincareConjecture.Proofs.M76.Mathlib.MaximalFaceAffineGerm

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_nonzero_height_vertex_of_triangle_interior_sign
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    {a : Finset E} (ha : a ∈ K.faces) (hac : a.card = 3)
    {p : E} (hpa : p ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
    (A : E →ᵃ[ℝ] ℝ) (hpos : p ∈ closure (K.space ∩ {x | 0 < A x})) :
    ∃ v ∈ a, A v ≠ 0 := by
  by_contra! hzero
  have hspan : affineSpan ℝ (a : Set E) ≤
      (affineSpan ℝ ({0} : Set ℝ)).comap A := by
    apply affineSpan_le.mpr
    intro v hv
    change A v ∈ affineSpan ℝ ({0} : Set ℝ)
    simpa only [AffineSubspace.mem_affineSpan_singleton] using hzero v hv
  obtain ⟨U, hU, hpU, hKU⟩ :=
    K.exists_open_eq_affineSpan_of_triangle_interior hK hbound ha hac hpa
  obtain ⟨x, hxU, hxK, hxpos⟩ := mem_closure_iff.mp hpos U hU hpU
  have hxspan := (hKU.subset ⟨hxK, hxU⟩).1
  have hxzero : A x = 0 := by
    simpa only [AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton]
      using hspan hxspan
  exact (ne_of_gt hxpos) hxzero

end Geometry.SimplicialComplex
