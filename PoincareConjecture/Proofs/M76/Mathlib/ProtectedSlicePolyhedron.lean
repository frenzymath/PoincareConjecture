import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralStrictHalfspaceClosure










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_protected_slice_polyhedron (K R : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hR : R.faces.Finite) (A : E →ᵃ[ℝ] ℝ)
    {d : Set E} (q : E)
    (hside : d ∩ closure (K.space ∩ {x | A x < 0}) ⊆ {q})
    (hres : d ∩ R.space ⊆ {q})
    (hcover : (K.space ∩ {x | A x = 0}) \ d ⊆ R.space) :
    ∃ Q : SimplicialComplex ℝ E, Q.faces.Finite ∧
      Q.space = closure (K.space ∩ {x | A x < 0}) ∪ R.space ∧
      d ∩ Q.space ⊆ {q} ∧ K.space ∩ {x | A x < 0} ⊆ Q.space ∧
      (K.space ∩ {x | A x = 0}) \ d ⊆ Q.space := by
  obtain ⟨N, hN, hNspace⟩ := K.exists_finite_triangulation_closure_affine_neg hK A
  obtain ⟨Q, hQ, hQspace⟩ := N.exists_finite_triangulation_union R hN hR
  rw [hNspace] at hQspace
  refine ⟨Q, hQ, hQspace, ?_, ?_, ?_⟩
  · rintro x ⟨hxd, hxQ⟩
    rw [hQspace] at hxQ
    rcases hxQ with hxN | hxR
    · exact hside ⟨hxd, hxN⟩
    · exact hres ⟨hxd, hxR⟩
  · intro x hx
    rw [hQspace]
    exact Or.inl (subset_closure hx)
  · intro x hx
    rw [hQspace]
    exact Or.inr (hcover hx)

end Geometry.SimplicialComplex
