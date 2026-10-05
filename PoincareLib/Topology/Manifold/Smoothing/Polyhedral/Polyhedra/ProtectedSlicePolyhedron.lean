import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.PolyhedralStrictHalfspaceClosure

/-!
# The protected polyhedron for an affine section deformation

The closed negative part and a residual section polyhedron have
an exact finite union triangulation. The disk avoids this carrier
except at its allowed fixed point under the one-sidedness premise.
See Alexander 1924, pp. 7--8 and M76 derivation 155.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The closure of the negative part and the residual section
curves form a finite protected carrier. The disk/closure incidence
is the explicit one-sided collar hypothesis. See derivation 155. -/
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
