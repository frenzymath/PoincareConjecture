import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClosedComplementSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes

set_option autoImplicit false
open Set Geometry

namespace Dehn

theorem exists_finite_interior_carrier_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hA : A.faces.Finite)
    (hAK : A.space ⊆ interior K.space) :
    ∃ N : SimplicialComplex ℝ E, N.faces.Finite ∧
      N.space = K.space \ interior A.space ∧
      N.space ∪ A.space = K.space ∧ N.space ∩ A.space = frontier A.space := by
  have hKclosed := (K.isCompact_space_of_finite hK).isClosed
  have hAclosed := (A.isCompact_space_of_finite hA).isClosed
  obtain ⟨R, J, hR, hRK, hJ⟩ := K.exists_subdivision_with_finite_polyhedra hK
    (fun _ : Unit ↦ A) (fun _ ↦ hA) (fun _ ↦ hAK.trans interior_subset)
  obtain ⟨N, _, hN, hNs, _⟩ := R.exists_closedComplement_subcomplex (J ()) hR (hJ ()).1
  rw [hRK.space_eq, (hJ ()).2] at hNs
  have hclosure : closure (K.space \ A.space) = K.space \ interior A.space := by
    apply Subset.antisymm
    · apply closure_minimal
      · exact sdiff_subset_sdiff_right interior_subset
      · exact hKclosed.sdiff isOpen_interior
    · intro x hx
      by_cases hxint : x ∈ interior K.space
      · have hxcompl : x ∈ closure (A.spaceᶜ) := by
          rw [closure_compl]
          exact hx.2
        have hh := isOpen_interior.closure_inter (s := A.spaceᶜ) ⟨hxcompl, hxint⟩
        have hsub : A.spaceᶜ ∩ interior K.space ⊆ K.space \ A.space :=
          fun _ hy ↦ ⟨interior_subset hy.2, hy.1⟩
        exact closure_mono hsub hh
      · exact subset_closure ⟨hx.1, fun hxA ↦ hxint (hAK hxA)⟩
  rw [hclosure] at hNs
  refine ⟨N, hN, hNs, ?_, ?_⟩
  · rw [hNs]
    ext x
    constructor
    · rintro (hx | hx)
      exacts [hx.1, interior_subset (hAK hx)]
    · intro hx
      by_cases hxA : x ∈ A.space
      · exact Or.inr hxA
      · exact Or.inl ⟨hx, fun hi ↦ hxA (interior_subset hi)⟩
  · rw [hNs, frontier, hAclosed.closure_eq]
    ext x
    constructor
    · rintro ⟨hx, hxA⟩
      exact ⟨hxA, hx.2⟩
    · rintro ⟨hxA, hxint⟩
      exact ⟨⟨interior_subset (hAK hxA), hxint⟩, hxA⟩

end Dehn
