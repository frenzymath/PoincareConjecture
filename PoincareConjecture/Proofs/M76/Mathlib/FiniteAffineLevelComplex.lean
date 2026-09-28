import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finite_affineLevel_complex (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) (c : ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = K.space ∩ {x | A x = c} := by
  classical
  let B := A - AffineMap.const ℝ E c
  obtain ⟨L, hL, hspace⟩ := K.exists_finite_triangulation_inter_halfspaces hK {B, -B}
  have hlevel : {x : E | ∀ C ∈ ({B, -B} : Finset (E →ᵃ[ℝ] ℝ)), C x ≤ 0} =
      {x | A x = c} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq, mem_ofPred_eq]
    change (A x - c ≤ 0 ∧ -(A x - c) ≤ 0) ↔ A x = c
    constructor
    · rintro ⟨h₁, h₂⟩
      linarith
    · intro h
      constructor <;> linarith
  exact ⟨L, hL, hspace.trans (congrArg (K.space ∩ ·) hlevel)⟩

end Geometry.SimplicialComplex
