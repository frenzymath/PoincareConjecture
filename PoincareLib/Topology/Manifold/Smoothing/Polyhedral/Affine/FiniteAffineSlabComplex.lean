import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex

/-!
# Exact finite triangulations of closed affine slabs

Two weak affine halfspace cuts retain both boundary levels,
including empty slabs and constant heights. See Hudson 1969,
pp. 12--14 and M76 derivation 211.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The part of a finite polyhedron in any closed affine slab
has an exact finite triangulation. No regularity or ordering
of the two bounds is required. See M76 derivation 211. -/
theorem exists_finite_affineSlab_complex (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) (a b : ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = K.space ∩ {x | A x ∈ Icc a b} := by
  classical
  let B := AffineMap.const ℝ E a - A
  let C := A - AffineMap.const ℝ E b
  obtain ⟨L, hL, hspace⟩ := K.exists_finite_triangulation_inter_halfspaces hK {B, C}
  refine ⟨L, hL, hspace.trans ?_⟩
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, mem_ofPred_eq]
  change (a - A x ≤ 0 ∧ A x - b ≤ 0) ↔ A x ∈ Icc a b
  simp only [sub_nonpos, mem_Icc]

end Geometry.SimplicialComplex
