import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralRefinement
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallPairs
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Interior, frontier and PL models of finite halfspace regions

Nonconstant affine forms identify interior by strict inequalities.
Compact finite halfspace regions have actual finite triangulations
and, when their interiors are nonempty, finite PL ball models.
See Hudson 1969, pp. 12--19 and M76 derivation 128.
-/

set_option autoImplicit false

open Set Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonconstant real affine functional identifies the interior
of its closed nonpositive halfspace with the negative halfspace.
See the halfspace model calculation in M76 derivation 128. -/
theorem AffineMap.interior_nonpos (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) :
    interior {x | A x ≤ 0} = {x | A x < 0} := by
  have hopen := A.isOpenMap A.continuous_of_finiteDimensional
    (A.linear_surjective_iff.mp (LinearMap.surjective hA))
  simpa only [interior_Iic, preimage, mem_Iic, mem_Iio] using
    (hopen.preimage_interior_eq_interior_preimage A.continuous_of_finiteDimensional
      (Iic (0 : ℝ))).symm

/-- The interior of finitely many nonconstant affine halfspace
constraints is given by all strict inequalities. See the standard
attachment models in M76 derivation 128. -/
theorem interior_finite_affine_halfspaces {ι : Type*} [Finite ι]
    (A : ι → E →ᵃ[ℝ] ℝ) (hA : ∀ i, (A i).linear ≠ 0) :
    interior {x | ∀ i, A i x ≤ 0} = {x | ∀ i, A i x < 0} := by
  simp only [ofPred_forall, interior_iInter_of_finite]
  exact iInter_congr fun i => (A i).interior_nonpos (hA i)

/-- A finite affine halfspace region has frontier precisely
where all constraints hold weakly and at least one is an equality.
Each defining form is nonconstant. See M76 derivation 128. -/
theorem frontier_finite_affine_halfspaces {ι : Type*} [Finite ι]
    (A : ι → E →ᵃ[ℝ] ℝ) (hA : ∀ i, (A i).linear ≠ 0) :
    frontier {x | ∀ i, A i x ≤ 0} =
      {x | (∀ i, A i x ≤ 0) ∧ ∃ i, A i x = 0} := by
  classical
  have hclosed : IsClosed {x | ∀ i, A i x ≤ 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (A i).continuous_of_finiteDimensional
      continuous_const
  rw [frontier, hclosed.closure_eq, interior_finite_affine_halfspaces A hA]
  ext x
  change ((∀ i, A i x ≤ 0) ∧ ¬ ∀ i, A i x < 0) ↔
    ((∀ i, A i x ≤ 0) ∧ ∃ i, A i x = 0)
  constructor
  · rintro ⟨hx, hstrict⟩
    obtain ⟨i, hi⟩ := not_forall.mp hstrict
    exact ⟨hx, i, le_antisymm (hx i) (not_lt.mp hi)⟩
  · rintro ⟨hx, i, hi⟩
    refine ⟨hx, fun hstrict => ?_⟩
    have h := hstrict i
    rw [hi] at h
    exact lt_irrefl _ h

namespace Set

/-- Every compact finite affine halfspace intersection has a
finite geometric triangulation of its exact carrier, including
empty and lower-dimensional regions. See Hudson pp. 12--14
and M76 derivation 128. -/
theorem IsCompact.exists_finite_triangulation_of_halfspaces {s : Set E}
    (hs : IsCompact s) (H : Finset (E →ᵃ[ℝ] ℝ))
    (hrep : s = {x | ∀ A ∈ H, A x ≤ 0}) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = s := by
  obtain ⟨K, hK, hSK, _⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    hs isOpen_univ (subset_univ _)
  obtain ⟨L, hL, hspace⟩ := K.exists_finite_triangulation_inter_halfspaces hK H
  rw [← hrep] at hspace
  exact ⟨L, hL, hspace.trans (inter_eq_right.mpr (fun _ hx => interior_subset (hSK hx)))⟩

/-- A compact finite halfspace region with nonempty interior
is a finite PL ball pair with its full ambient frontier.
See Hudson pp. 12--19 and M76 derivation 128. -/
theorem isFinitePLBallPair_of_affine_halfspaces {s : Set E}
    (hs : IsCompact s) (H : Finset (E →ᵃ[ℝ] ℝ))
    (hrep : s = {x | ∀ A ∈ H, A x ≤ 0}) (hne : (interior s).Nonempty) :
    IsFinitePLBallPair E s (frontier s) := by
  obtain ⟨K, hK, hspace⟩ := hs.exists_finite_triangulation_of_halfspaces H hrep
  have hcv : Convex ℝ s := by
    rw [hrep]
    simp only [ofPred_forall]
    exact convex_iInter fun A => convex_iInter fun _ => (convex_Iic (0 : ℝ)).affine_preimage A
  exact isFinitePLBallPair_of_compact_convex hs hcv hne K hK hspace

end Set
