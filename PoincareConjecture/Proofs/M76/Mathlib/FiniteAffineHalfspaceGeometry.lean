import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import Mathlib.Analysis.Normed.Operator.Banach










set_option autoImplicit false

open Set Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem AffineMap.interior_nonpos (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) :
    interior {x | A x ≤ 0} = {x | A x < 0} := by
  have hopen := A.isOpenMap A.continuous_of_finiteDimensional
    (A.linear_surjective_iff.mp (LinearMap.surjective hA))
  simpa only [interior_Iic, preimage, mem_Iic, mem_Iio] using
    (hopen.preimage_interior_eq_interior_preimage A.continuous_of_finiteDimensional
      (Iic (0 : ℝ))).symm




theorem interior_finite_affine_halfspaces {ι : Type*} [Finite ι]
    (A : ι → E →ᵃ[ℝ] ℝ) (hA : ∀ i, (A i).linear ≠ 0) :
    interior {x | ∀ i, A i x ≤ 0} = {x | ∀ i, A i x < 0} := by
  simp only [ofPred_forall, interior_iInter_of_finite]
  exact iInter_congr fun i => (A i).interior_nonpos (hA i)




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





theorem IsCompact.exists_finite_triangulation_of_halfspaces {s : Set E}
    (hs : IsCompact s) (H : Finset (E →ᵃ[ℝ] ℝ))
    (hrep : s = {x | ∀ A ∈ H, A x ≤ 0}) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = s := by
  obtain ⟨K, hK, hSK, _⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    hs isOpen_univ (subset_univ _)
  obtain ⟨L, hL, hspace⟩ := K.exists_finite_triangulation_inter_halfspaces hK H
  rw [← hrep] at hspace
  exact ⟨L, hL, hspace.trans (inter_eq_right.mpr (fun _ hx => interior_subset (hSK hx)))⟩




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
