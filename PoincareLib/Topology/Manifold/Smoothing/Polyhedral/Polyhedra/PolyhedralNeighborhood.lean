import PoincareLib.Topology.Manifold.Smoothing.Imports.Topology.FinitePolyhedralNeighborhood
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Finite polyhedral neighborhoods inside an open set

Local polyhedral preparation for Hamilton 1976, Theorem 2(1), p. 69.
We use the lower M02 Euclidean grid construction, which has no smoothness
premise. See M76 derivation 06, including the separate empty-set case.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

/-- A compact Euclidean subset has a finite polyhedral neighborhood contained
in any prescribed open neighborhood. See Hamilton p. 69 and M76 derivation 06. -/
theorem exists_finite_neighborhood_subset {N : ℕ}
    {S U : Set (EuclideanSpace ℝ (Fin N))} (hS : IsCompact S)
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)),
      K.faces.Finite ∧ S ⊆ interior K.space ∧ K.space ⊆ U := by
  by_cases hne : S.Nonempty
  · obtain ⟨ε, hε, hεU⟩ := hS.exists_thickening_subset_open hU hSU
    obtain ⟨K, hKf, hSK, hKε⟩ :=
      PoincareMT.Proofs.M02.Topology.exists_finite_polyhedral_neighborhood hS ε hε
    refine ⟨K, hKf, hSK, fun x hx => hεU ?_⟩
    exact (Metric.mem_thickening_iff_infDist_lt hne).mpr (hKε x hx)
  · have hS0 : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨⊥, Set.finite_empty, ?_, ?_⟩ <;> simp [hS0, space_bot]

end Geometry.SimplicialComplex
