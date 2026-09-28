import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Ordinary

set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

theorem OrdinaryMarkedPlanarAnnulus.exists_minimal_boundary_count
    {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
    {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C R : Set M}
    {F : Bool → Set M} {s : Stage e S f r C}
    (A : OrdinaryMarkedPlanarAnnulus s R F) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R F,
      ∀ D : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount ≤ D.boundaryCount := by
  classical
  have hex : ∃ n : ℕ, ∃ B : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount = n :=
    ⟨A.boundaryCount, A, rfl⟩
  obtain ⟨B, hB⟩ := Nat.find_spec hex
  refine ⟨B, fun D => ?_⟩
  rw [hB]
  exact Nat.find_min' hex ⟨D, rfl⟩

end Geometry.OriginalPLTower
