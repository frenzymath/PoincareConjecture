import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.LatticeBasisQuotient

/-!
# Boundary-preserving coordinates on arbitrary lattice handles

Reindex the disk coordinates isometrically and change the torus lattice
by an actual lattice basis. The resulting ambient and handle maps agree
on the complete domain and preserve the entire marked boundary.
See Hamilton 1976, pp. 65--67, and the arbitrary-lattice obligation in
Rigidity/REMAINING-PRODUCER.md.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

/-- Arbitrary finite indices and actual lattices admit compatible ambient
and handle coordinates, with an explicit quotient formula and exact
domain and whole-boundary preimages. -/
theorem exists_marked_lattice_handle_coordinates
    {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (τ : ι ≃ ι') (σ : κ ≃ κ')
    (L : Submodule ℤ (κ → ℝ)) (L' : Submodule ℤ (κ' → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L'] :
    ∃ (A : (κ → ℝ) ≃L[ℝ] (κ' → ℝ))
      (q : ((κ → ℝ) ⧸ L.toAddSubgroup) ≃ₜ ((κ' → ℝ) ⧸ L'.toAddSubgroup))
      (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
      (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι' κ' L'),
      L.map (A.toLinearEquiv.restrictScalars ℤ).toLinearMap = L' ∧
      (∀ x : κ → ℝ, q (QuotientAddGroup.mk x) = QuotientAddGroup.mk (A x)) ∧
      (∀ x, h x = (fun i => x.1 (τ.symm i), q x.2)) ∧
      h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L ∧
      (∀ x, ((g x).1.val, (g x).2) = h (x.1.val, x.2)) ∧
      g ⁻¹' latticeHandleBoundary ι' κ' L' = latticeHandleBoundary ι κ L := by
  obtain ⟨A, hA, q, hq⟩ := exists_lattice_basis_quotient_homeomorph σ L L'
  let E : (ι → ℝ) ≃ᵢ (ι' → ℝ) := IsometryEquiv.piCongrLeft' τ
  have hE0 : E 0 = 0 := rfl
  have hnorm (x : ι → ℝ) : ‖E x‖ = ‖x‖ := by
    simpa only [hE0, dist_zero_right] using E.isometry.dist_eq x 0
  let ED : closedBall (0 : ι → ℝ) 1 ≃ₜ closedBall (0 : ι' → ℝ) 1 :=
    E.toHomeomorph.subtype (fun x => by
      change x ∈ closedBall 0 1 ↔ E x ∈ closedBall 0 1
      simp only [mem_closedBall, dist_zero_right, hnorm])
  refine ⟨A, q, E.toHomeomorph.prodCongr q, ED.prodCongr q,
    hA, hq, fun _ => rfl, ?_, fun _ => rfl, ?_⟩
  · ext x
    change (E x.1 ∈ closedBall 0 1 ∧ q x.2 ∈ univ) ↔
      (x.1 ∈ closedBall 0 1 ∧ x.2 ∈ univ)
    simp only [mem_univ, and_true, mem_closedBall, dist_zero_right, hnorm]
  · ext x
    change (‖E x.1.val‖ = 1 ∧ q x.2 ∈ univ) ↔
      (‖x.1.val‖ = 1 ∧ x.2 ∈ univ)
    simp only [hnorm, mem_univ, and_true]

end PoincareMT.M76
