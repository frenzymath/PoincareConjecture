import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.PLAtlasTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.LatticeHandleCoordinates

/-!
# Standard atlases under the constructed lattice coordinates

The affine inverse formulas of the original standard atlas compose with
the inverse of the actual real linear lift. Thus arbitrary-lattice
normalization retains the full standard-atlas condition, in addition to
the entire domain and boundary. See Hamilton 1976, pp. 65--67.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

/-- A real linear lift of an ambient coordinate change transports the
standard atlas by composing its full affine inverse formulas. -/
theorem StandardLatticeHandleAtlas.preimage_linear_coordinates
    {ι ι' κ κ' α : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {L : Submodule ℤ (κ → ℝ)} {L' : Submodule ℤ (κ' → ℝ)}
    {d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι' κ' L' d)
    (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
    (A : ((ι → ℝ) × (κ → ℝ)) ≃L[ℝ] ((ι' → ℝ) × (κ' → ℝ)))
    (hR : h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L)
    (hA : ∀ x, h (x.1, QuotientAddGroup.mk x.2) =
      ((A x).1, QuotientAddGroup.mk (A x).2)) :
    StandardLatticeHandleAtlas ι κ L (fun i => h.transOpenPartialHomeomorph (d i)) := by
  refine ⟨?_, ?_⟩
  · simpa only [hR] using hd.domain.preimage_homeomorph h
  · intro i
    obtain ⟨a, ha⟩ := hd.inverse_formula i
    refine ⟨a.trans A.symm.toContinuousAffineEquiv, ?_⟩
    intro z hz
    change h.symm ((d i).symm z) =
      ((A.symm (a z)).1, QuotientAddGroup.mk (A.symm (a z)).2)
    apply h.injective
    rw [h.apply_symm_apply, hA, A.apply_symm_apply]
    exact ha z hz

/-- Construct the complete ambient and handle normalization, including
the transported standard atlas, from actual lattices and finite index
bijections. The chart and lattice-coordinate witnesses are all constructed. -/
theorem exists_standard_marked_lattice_handle_coordinates
    {ι ι' κ κ' α : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (τ : ι ≃ ι') (σ : κ ≃ κ')
    (L : Submodule ℤ (κ → ℝ)) (L' : Submodule ℤ (κ' → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι' κ' L' d) :
    ∃ (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
      (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι' κ' L'),
      h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L ∧
      (∀ x, ((g x).1.val, (g x).2) = h (x.1.val, x.2)) ∧
      g ⁻¹' latticeHandleBoundary ι' κ' L' = latticeHandleBoundary ι κ L ∧
      StandardLatticeHandleAtlas ι κ L
        (fun i => h.transOpenPartialHomeomorph (d i)) := by
  obtain ⟨A, q, h, g, _, hq, hh, hR, hg, hB⟩ :=
    exists_marked_lattice_handle_coordinates τ σ L L'
  let E := (LinearEquiv.piCongrLeft' ℝ (fun _ : ι => ℝ) τ).toContinuousLinearEquiv
  let F := E.prodCongr A
  refine ⟨h, g, hR, hg, hB, hd.preimage_linear_coordinates h F hR ?_⟩
  intro x
  rw [hh, hq]
  rfl

end PoincareMT.M76
