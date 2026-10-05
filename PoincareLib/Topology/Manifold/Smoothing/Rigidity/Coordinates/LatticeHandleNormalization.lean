import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.StandardLatticeAtlasTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.LatticeHandleMapTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.Mathlib.HomeomorphConjugacy

/-!
# Normalize the original relative lattice-handle problem

The lattice basis, ambient coordinates, and handle coordinates are
constructed internally. Both original irreducibility hypotheses, the
actual PL map, exact boundary preimage and the whole-boundary identity
homotopy transport to the same normalized problem. No rigidity conclusion
or proper disk is used. See Hamilton 1976, Lemma 3, pp. 65--67, and
Rigidity derivation 001, first formal stage 3.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

/-- Construct all original rigidity premises in a chosen lattice model
of the same dimensions. The ambient and handle coordinates agree on
the whole domain, and the new map is the exact conjugate of the old map. -/
theorem exists_lattice_handle_normalization
    {ι ι' κ κ' α β : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (τ : ι ≃ ι') (σ : κ ≃ κ')
    (L : Submodule ℤ (κ → ℝ)) (L' : Submodule ℤ (κ' → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι' κ' L' d)
    (hI : IsPLIrreducible e (latticeHandleDomain ι' κ' L'))
    (hJ : IsPLIrreducible d (latticeHandleDomain ι' κ' L'))
    (phi : C(LatticeHandle ι' κ' L', LatticeHandle ι' κ' L'))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain ι' κ' L' phi))
    (hproper : phi ⁻¹' latticeHandleBoundary ι' κ' L' = latticeHandleBoundary ι' κ' L')
    (F : (ContinuousMap.id (LatticeHandle ι' κ' L')).HomotopyRel phi
      (latticeHandleBoundary ι' κ' L')) :
    ∃ (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
      (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι' κ' L')
      (psi : C(LatticeHandle ι κ L, LatticeHandle ι κ L)),
      h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L ∧
      (∀ x, ((g x).1.val, (g x).2) = h (x.1.val, x.2)) ∧
      g ⁻¹' latticeHandleBoundary ι' κ' L' = latticeHandleBoundary ι κ L ∧
      (∀ x, g (psi x) = phi (g x)) ∧
      StandardLatticeHandleAtlas ι κ L (fun i => h.transOpenPartialHomeomorph (d i)) ∧
      IsPLIrreducible (fun i => h.transOpenPartialHomeomorph (e i))
        (latticeHandleDomain ι κ L) ∧
      IsPLIrreducible (fun i => h.transOpenPartialHomeomorph (d i))
        (latticeHandleDomain ι κ L) ∧
      ChartwisePLMap (fun i => h.transOpenPartialHomeomorph (e i))
        (fun i => h.transOpenPartialHomeomorph (d i)) (latticeHandleMapInDomain ι κ L psi) ∧
      psi ⁻¹' latticeHandleBoundary ι κ L = latticeHandleBoundary ι κ L ∧
      Nonempty ((ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel psi
        (latticeHandleBoundary ι κ L)) := by
  obtain ⟨h, g, hR, hg, hB, hd'⟩ :=
    exists_standard_marked_lattice_handle_coordinates τ σ L L' d hd
  let psi : C(LatticeHandle ι κ L, LatticeHandle ι κ L) :=
    ⟨fun x => g.symm (phi (g x)),
      g.symm.continuous.comp (phi.continuous.comp g.continuous)⟩
  have hconj (x) : g (psi x) = phi (g x) := g.apply_symm_apply _
  refine ⟨h, g, psi, hR, hg, hB, hconj, hd', ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hR] using hI.preimage_homeomorph h
  · simpa only [hR] using hJ.preimage_homeomorph h
  · exact hphi.lattice_handle_conjugacy h g hR hg psi hconj
  · simpa only [hB] using g.preimage_fixedSet_of_conjugacy hproper hconj
  · have H := F.of_homeomorph_conjugacy
      (g₀ := ContinuousMap.id (LatticeHandle ι κ L)) g (fun _ => rfl) hconj
    exact ⟨by simpa only [hB] using H⟩

end PoincareMT.M76
