import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.StandardLatticeAtlasTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.LatticeHandleMapTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Isotopy.Mathlib.HomeomorphConjugacy












set_option autoImplicit false

open Set

namespace PoincareConjecture.M76




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

end PoincareConjecture.M76
