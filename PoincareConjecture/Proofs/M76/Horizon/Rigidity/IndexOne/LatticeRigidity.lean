import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Rigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.LatticeHandleRigidityTransport









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76


theorem exists_indexOne_lattice_rigidity
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (Λ : Submodule ℤ (κ → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ))
    (hι : Fintype.card ι = 1) (hκ : Fintype.card κ = 2)
    (hd : StandardLatticeHandleAtlas ι κ Λ d)
    (hI : IsPLIrreducible e (latticeHandleDomain ι κ Λ))
    (hJ : IsPLIrreducible d (latticeHandleDomain ι κ Λ))
    (phi : C(LatticeHandle ι κ Λ, LatticeHandle ι κ Λ))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain ι κ Λ phi))
    (hproper : phi ⁻¹' latticeHandleBoundary ι κ Λ = latticeHandleBoundary ι κ Λ)
    (F : (ContinuousMap.id (LatticeHandle ι κ Λ)).HomotopyRel phi
      (latticeHandleBoundary ι κ Λ)) :
    ∃ g : LatticeHandle ι κ Λ ≃ₜ LatticeHandle ι κ Λ,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain ι κ Λ g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ (latticeHandleBoundary ι κ Λ)) ∧
      Nonempty ((ContinuousMap.id (LatticeHandle ι κ Λ)).HomotopyRel
        ⟨g, g.continuous⟩ (latticeHandleBoundary ι κ Λ)) := by
  classical
  let τ : Fin 1 ≃ ι := (Fintype.equivFinOfCardEq hι).symm
  let σ : Fin 2 ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  obtain ⟨h, g, psi, hR, hg, hB, hconj, hd', hI', _, hpsi, _, ⟨F'⟩⟩ :=
    exists_lattice_handle_normalization τ σ (hamiltonLowerPeriodLattice (Fin 2))
      Λ e d hd hI hJ phi hphi hproper F
  obtain ⟨f, hf, ⟨Hf⟩, _⟩ := exists_fixed_indexOne_rigidity hI' hd' psi hpsi F'
  exact exists_lattice_handle_rigidity_transport h g hR hg hB phi psi hconj F f hf Hf

end PoincareConjecture.M76
