import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.SourceProperMeridian
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.SourceMeridianRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.LatticeHandleRigidityTransport

/-!
# Relative rigidity of the lattice solid torus

The proper source meridian is constructed internally, then cut, straightened
and reglued by the original marked-period consumer. Lattice normalization
returns the result to arbitrary rank-one lattices and both original atlases.
See Hamilton 1976, Lemma 3 and its application, pp. 65--67.
-/

set_option autoImplicit false
open Set

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L

theorem exists_fixed_indexTwo_rigidity
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hI : IsPLIrreducible e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ g : H ≃ₜ H,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel ⟨g, g.continuous⟩ B) := by
  obtain ⟨j, hj, hi, hjR, hproper, hrim⟩ :=
    exists_source_proper_meridian hI.1 hd phi hphi F
  exact exists_source_meridian_rigidity hI hd phi hphi F j hj hi hjR hproper hrim

/-- The original relative rigidity conclusion for every index-two lattice
handle, without a supplied meridian or normalized rigidity theorem. -/
theorem exists_indexTwo_lattice_rigidity
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (Λ : Submodule ℤ (κ → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) V3)
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) V3)
    (hι : Fintype.card ι = 2) (hκ : Fintype.card κ = 1)
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
  let τ : Fin 2 ≃ ι := (Fintype.equivFinOfCardEq hι).symm
  let σ : Fin 1 ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  obtain ⟨h, g, psi, hR, hg, hB, hconj, hd', hI', _, hpsi, _, ⟨F'⟩⟩ :=
    exists_lattice_handle_normalization τ σ L Λ e d hd hI hJ phi hphi hproper F
  obtain ⟨f, hf, ⟨Hf⟩, _⟩ := exists_fixed_indexTwo_rigidity hI' hd' psi hpsi F'
  exact exists_lattice_handle_rigidity_transport h g hR hg hB phi psi hconj F f hf Hf

end PoincareMT.M76
