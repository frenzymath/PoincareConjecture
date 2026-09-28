import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))
  {α β : Type*}

def HasHamiltonRelativeTorusRigidity [DiscreteTopology L] [IsZLattice ℝ L]
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)) :
    Prop :=
  Fintype.card ι + Fintype.card κ = 3 → Fintype.card ι ≤ 2 →
    StandardLatticeHandleAtlas ι κ L d →
      IsPLIrreducible e (latticeHandleDomain ι κ L) →
        IsPLIrreducible d (latticeHandleDomain ι κ L) →
          ∀ phi : C(LatticeHandle ι κ L, LatticeHandle ι κ L),
            ChartwisePLMap e d (latticeHandleMapInDomain ι κ L phi) →
              phi ⁻¹' latticeHandleBoundary ι κ L = latticeHandleBoundary ι κ L →
                Nonempty ((ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel phi
                  (latticeHandleBoundary ι κ L)) →
                  ∃ g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L,
                    ChartwisePLHomeomorph e d
                      (latticeHandleHomeomorphInDomain ι κ L g) ∧
                    Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩
                      (latticeHandleBoundary ι κ L)) ∧
                    Nonempty ((ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel
                      ⟨g, g.continuous⟩ (latticeHandleBoundary ι κ L))

end PoincareConjecture.M76
