import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLatticeHandleModel
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLIrreducibility
import Mathlib.Topology.Homotopy.Basic

/-!
# Hamilton's specialised relative torus-rigidity input

The source and target are actual PL structures on one fixed marked
lattice handle. Irreducibility is tested by actual PL sphere and ball
maps. The result retains the map direction and the literal boundary
homotopy consumed by the proved bounded lift. This file defines the
missing geometric assertion; it does not prove it or imply handle
straightening. See Hamilton 1976, Lemma 3, pp. 65--67, and derivation 320.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))
  {α β : Type*}

/-- The lower-index specialisation of Hamilton Lemma 3, including the
preceding identity homotopy. The fixed standard model supplies the
compact orientable sufficiently-large target; establishing those
properties is part of a proof of this named input. Boundary-properness
is exact, and neither PL irreducibility is omitted. The last homotopy
is the literal input to `exists_boundedHandleLift` after unfolding the
two model definitions. See Hamilton pp. 65--67 and derivation 320. -/
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

end PoincareMT.M76
