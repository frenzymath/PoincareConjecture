import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

universe u v w

open Set

namespace PoincareConjecture.M76

variable {X : Type u} [TopologicalSpace X]
  {ι : Type v} {κ : Type w}

def HasRelativeBoundaryProperPLApproximation [T2Space X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (d : κ → OpenPartialHomeomorph X (Fin 3 → ℝ)) (R : Set X) : Prop :=
  IsCompact R → PLDomain e R → PLDomain d R →
    ∀ U : Set R, IsOpen U → (Subtype.val : R → X) ⁻¹' frontier R ⊆ U →
      ChartwisePLOn e d (ContinuousMap.id R) U →
        ∃ phi : C(R, R), ChartwisePLMap e d phi ∧
          phi ⁻¹' ((Subtype.val : R → X) ⁻¹' frontier R) =
            (Subtype.val : R → X) ⁻¹' frontier R ∧
          Nonempty ((ContinuousMap.id R).HomotopyRel phi
            ((Subtype.val : R → X) ⁻¹' frontier R))

end PoincareConjecture.M76
