import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false

universe u v

open Set

namespace PoincareConjecture.M76

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

def IsPLIrreducible (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (R : Set X) : Prop :=
  PLDomain e R ∧
    ∀ S : Set X, S ⊆ interior R → Nonempty (ChartwisePLSphere e S) →
      ∃ D : Set X, D ⊆ R ∧ Nonempty (ChartwisePLBall e D S)

end PoincareConjecture.M76
