import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs

/-!
# PL irreducibility in the actual marked domain

Every embedded PL sphere in the domain interior must bound an
embedded PL ball in the same chart family. Brown's topological
sphere-ball conclusion does not supply this assertion. See Hamilton
1976, pp. 66--67 and M76 derivation 320.
-/

set_option autoImplicit false

universe u v

open Set

namespace PoincareMT.M76

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- PL irreducibility with actual sphere and ball parametrisations in
the specified structure. The complete original sphere is the marked
ball boundary. This is a predicate, not an irreducibility theorem.
See Hamilton pp. 66--67 and M76 derivation 320. -/
def IsPLIrreducible (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (R : Set X) : Prop :=
  PLDomain e R ∧
    ∀ S : Set X, S ⊆ interior R → Nonempty (ChartwisePLSphere e S) →
      ∃ D : Set X, D ⊆ R ∧ Nonempty (ChartwisePLBall e D S)

end PoincareMT.M76
