import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Proof
import PoincareConjecture.Statements.M27KappaAlternatives
import PoincareConjecture.Statements.M27Providers

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m27KappaAlternatives (P : M27KappaAlternativePredecessors.{u}) :
    RepairedKappaAlternativeTheory.{u} :=
  horizon_m27KappaAlternatives P

end PoincareConjecture
