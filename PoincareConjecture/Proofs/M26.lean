import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.M26Proof
import PoincareConjecture.Statements.M26CanonicalNeighborhoods

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m26CanonicalNeighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  horizon_m26CanonicalNeighborhoods P

theorem m26CanonicalNeighborhoodTheory
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  m26CanonicalNeighborhoods P

end PoincareConjecture
