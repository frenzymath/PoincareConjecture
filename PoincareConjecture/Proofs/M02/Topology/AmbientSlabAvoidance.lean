import PoincareConjecture.Proofs.M02.Topology.AmbientFiniteSlabAvoidance
import PoincareConjecture.Proofs.M02.Topology.AmbientGridPerturbation





set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.Proofs.M02.Topology

def ambientGridSlabRatio (N : Nat) : Real :=
  1 / (4 * (N + 1 : Real) ^ 2 * (ambientGridStarBound N + 1 : Real))

def ambientGridGap (N r : Nat) : Real :=
  (ambientGridMoveRatio N * ambientGridSlabRatio N / 2) *
    (ambientGridMoveRatio N * ambientGridSlabRatio N /
      (8 * (N + 1 : Real))) ^ r

end PoincareConjecture.Proofs.M02.Topology
