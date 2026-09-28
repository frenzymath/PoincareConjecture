import PoincareConjecture.Definitions.M82PrimeFactors
import PoincareConjecture.Statements.M73SphereFactors
import PoincareConjecture.Statements.M82PrimeFactors

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m82PrimeFactorLedger : M82PrimeFactorLedgerStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ N I C F
  let L : M82PrimeFactorLedger I C F :=
    { source := C.summand_index
      source_bijective := C.summand_index_bijective
      source_eq := rfl
      pieces := C.pieces
      piece_eq := by
        intro j
        simpa using C.piece_eq j
      non_survivor := by
        intro j
        simpa using C.piece_kind j
      spaceform := by
        intro j
        simpa using F.factor_kind j
      sphere_map := by
        intro j
        simpa using F.factor_sphere j
      assembly := C.assembly }
  exact ⟨L⟩

end PoincareConjecture
