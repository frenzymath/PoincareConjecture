import PoincareConjecture.Definitions.M18AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Compat.M18AsymptoticSoliton
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace PoincareConjecture

theorem isCompact_ancientM18TimeWindow (j : ℕ) : IsCompact (ancientM18TimeWindow j) :=
  isCompact_Icc

end PoincareConjecture
