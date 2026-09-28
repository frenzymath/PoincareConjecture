import Mathlib.Topology.Homotopy.Contractible

set_option autoImplicit false

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem contractibleSpace_of_retract [ContractibleSpace X]
    (r : C(X, Y)) (s : C(Y, X)) (h : Function.LeftInverse r s) :
    ContractibleSpace Y := by
  apply (contractible_iff_id_nullhomotopic Y).mpr
  have hn := ((id_nullhomotopic X).comp_left s).comp_right r
  have heq : r.comp ((ContinuousMap.id X).comp s) = ContinuousMap.id Y := by
    ext y
    exact h y
  exact heq ▸ hn

end ContinuousMap
