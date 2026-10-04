import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility from an actual continuous retraction

Compose the actual nullhomotopy with the section and retraction.
Only the retraction identity is used; see Dehn derivation 015.
-/

set_option autoImplicit false

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An actual continuous retract of a contractible space is contractible.
No local path connectedness or second inverse identity is required. -/
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
