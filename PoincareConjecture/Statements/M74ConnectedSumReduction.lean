import PoincareConjecture.Definitions.M74ConnectedSumReduction

set_option autoImplicit false

universe u

namespace PoincareConjecture

def M74ConnectedSumReductionStatement : Prop :=
  ∀ {n : ℕ} (pieces : Fin n → GeneralizedSliceCarrier.{u})
    (C : GeneralizedSliceCarrier.{u})
    (_I : M74ReductionInput pieces C),
    Nonempty (M74ReductionConclusion C)

end PoincareConjecture
