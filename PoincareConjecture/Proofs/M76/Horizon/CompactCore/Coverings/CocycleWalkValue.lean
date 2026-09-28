import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCocycleOfClosed
import PoincareConjecture.Proofs.M76.Mathlib.ComplexCycleLabels



set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : AbstractSimplicialComplex ι}

def walkValue (c : A.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle) :
    {u v : ι} → A.edgeGraph.Walk u v → ZMod 2
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => c.value u v + walkValue c p

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
