import PoincareConjecture.Statements.M28BoundedDistance
import PoincareConjecture.Statements.M25NeckCapTopology
import PoincareConjecture.Statements.Ch04.CurvatureTheory











set_option autoImplicit false

universe u

namespace PoincareConjecture

structure M28BoundedDistancePredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m25 : Nonempty (RepairedNeckCapTopologyTheory.{u})

end PoincareConjecture
