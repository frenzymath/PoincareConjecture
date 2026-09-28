import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.Ch04.Harnack
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Statements.M29GeneralizedDistance

set_option autoImplicit false

universe u

namespace PoincareConjecture

structure M30ControlledBlowupPredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m06 : HarnackAncientTheory.{u}
  m07 : ∀ {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T),
    Nonempty (PointedRicciFlowCompactnessConclusion H)
  m29 : RepairedGeneralizedBoundedDistanceTheory.{u}

end PoincareConjecture
