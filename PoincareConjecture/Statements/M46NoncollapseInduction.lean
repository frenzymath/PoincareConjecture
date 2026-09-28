import PoincareConjecture.Definitions.M46NoncollapseInduction
import PoincareConjecture.Statements.M15Noncollapsing
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.M11GeneralizedFlow
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Statements.M14GeneralizedLGeometry
import PoincareConjecture.Definitions.M33RegularHistory

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M46Predecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m11 : GeneralizedSpacetimeGeometryTheory.{u} 3
  m12 : GeneralizedRicciGaugeTheory.{u} 3
  m13 : GeneralizedParabolicRescalingTheory.{u} 3
  m14 : GeneralizedLGeometryTheory.{u} 3
  m15 : GeneralizedNoncollapsingConclusion.{u} 3
  regular_history : ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F),
    Nonempty (M33RegularHistoryData W)

structure RepairedNoncollapseInductionTheory : Prop where
  induction : ∀ S : RepairedControlledSchedulesData.{u},
      Nonempty (RepairedNoncollapseInductionData.{u} S)

end PoincareConjecture
