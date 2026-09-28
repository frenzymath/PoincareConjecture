import PoincareConjecture.Statements.Ch04.Harnack
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Theorem











set_option autoImplicit false

universe u

namespace PoincareConjecture
















theorem differentialHarnackAncientTheory
    (hM04 : RicciFlowCurvatureTheory.{u}) : HarnackAncientTheory.{u} := by
  exact horizon_differentialHarnackAncientTheory hM04


theorem differentialHarnackAncientTheory_from_M04 : HarnackAncientTheory.{u} := by
  exact differentialHarnackAncientTheory ricciFlowCurvatureTheory

end PoincareConjecture
