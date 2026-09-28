import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Assembly

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem horizon_differentialHarnackAncientTheory
    (hM04 : RicciFlowCurvatureTheory.{u}) : HarnackAncientTheory.{u} := by
  exact differentialHarnackAncientTheory_of_bounded_ancient_zero_volume hM04

end PoincareConjecture
