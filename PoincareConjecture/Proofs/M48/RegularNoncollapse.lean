import PoincareConjecture.Proofs.M48.RegularSpacetime
import PoincareConjecture.Proofs.M15.RawNoncollapse

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem M48Predecessors.regular_noncollapsed (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} {L : RepairedPreterminalSlab F T}
    (R : M48RegularSpacetimeData L) (p : R.history.generalized.point) (r0 kappa : ℝ)
    (h : M15GeneralizedNoncollapseAt R.geometry.toLGeometry p r0 kappa) :
    GeneralizedKappaNoncollapsedAt R.history.generalized p kappa r0 :=
  Proofs.M15.raw_noncollapse R.geometry P.m13 h

end PoincareConjecture
