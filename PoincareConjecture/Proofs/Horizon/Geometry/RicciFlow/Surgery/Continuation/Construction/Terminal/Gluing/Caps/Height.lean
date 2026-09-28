import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Caps.Chart




set_option autoImplicit false

universe u

namespace PoincareConjecture.SurgeryCapChart

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {h k : ℝ}

def atHeight (C : SurgeryCapChart g₀ S g h) (hk : h = k) : SurgeryCapChart g₀ S g k where
  radius := C.radius
  radius_eq := C.radius_eq
  tip := C.tip
  map := C.map
  inverse := C.inverse
  domain := C.domain
  domain_eq := C.domain_eq
  carrier := C.carrier
  image := C.image
  carrier_compact := C.carrier_compact
  homeomorph := C.homeomorph
  homeomorph_eq := C.homeomorph_eq
  map_tip := C.map_tip
  left_inverse := C.left_inverse
  right_inverse := C.right_inverse
  map_smooth := C.map_smooth
  inverse_smooth := C.inverse_smooth
  inner_ball := by rw [← hk]; exact C.inner_ball
  outer_ball := by rw [← hk]; exact C.outer_ball

end PoincareConjecture.SurgeryCapChart
