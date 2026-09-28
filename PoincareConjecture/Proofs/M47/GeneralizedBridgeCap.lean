import PoincareConjecture.Proofs.M47.GeneralizedBridgeIsometry
import PoincareConjecture.Proofs.M34.Standard.CapIsometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
  (hregular : t ∉ F.surgery_times)

include hregular

theorem regular_history_cap_control {epsilon C : ℝ}
    (x : (H.generalized.slice t).carrier) (N : CapCertificate (F.metric t))
    (hepsilon : N.epsilon = epsilon) (hconstant : N.cap_constant ≤ C)
    (hx : H.history.forward t ht x ∈ N.core) :
    Nonempty (GeneralizedCanonicalControl (F := H.generalized) t x epsilon C) := by
  let f := regular_history_slice_diffeomorph H t ht hregular
  obtain ⟨N', he, hC, hD, hcore, _⟩ := N.exists_isometric_image_cap f.symm
    (regular_history_inverse_homothety H ht hregular) (H.generalized.connection t)
  refine ⟨GeneralizedCanonicalControl.cap N' (he.trans hepsilon)
    (hC ▸ hconstant) hD ?_⟩
  rw [hcore]
  exact ⟨f x, hx, f.symm_apply_apply x⟩

end PoincareConjecture.M47
