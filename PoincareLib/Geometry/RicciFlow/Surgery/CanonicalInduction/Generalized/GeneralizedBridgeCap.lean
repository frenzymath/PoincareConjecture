import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeIsometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapIsometry

/-!
# Full canonical caps on a regular generalized slice

The verified exact-isometry cap theorem transports every frozen field,
including both necks and actual core balls, with unchanged constants.
The nonsurgery hypothesis ensures the whole physical slice is present.
Source: Morgan--Tian Definition 9.72 and Proposition 14.12.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
  (hregular : t ∉ F.surgery_times)

include hregular

/-- A physical cap at a regular time gives the same full generalized
canonical alternative, retaining epsilon and its original cap constant. -/
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

end PoincareMT.M47
