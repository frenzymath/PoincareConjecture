import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions
import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineImage
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set

theorem ContinuousLinearEquiv.isBounded_image_iff {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F) (s : Set E) :
    Bornology.IsBounded (e '' s) ↔ Bornology.IsBounded s := by
  exact e.toContinuousAffineEquiv.isBounded_image_iff s

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

theorem mem_inside_linearImage_iff (P : Polygon E n) (e : E ≃L[ℝ] F) (x : E) :
    e x ∈ (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).inside ↔ x ∈ P.inside := by
  exact P.mem_inside_affineImage_iff e.toContinuousAffineEquiv x

theorem inside_linearImage (P : Polygon E n) (e : E ≃L[ℝ] F) :
    (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).inside = e '' P.inside := by
  exact P.inside_affineImage e.toContinuousAffineEquiv

theorem outside_linearImage (P : Polygon E n) (e : E ≃L[ℝ] F) :
    (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).outside = e '' P.outside := by
  exact P.outside_affineImage e.toContinuousAffineEquiv

theorem closure_inside_linearImage (P : Polygon E n) (e : E ≃L[ℝ] F) :
    closure (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).inside =
      e '' closure P.inside := by
  exact P.closure_inside_affineImage e.toContinuousAffineEquiv

end Polygon
