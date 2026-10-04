import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonRegionAffineImage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonAffineImage
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Linear coordinate changes preserve canonical polygon regions

A continuous linear equivalence preserves boundedness and carries
complementary components onto complementary components. Therefore
it preserves the canonical inside and outside of every polygon.
See Erickson, Simple Polygons, pp. 2--9 and M76 derivation 105.
-/

set_option autoImplicit false

open Set

/-- A continuous linear equivalence preserves and reflects
boundedness, by the Lipschitz bounds for it and its inverse.
See M76 derivation 105. -/
theorem ContinuousLinearEquiv.isBounded_image_iff {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F) (s : Set E) :
    Bornology.IsBounded (e '' s) ↔ Bornology.IsBounded s := by
  exact e.toContinuousAffineEquiv.isBounded_image_iff s

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- A linear coordinate change preserves membership in the
canonical polygon inside. See M76 derivation 105. -/
theorem mem_inside_linearImage_iff (P : Polygon E n) (e : E ≃L[ℝ] F) (x : E) :
    e x ∈ (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).inside ↔ x ∈ P.inside := by
  exact P.mem_inside_affineImage_iff e.toContinuousAffineEquiv x

/-- The canonical inside of a linear-image polygon is exactly
the image of the original inside, without any simplicity or
dimension assumption. See M76 derivation 105. -/
theorem inside_linearImage (P : Polygon E n) (e : E ≃L[ℝ] F) :
    (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).inside = e '' P.inside := by
  exact P.inside_affineImage e.toContinuousAffineEquiv

/-- The canonical outside of a linear-image polygon is exactly
the image of its outside. See M76 derivation 105. -/
theorem outside_linearImage (P : Polygon E n) (e : E ≃L[ℝ] F) :
    (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).outside = e '' P.outside := by
  exact P.outside_affineImage e.toContinuousAffineEquiv

/-- Closed polygon regions commute with continuous linear
coordinate equivalences. See M76 derivation 105. -/
theorem closure_inside_linearImage (P : Polygon E n) (e : E ≃L[ℝ] F) :
    closure (P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap).inside =
      e '' closure P.inside := by
  exact P.closure_inside_affineImage e.toContinuousAffineEquiv

end Polygon
