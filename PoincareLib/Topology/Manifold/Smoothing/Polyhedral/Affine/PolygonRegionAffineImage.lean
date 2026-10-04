import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PolygonAffineImage
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Affine coordinate changes preserve canonical polygon regions

Bounded complementary components are preserved by continuous affine
equivalences, so the polygon inside, outside and closed inside are
preserved. See Erickson, Simple Polygons, pp. 2--9 and M76 derivation 111.
-/

set_option autoImplicit false

open Set

/-- A continuous affine map between normed spaces is Lipschitz
with the norm of its linear part. See M76 derivation 111. -/
theorem ContinuousAffineMap.lipschitz {K E F : Type*}
    [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (f : E →ᴬ[K] F) :
    LipschitzWith ‖f.contLinear‖₊ f := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have h : f.contLinear (x - y) = f x - f y := f.contLinear_map_vsub x y
  rw [← h]
  exact f.contLinear.le_opNorm (x - y)

/-- An invertible continuous affine map preserves and reflects
boundedness. See M76 derivation 111. -/
theorem ContinuousAffineEquiv.isBounded_image_iff {K E F : Type*}
    [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (e : E ≃ᴬ[K] F) (s : Set E) :
    Bornology.IsBounded (e '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro h
    have hb := e.symm.toContinuousAffineMap.lipschitz.isBounded_image h
    simpa only [image_image, ContinuousAffineEquiv.coe_toContinuousAffineMap,
      e.symm_apply_apply, image_id'] using hb
  · exact e.toContinuousAffineMap.lipschitz.isBounded_image

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

private theorem complement_affineImage (P : Polygon E n) (e : E ≃ᴬ[ℝ] F) :
    ((P.affineImage e.toAffineEquiv.toAffineMap).boundary ℝ)ᶜ =
      e '' (P.boundary ℝ)ᶜ := by
  rw [P.affineImage_boundary]
  exact (e.toHomeomorph.image_compl _).symm

/-- Affine coordinates preserve membership in the canonical
inside, without a simplicity hypothesis. See M76 derivation 111. -/
theorem mem_inside_affineImage_iff (P : Polygon E n) (e : E ≃ᴬ[ℝ] F) (x : E) :
    e x ∈ (P.affineImage e.toAffineEquiv.toAffineMap).inside ↔ x ∈ P.inside := by
  change (e x ∈ _ ∧ Bornology.IsBounded _) ↔ (x ∈ _ ∧ Bornology.IsBounded _)
  rw [complement_affineImage, e.injective.mem_set_image]
  by_cases hx : x ∈ (P.boundary ℝ)ᶜ
  · have hc : e '' connectedComponentIn (P.boundary ℝ)ᶜ x =
        connectedComponentIn (e '' (P.boundary ℝ)ᶜ) (e x) :=
      e.toHomeomorph.image_connectedComponentIn hx
    rw [← hc, e.isBounded_image_iff]
  · simp only [hx, false_and]

/-- The canonical inside commutes with continuous affine
equivalences. See M76 derivation 111. -/
theorem inside_affineImage (P : Polygon E n) (e : E ≃ᴬ[ℝ] F) :
    (P.affineImage e.toAffineEquiv.toAffineMap).inside = e '' P.inside := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [P.mem_inside_affineImage_iff, e.injective.mem_set_image]

/-- The canonical outside commutes with continuous affine
equivalences. See M76 derivation 111. -/
theorem outside_affineImage (P : Polygon E n) (e : E ≃ᴬ[ℝ] F) :
    (P.affineImage e.toAffineEquiv.toAffineMap).outside = e '' P.outside := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image]
  change (e x ∈ _ ∧ ¬ Bornology.IsBounded _) ↔ (x ∈ _ ∧ ¬ Bornology.IsBounded _)
  rw [complement_affineImage, e.injective.mem_set_image]
  by_cases hx : x ∈ (P.boundary ℝ)ᶜ
  · have hc : e '' connectedComponentIn (P.boundary ℝ)ᶜ x =
        connectedComponentIn (e '' (P.boundary ℝ)ᶜ) (e x) :=
      e.toHomeomorph.image_connectedComponentIn hx
    rw [← hc, e.isBounded_image_iff]
  · simp only [hx, false_and]

/-- Closed polygon regions commute with continuous affine
equivalences. See M76 derivation 111. -/
theorem closure_inside_affineImage (P : Polygon E n) (e : E ≃ᴬ[ℝ] F) :
    closure (P.affineImage e.toAffineEquiv.toAffineMap).inside = e '' closure P.inside := by
  rw [P.inside_affineImage]
  exact (e.toHomeomorph.image_closure _).symm

end Polygon
