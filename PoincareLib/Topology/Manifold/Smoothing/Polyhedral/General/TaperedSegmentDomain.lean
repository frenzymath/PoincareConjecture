import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.TaperedTriangleDomain
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.SegmentStripProduct

/-!
# Geometric source domains of tapered segment collars

Actual bottom-segment points and their heights give a common
ambient source for gluing tapered and regular triangle pieces.
See Alexander 1924, pp. 6--8, Hudson 1969, pp. 15--19 and
M76 derivation 184.
-/

set_option autoImplicit false

open Set Geometry AffineMap

namespace TaperedStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tapered collar domain over the actual segment from
`q` to `w`, with top height `β` at `w` and zero width at `q`.
See Alexander p. 8 and M76 derivation 184. -/
def segmentDomain (q w : E) (β : ℝ) : Set (E × ℝ) :=
  convexHull ℝ (insert (q, 0) ({(w, 0), (w, β)} : Set (E × ℝ)))

/-- Scalar tapered coordinates have exactly the geometric
segment domain as their affine image. See derivation 184. -/
theorem segmentProductCoordinates_image (q w : E) {β : ℝ} (hβ : 0 < β) :
    PLStrip.segmentProductCoordinates q w 0 1 '' domain β = segmentDomain q w β := by
  let F := PLStrip.segmentProductCoordinates q w 0 1
  change F.toAffineMap '' domain β = _
  rw [domain_eq_convexHull hβ, F.toAffineMap.image_convexHull]
  simp only [Matrix.range_cons, Matrix.range_empty, union_empty, singleton_union,
    image_insert_eq, image_singleton]
  change convexHull ℝ {F (0, 0), F (1, 0), F (1, β)} = _
  simp only [F, PLStrip.segmentProductCoordinates_apply, lineMap_apply_zero,
    lineMap_apply_one, sub_zero, one_mul, zero_add]
  rfl

/-- The exact geometric tapered domain is finite PL
homeomorphic to its scalar parameter triangle, with the
actual bottom point and height formula retained.
See Alexander p. 8 and M76 derivation 184. -/
theorem exists_segmentDomain_homeomorph {q w : E} (hqw : q ≠ w)
    {β : ℝ} (hβ : 0 < β) :
    ∃ e : domain β ≃ₜ segmentDomain q w β, e.IsFinitePL ∧
      ∀ p : domain β, (e p : E × ℝ) = (lineMap q w (p : ℝ × ℝ).1, (p : ℝ × ℝ).2) := by
  obtain ⟨K, hK, hspace⟩ := exists_finite_triangulation hβ
  have hf : FinitePiecewiseAffineOn (PLStrip.segmentProductCoordinates q w 0 1) (domain β) :=
    ⟨K, hK, hspace, K.affineOnFaces_affine _⟩
  obtain ⟨G, hG, hGval⟩ := hf.exists_homeomorph_image
    (PLStrip.segmentProductCoordinates_injective hqw (by norm_num : (0 : ℝ) ≠ 1)).injOn
  let e := (Homeomorph.setCongr (rfl : domain β = domain β)).trans
    (G.trans (Homeomorph.setCongr (segmentProductCoordinates_image q w hβ)))
  refine ⟨e, hG.setCongr rfl (segmentProductCoordinates_image q w hβ), fun p => ?_⟩
  change (G p : E × ℝ) = _
  rw [hGval, PLStrip.segmentProductCoordinates_apply]
  simp

end TaperedStrip
