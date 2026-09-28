import PoincareConjecture.Proofs.M76.Mathlib.TaperedTriangleDomain
import PoincareConjecture.Proofs.M76.Mathlib.SegmentStripProduct










set_option autoImplicit false

open Set Geometry AffineMap

namespace TaperedStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




def segmentDomain (q w : E) (β : ℝ) : Set (E × ℝ) :=
  convexHull ℝ (insert (q, 0) ({(w, 0), (w, β)} : Set (E × ℝ)))



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
