import PoincareConjecture.Proofs.M76.Mathlib.ResidualTaperedTriangle
import PoincareConjecture.Proofs.M76.Mathlib.ZeroApexTriangleCollar










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem zeroApexCoordinates_diagonal (A : E →ᵃ[ℝ] ℝ) (q w v : E)
    (hw : A w = 0) (β s : ℝ) :
    A.zeroApexCoordinates q w v (s, β * s) =
      lineMap q (A.edgeLevel w v β) s := by
  rw [zeroApexCoordinates_apply, lineMap_apply_module', edgeLevel, hw, sub_zero]
  module




theorem zeroApexCoordinates_residual_image (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hq : A q = 0) (hw : A w = 0) {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    A.zeroApexCoordinates q w v '' TaperedStrip.residualDomain β (A v) =
      convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) := by
  let F := A.zeroApexCoordinates q w v
  have h0 : F (0, 0) = q := by
    rw [zeroApexCoordinates_bottom, lineMap_apply_zero]
  have h1 : F (1, β) = A.edgeLevel w v β := A.zeroApexCoordinates_side q w v hw β
  have h2 : F (β / A v, β) = A.edgeLevel q v β := by
    simp only [F, zeroApexCoordinates_apply, heightRay, edgeLevel, hq, hw, sub_zero,
      div_eq_mul_inv, mul_smul]
    module
  change F.toAffineMap '' TaperedStrip.residualDomain β (A v) = _
  rw [TaperedStrip.residualDomain_eq_convexHull hβ hβv, F.toAffineMap.image_convexHull]
  simp only [Matrix.range_cons, Matrix.range_empty, union_empty, singleton_union,
    image_insert_eq, image_singleton]
  change convexHull ℝ {F (0, 0), F (1, β), F (β / A v, β)} = _
  rw [h0, h1, h2]




theorem zeroApex_slab_partition (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0)
    {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    (convexHull ℝ (insert q ({w, A.edgeLevel w v β} : Set E)) ∪
        convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) =
      convexHull ℝ (insert q ({w, v} : Set E)) ∩ {x | A x ≤ β}) ∧
    (convexHull ℝ (insert q ({w, A.edgeLevel w v β} : Set E)) ∩
        convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) =
      segment ℝ q (A.edgeLevel w v β)) := by
  have hv : 0 < A v := hβ.trans hβv
  let F := A.zeroApexCoordinates q w v
  have hinj : Function.Injective F := A.zeroApexCoordinates_injective hqw hq hw hv.ne'
  have hC := A.zeroApexCoordinates_image q w v hw hβ
  have hR := A.zeroApexCoordinates_residual_image hq hw hβ hβv
  have hfull : F '' TaperedStrip.domain (A v) =
      convexHull ℝ (insert q ({w, v} : Set E)) := by
    rw [A.zeroApexCoordinates_image q w v hw hv]
    have he : A.edgeLevel w v (A v) = v := by
      rw [edgeLevel_eq_lineMap, hw, sub_zero, div_self hv.ne', lineMap_apply_one]
    rw [he]
  constructor
  · rw [← hC, ← hR, ← image_union,
      ← TaperedStrip.slab_eq_domain_union_residual hβ.le hβv.le]
    have hlevel : {p : ℝ × ℝ | p.2 ≤ β} = F ⁻¹' {x | A x ≤ β} := by
      ext p
      change p.2 ≤ β ↔ A (F p) ≤ β
      rw [A.apply_zeroApexCoordinates hq hw hv.ne']
    rw [hlevel, image_inter_preimage, hfull]
  · rw [← hC, ← hR, ← image_inter hinj,
      TaperedStrip.domain_inter_residual hβ.le hβv.le]
    change F.toAffineMap '' segment ℝ ((0, 0) : ℝ × ℝ) (1, β) = _
    rw [image_segment]
    change segment ℝ (F (0, 0)) (F (1, β)) = _
    rw [A.zeroApexCoordinates_bottom q w v 0, lineMap_apply_zero,
      A.zeroApexCoordinates_side q w v hw β]

end AffineMap
