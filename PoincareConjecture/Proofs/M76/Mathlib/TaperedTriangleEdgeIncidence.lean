import PoincareConjecture.Proofs.M76.Mathlib.ZeroApexTriangleCollar
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevelUniqueness

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zeroApexCoordinates_mem_bottom_iff (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hq : A q = 0) (hw : A w = 0) (hv : A v ≠ 0)
    {β : ℝ} {p : ℝ × ℝ} (hp : p ∈ TaperedStrip.domain β) :
    A.zeroApexCoordinates q w v p ∈ segment ℝ q w ↔ p.2 = 0 := by
  constructor
  · intro hm
    have hzero : segment ℝ q w ⊆ {x | A x = 0} := by
      rw [← convexHull_pair]
      apply convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage A)
      intro x hx
      rcases hx with rfl | rfl
      · exact hq
      · exact hw
    exact (A.apply_zeroApexCoordinates hq hw hv p).symm.trans (hzero hm)
  · intro ht
    have hp0 : p = (p.1, 0) := Prod.ext rfl ht
    rw [hp0, zeroApexCoordinates_bottom]
    exact lineMap_mem_segment ℝ q w hp.1

theorem zeroApexCoordinates_mem_side_iff (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0) (hv : 0 < A v)
    {β : ℝ} (hβv : β ≤ A v) {p : ℝ × ℝ} (hp : p ∈ TaperedStrip.domain β) :
    A.zeroApexCoordinates q w v p ∈ segment ℝ w v ↔ p.1 = 1 := by
  have hvw : A v ≠ A w := by rw [hw]; exact hv.ne'
  constructor
  · intro hm
    have hspan : A.zeroApexCoordinates q w v p ∈ affineSpan ℝ ({w, v} : Set E) :=
      convexHull_subset_affineSpan _ (by rwa [convexHull_pair])
    have hpoint := A.eq_edgeLevel_of_mem_affineSpan hvw hspan
      (A.apply_zeroApexCoordinates hq hw hv.ne' p)
    have hparam := A.zeroApexCoordinates_injective hqw hq hw hv.ne'
      (hpoint.trans (A.zeroApexCoordinates_side q w v hw p.2).symm)
    exact congrArg Prod.fst hparam
  · intro hs
    have hu : p.2 ≤ A v := by
      have h := hp.2.2
      rw [hs, mul_one] at h
      exact h.trans hβv
    have hp1 : p = (1, p.2) := Prod.ext hs rfl
    rw [hp1, zeroApexCoordinates_side A q w v hw, edgeLevel_eq_lineMap, hw,
      sub_zero, sub_zero]
    exact lineMap_mem_segment ℝ w v
      ⟨div_nonneg hp.2.1 hv.le, (div_le_one hv).mpr hu⟩

theorem zeroApexCoordinates_mem_far_edge_iff (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0) (hv : 0 < A v)
    {β : ℝ} (hβv : β < A v) {p : ℝ × ℝ} (hp : p ∈ TaperedStrip.domain β) :
    A.zeroApexCoordinates q w v p ∈ segment ℝ q v ↔ p = (0, 0) := by
  let F := A.zeroApexCoordinates q w v
  have h0 : F (0, 0) = q := by
    rw [zeroApexCoordinates_bottom, lineMap_apply_zero]
  have h1 : F (1, A v) = v := by
    rw [zeroApexCoordinates_side A q w v hw, edgeLevel_eq_lineMap, hw,
      sub_zero, div_self hv.ne', lineMap_apply_one]
  have himage : F '' segment ℝ (0, 0) (1, A v) = segment ℝ q v := by
    change F.toAffineMap '' segment ℝ (0, 0) (1, A v) = _
    rw [image_segment ℝ F.toAffineMap]
    change segment ℝ (F (0, 0)) (F (1, A v)) = _
    rw [h0, h1]
  constructor
  · intro hm
    rw [← himage] at hm
    obtain ⟨z, hz, hzp⟩ := hm
    have hzp' : z = p := A.zeroApexCoordinates_injective hqw hq hw hv.ne' hzp
    subst z
    have hline : p.2 = A v * p.1 := by
      obtain ⟨a, b, _, _, _, rfl⟩ := hz
      change a * 0 + b * A v = A v * (a * 0 + b * 1)
      ring
    have hs : p.1 = 0 := by
      by_contra hs
      have hspos : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm hs)
      have hbig := mul_lt_mul_of_pos_right hβv hspos
      have hu := hp.2.2
      rw [hline] at hu
      exact (not_lt_of_ge hu) hbig
    exact Prod.ext hs (by rw [hline, hs, mul_zero])
  · rintro rfl
    rw [h0]
    exact left_mem_segment ℝ q v

end AffineMap
