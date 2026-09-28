import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCutCancellation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

section Band

variable {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem m64Intrinsic_band_height_mem_source {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) (B.height x)) :
    collarParameterEquiv.symm (x, z) ∈ B.coordinates.source := by
  apply B.band_subset_source
  rw [B.band_eq_subgraph]
  simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using ⟨hx, hz⟩

theorem m64Intrinsic_band_bottom_image :
    (fun t => B.coordinates (collarParameterEquiv.symm (t, 0))) '' Icc (0 : ℝ) 1 =
      B.lowerArc := by
  have hab : a ≤ b := by
    simpa only [B.cuts.A_zero, B.cuts.B_zero] using (B.cuts.separated 0
      ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩).le
  have hi : (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = Icc a b := by
    simpa using
      ((continuous_const : Continuous (fun _ : ℝ => a)).add
        (continuous_id.mul_const (b - a))).continuousOn.image_Icc_of_monotoneOn
        (zero_le_one : (0 : ℝ) ≤ 1) (fun x _ y _ hxy =>
          add_le_add_right (mul_le_mul_of_nonneg_right hxy (sub_nonneg.mpr hab)) a)
  rw [ObliqueBandFaces.lowerArc, ← hi, image_image]
  exact image_congr (fun t _ => B.coordinates_bottom t)

theorem m64Intrinsic_band_top_disjoint_lower : Disjoint B.polygonalTop B.lowerArc := by
  apply disjoint_left.mpr
  intro p hp hplower
  rw [← B.height_graph_image] at hp
  rw [← m64Intrinsic_band_bottom_image B] at hplower
  obtain ⟨x, hx, hxp⟩ := hp
  obtain ⟨y, hy, hyp⟩ := hplower
  have hxy := B.coordinates.injOn
    (m64Intrinsic_band_height_mem_source B hx ⟨(B.height_pos hx).le, le_rfl⟩)
    (m64Intrinsic_band_height_mem_source B hy ⟨le_rfl, (B.height_pos hy).le⟩)
    (hxp.trans hyp.symm)
  have hz := congrArg (fun q => (collarParameterEquiv q).2) hxy
  simp only [collarParameterEquiv.apply_symm_apply] at hz
  exact (B.height_pos hx).ne' hz

theorem m64Intrinsic_band_top_subset_region {U : Set AnnulusCoordinates}
    (hregion : B.carrier \ B.lowerArc ⊆ U) : B.polygonalTop ⊆ U := by
  intro p hp
  apply hregion
  refine ⟨B.isClosed_carrier.frontier_subset
    (B.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inr hp)))), ?_⟩
  exact fun hl => disjoint_left.mp (m64Intrinsic_band_top_disjoint_lower B) hp hl

end Band

section LinearBand

variable (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces
    (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
    lo a b ua wa ub wb ra rb)

theorem m64Intrinsic_band_left_cut :
    B.leftCut = segment ℝ (L (a, lo a)) (L (a, lo a) + ra • L (ua, wa)) := by
  change (fun q : ℝ × ℝ => L (collarParameterEquiv (collarParameterEquiv.symm q))) ''
    segment ℝ (a, lo a) (a + ra * ua, lo a + ra * wa) = _
  simp only [collarParameterEquiv.apply_symm_apply]
  change L.toLinearMap.toAffineMap '' segment ℝ (a, lo a)
    (a + ra * ua, lo a + ra * wa) = _
  rw [image_segment ℝ L.toLinearMap.toAffineMap]
  congr 1
  rw [← map_smul, ← map_add]
  rfl

theorem m64Intrinsic_band_right_cut :
    B.rightCut = segment ℝ (L (b, lo b)) (L (b, lo b) + rb • L (ub, wb)) := by
  change (fun q : ℝ × ℝ => L (collarParameterEquiv (collarParameterEquiv.symm q))) ''
    segment ℝ (b, lo b) (b + rb * ub, lo b + rb * wb) = _
  simp only [collarParameterEquiv.apply_symm_apply]
  change L.toLinearMap.toAffineMap '' segment ℝ (b, lo b)
    (b + rb * ub, lo b + rb * wb) = _
  rw [image_segment ℝ L.toLinearMap.toAffineMap]
  congr 1
  rw [← map_smul, ← map_add]
  rfl

end LinearBand

theorem m64Intrinsic_ray_image_eq_segment (p d : AnnulusCoordinates) {r : ℝ} (hr : 0 ≤ r) :
    (fun u : ℝ => p + u • d) '' Icc (0 : ℝ) r = segment ℝ p (p + r • d) := by
  have himage : (fun t : ℝ => t * r) '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) r := by
    simpa using (continuous_id.mul_const r).continuousOn.image_Icc_of_monotoneOn
      (zero_le_one : (0 : ℝ) ≤ 1)
      (fun x _ y _ hxy => mul_le_mul_of_nonneg_right hxy hr)
  rw [← himage, image_image, segment_eq_image]
  apply image_congr
  intro t _
  module

theorem m64Intrinsic_segment_base_eq_of_same_direction {p q d : AnnulusCoordinates}
    (heq : segment ℝ p (p + d) = segment ℝ q (q + d)) : p = q := by
  have hp : p ∈ segment ℝ q (q + d) := heq ▸ left_mem_segment ℝ p (p + d)
  have hq : q ∈ segment ℝ p (p + d) := heq.symm ▸ left_mem_segment ℝ q (q + d)
  rw [segment_eq_image] at hp hq
  obtain ⟨s, hs, hsp⟩ := hp
  obtain ⟨t, ht, htq⟩ := hq
  have hp' : q + s • d = p := by rw [← hsp]; module
  have hq' : p + t • d = q := by rw [← htq]; module
  have hsum : (t + s) • d = 0 := by
    apply add_left_cancel (a := p)
    calc
      p + (t + s) • d = (p + t • d) + s • d := by module
      _ = p := by rw [hq', hp']
      _ = p + 0 := (add_zero p).symm
  rcases smul_eq_zero.mp hsum with hscalar | hd
  · have ht0 : t = 0 := by linarith [hs.1, ht.1]
    simpa only [ht0, zero_smul, add_zero] using hq'
  · simpa only [hd, smul_zero, add_zero] using hq'

end PoincareConjecture
