import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandBoundaryGeometry

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

theorem m64Intrinsic_band_endpoint_mem_lower_iff (right : Bool)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (B.endpointEdge right).map t ∈ B.lowerArc ↔ t = 0 := by
  let e : ℝ := if right then 1 else 0
  have he : e ∈ Icc (0 : ℝ) 1 := by cases right <;> simp [e]
  have hheight := B.height_pos he
  have hmap : (B.endpointEdge right).map t =
      B.coordinates (collarParameterEquiv.symm (e, t * B.height e)) :=
    B.endpointEdge_map right t
  rw [hmap, ← m64Intrinsic_band_bottom_image B]
  constructor
  · rintro ⟨x, hx, hxp⟩
    have hsrc := m64Intrinsic_band_height_mem_source B he
      ⟨mul_nonneg ht.1 hheight.le, by nlinarith [ht.2]⟩
    have hsrc0 := m64Intrinsic_band_height_mem_source B hx
      ⟨le_rfl, (B.height_pos hx).le⟩
    have hcoords := B.coordinates.injOn hsrc0 hsrc hxp
    have h := congrArg (fun q => (collarParameterEquiv q).2) hcoords
    simp only [collarParameterEquiv.apply_symm_apply] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hheight.ne'
  · rintro rfl
    exact ⟨e, he, by simp only [zero_mul]⟩

theorem m64Intrinsic_band_positive_endpoint_subset_region (right : Bool)
    {U : Set AnnulusCoordinates} (hregion : B.carrier \ B.lowerArc ⊆ U) :
    (B.endpointEdge right).map '' Ioc (0 : ℝ) 1 ⊆ U := by
  rintro z ⟨t, ht, rfl⟩
  apply hregion
  refine ⟨B.isClosed_carrier.frontier_subset
    (B.endpointEdge_subset_frontier right ⟨t, Ioc_subset_Icc_self ht, rfl⟩), ?_⟩
  intro h
  exact ht.1.ne' ((m64Intrinsic_band_endpoint_mem_lower_iff B right
    (Ioc_subset_Icc_self ht)).mp h)

theorem m64Intrinsic_band_cut_contact_subset_base (right : Bool)
    {U K : Set AnnulusCoordinates} (hregion : B.carrier \ B.lowerArc ⊆ U)
    (hdisj : Disjoint U K) :
    (if right then B.rightCut else B.leftCut) ∩ K ⊆ {(B.endpointEdge right).map 0} := by
  rw [← B.endpointEdge_image]
  rintro z ⟨⟨t, ht, rfl⟩, hzK⟩
  by_cases ht0 : t = 0
  · simp only [ht0, mem_singleton_iff]
  · exact False.elim (disjoint_left.mp hdisj
      (m64Intrinsic_band_positive_endpoint_subset_region B right hregion
        ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩, rfl⟩) hzK)

end Band

section LinearBand

variable (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces
    (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
    lo a b ua wa ub wb ra rb)

theorem m64Intrinsic_band_left_endpoint_zero :
    (B.endpointEdge false).map 0 = L (a, lo a) := by
  rw [B.endpointEdge_map]
  change B.coordinates (collarParameterEquiv.symm (0, 0 * B.height 0)) = _
  rw [zero_mul]
  have h := m64Intrinsic_band_left_parameter L B B.cuts.left.zero_mem_source
  simpa only [B.cuts.left.parameter_zero, zero_smul, add_zero] using h

theorem m64Intrinsic_band_right_endpoint_zero :
    (B.endpointEdge true).map 0 = L (b, lo b) := by
  rw [B.endpointEdge_map]
  change B.coordinates (collarParameterEquiv.symm (1, 0 * B.height 1)) = _
  rw [zero_mul]
  have h := m64Intrinsic_band_right_parameter L B B.cuts.right.zero_mem_source
  simpa only [B.cuts.right.parameter_zero, zero_smul, add_zero] using h

end LinearBand

end PoincareConjecture
