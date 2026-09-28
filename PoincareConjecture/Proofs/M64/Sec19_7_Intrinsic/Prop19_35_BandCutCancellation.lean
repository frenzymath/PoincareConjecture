import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AttachedReturnBands
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

section OneBand

variable (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces
    (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
    lo a b ua wa ub wb ra rb)

theorem m64Intrinsic_band_left_parameter {u : ℝ} (hu : u ∈ B.cuts.left.parameter.source) :
    B.coordinates (collarParameterEquiv.symm (0, B.cuts.left.parameter u)) =
      L (a, lo a) + u • L (ua, wa) := by
  rw [B.coordinates_pair_apply]
  change L (collarParameterEquiv (collarParameterEquiv.symm
    (B.cuts.coordinates B.open_domain B.smooth_lower (0, B.cuts.left.parameter u)))) = _
  rw [collarParameterEquiv.apply_symm_apply, B.cuts.coordinates_apply]
  simp only [obliqueStripMap, zero_mul, add_zero]
  change L (B.cuts.left.horizontal (B.cuts.left.parameter u),
    lo (B.cuts.left.horizontal (B.cuts.left.parameter u)) + B.cuts.left.parameter u) = _
  rw [B.cuts.left.horizontal_parameter hu, B.cuts.left.map_eq, ← map_smul, ← map_add]
  congr 1
  ext <;> simp [transverseCutHeight, smul_eq_mul]

theorem m64Intrinsic_band_right_parameter {u : ℝ} (hu : u ∈ B.cuts.right.parameter.source) :
    B.coordinates (collarParameterEquiv.symm (1, B.cuts.right.parameter u)) =
      L (b, lo b) + u • L (ub, wb) := by
  rw [B.coordinates_pair_apply]
  change L (collarParameterEquiv (collarParameterEquiv.symm
    (B.cuts.coordinates B.open_domain B.smooth_lower (1, B.cuts.right.parameter u)))) = _
  rw [collarParameterEquiv.apply_symm_apply, B.cuts.coordinates_apply]
  have hx (z : ℝ) : B.cuts.A z + (B.cuts.B z - B.cuts.A z) = B.cuts.B z := by ring
  simp only [obliqueStripMap, one_mul, hx]
  change L (B.cuts.right.horizontal (B.cuts.right.parameter u),
    lo (B.cuts.right.horizontal (B.cuts.right.parameter u)) + B.cuts.right.parameter u) = _
  rw [B.cuts.right.horizontal_parameter hu, B.cuts.right.map_eq, ← map_smul, ← map_add]
  congr 1
  ext <;> simp [transverseCutHeight, smul_eq_mul]

theorem m64Intrinsic_band_open_left_ray :
    (fun u : ℝ => L (a, lo a) + u • L (ua, wa)) '' Ioo 0 ra ⊆
      (B.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
  rintro q ⟨u, hu, rfl⟩
  have hus := B.cuts.left.parameter_Icc_subset_source B.interface.left_parameter_mem
    (Ioo_subset_Icc_self hu)
  have hz0 : 0 < B.cuts.left.parameter u := by
    simpa only [B.cuts.left.parameter_zero] using
      B.cuts.left.strictMono B.cuts.left.zero_mem_source hus hu.1
  have hzr : B.cuts.left.parameter u < B.height 0 := by
    rw [B.height_zero]
    exact B.cuts.left.strictMono hus B.interface.left_parameter_mem hu.2
  have hh := B.height_pos (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  refine ⟨B.cuts.left.parameter u / B.height 0,
    ⟨div_pos hz0 hh, (div_lt_one hh).mpr hzr⟩, ?_⟩
  rw [B.endpointEdge_map]
  change B.coordinates (collarParameterEquiv.symm
    (0, B.cuts.left.parameter u / B.height 0 * B.height 0)) = _
  rw [div_mul_cancel₀ _ hh.ne']
  exact m64Intrinsic_band_left_parameter L B hus

theorem m64Intrinsic_band_open_right_ray :
    (fun u : ℝ => L (b, lo b) + u • L (ub, wb)) '' Ioo 0 rb ⊆
      (B.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
  rintro q ⟨u, hu, rfl⟩
  have hus := B.cuts.right.parameter_Icc_subset_source B.interface.right_parameter_mem
    (Ioo_subset_Icc_self hu)
  have hz0 : 0 < B.cuts.right.parameter u := by
    simpa only [B.cuts.right.parameter_zero] using
      B.cuts.right.strictMono B.cuts.right.zero_mem_source hus hu.1
  have hzr : B.cuts.right.parameter u < B.height 1 := by
    rw [B.height_one]
    exact B.cuts.right.strictMono hus B.interface.right_parameter_mem hu.2
  have hh := B.height_pos (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  refine ⟨B.cuts.right.parameter u / B.height 1,
    ⟨div_pos hz0 hh, (div_lt_one hh).mpr hzr⟩, ?_⟩
  rw [B.endpointEdge_map]
  change B.coordinates (collarParameterEquiv.symm
    (1, B.cuts.right.parameter u / B.height 1 * B.height 1)) = _
  rw [div_mul_cancel₀ _ hh.ne']
  exact m64Intrinsic_band_right_parameter L B hus

theorem m64Intrinsic_band_left_tip_mem_top :
    L (a, lo a) + ra • L (ua, wa) ∈ B.polygonalTop := by
  rw [← B.height_graph_image]
  refine ⟨0, by norm_num, ?_⟩
  change B.coordinates (collarParameterEquiv.symm (0, B.height 0)) = _
  rw [B.height_zero]
  exact m64Intrinsic_band_left_parameter L B B.interface.left_parameter_mem

theorem m64Intrinsic_band_right_tip_mem_top :
    L (b, lo b) + rb • L (ub, wb) ∈ B.polygonalTop := by
  rw [← B.height_graph_image]
  refine ⟨1, by norm_num, ?_⟩
  change B.coordinates (collarParameterEquiv.symm (1, B.height 1)) = _
  rw [B.height_one]
  exact m64Intrinsic_band_right_parameter L B B.interface.right_parameter_mem

end OneBand

theorem m64Intrinsic_band_shared_cut_interior
    (L L' : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {lo lo' : ℝ → ℝ} {a b ua wa ub wb ra r a' b' ua' wa' ub' wb' rb' : ℝ}
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      lo a b ua wa ub wb ra r)
    (B' : ObliqueBandFaces
      (collarParameterEquiv.trans L').toHomeomorph.toOpenPartialHomeomorph
      lo' a' b' ua' wa' ub' wb' r rb')
    {p d : AnnulusCoordinates}
    (hbase : L (b, lo b) = p) (hbase' : L' (a', lo' a') = p)
    (hdir : L (ub, wb) = d) (hdir' : L' (ua', wa') = d)
    (hcut : B.rightCut = segment ℝ p (p + r • d))
    (hcut' : B'.leftCut = segment ℝ p (p + r • d))
    (hinter : B.carrier ∩ B'.carrier = segment ℝ p (p + r • d)) :
    (fun u : ℝ => p + u • d) '' Ioo 0 r ⊆ interior (B.carrier ∪ B'.carrier) := by
  have hleft : (fun u : ℝ => p + u • d) '' Ioo 0 r ⊆
      (B.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
    simpa only [hbase, hdir] using m64Intrinsic_band_open_right_ray L B
  have hright : (fun u : ℝ => p + u • d) '' Ioo 0 r ⊆
      (B'.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
    simpa only [hbase', hdir'] using m64Intrinsic_band_open_left_ray L' B'
  apply (subset_inter hleft hright).trans
  apply B.shared_endpointCut_subset_interior_union B' true false
  · rw [B.endpointEdge_image, B'.endpointEdge_image]
    simp only [Bool.false_eq_true, ↓reduceIte, hcut, hcut']
  · rw [hinter, ← hcut]
    exact fun _ hz => B.outer_boundaries_subset_frontier (Or.inr hz)

end PoincareConjecture
