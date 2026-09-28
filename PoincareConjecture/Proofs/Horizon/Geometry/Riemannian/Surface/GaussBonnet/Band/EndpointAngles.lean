import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientSectorAngles
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.EndpointFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapBandSectorGerms







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Curves

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

private theorem fiber_fderiv_eq_cut_inverse
    {lo : ℝ → ℝ} {a u w : ℝ} (P : TransverseCutCoordinates lo a u w)
    {Q : (ℝ × ℝ) → ℝ × ℝ} {t η : ℝ}
    (hQ : DifferentiableAt ℝ Q (t, η)) (hη : η ∈ P.parameter.target)
    (he : (fun z : ℝ => Q (t, z)) =ᶠ[𝓝 η]
      fun z => (a + P.parameter.symm z * u, lo a + P.parameter.symm z * w)) :
    fderiv ℝ Q (t, η) (0, 1) = deriv P.parameter.symm η • (u, w) := by
  have hi := ((P.smooth_symm η hη).contDiffAt
    (P.parameter.open_target.mem_nhds hη)).differentiableAt (by simp) |>.hasDerivAt
  have hd := hQ.hasFDerivAt.comp_hasDerivAt η
    ((hasDerivAt_const η t).prodMk (hasDerivAt_id η))
  have hr := ((hi.mul_const u).const_add a).prodMk ((hi.mul_const w).const_add (lo a))
  have h := hd.unique (hr.congr_of_eventuallyEq he)
  simpa only [Prod.smul_mk, smul_eq_mul] using h

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {D : FiniteChartRegionDecomposition (M := S)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane S} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)



theorem first_outward_direction_eq_pos_smul :
    ∃ r : ℝ, 0 < r ∧ B.ambientOutwardDirection 0 = r • G.frame.symm (ua, wa) := by
  let Q := B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
  let η := B.faces.height 0
  have hband : collarParameterEquiv.symm (0, η) ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using
      (show (0 : ℝ) ∈ Icc 0 1 ∧ 0 ≤ η ∧ η ≤ B.faces.height 0 from
        ⟨by simp, (B.faces.height_pos (by simp)).le, le_rfl⟩)
  have hs := (B.faces.band_subset_source hband).1.1.2
  change collarParameterEquiv (collarParameterEquiv.symm (0, η)) ∈ Q.source at hs
  rw [collarParameterEquiv.apply_symm_apply] at hs
  have hQ := ((B.faces.cuts.smooth_coordinates B.faces.open_domain B.faces.smooth_lower).contDiffAt
    (Q.open_source.mem_nhds hs)).differentiableAt (by simp)
  have hη : η ∈ B.faces.cuts.left.parameter.target := by
    dsimp only [η]
    rw [B.faces.height_zero]
    exact B.faces.cuts.left.parameter.map_source B.faces.interface.left_parameter_mem
  have he : (fun z : ℝ => Q (0, z)) =ᶠ[𝓝 η] fun z =>
      (G.parameter a + B.faces.cuts.left.parameter.symm z * ua,
        G.lower (G.parameter a) + B.faces.cuts.left.parameter.symm z * wa) := by
    filter_upwards [B.faces.cuts.left.parameter.open_target.mem_nhds hη] with z hz
    exact (B.faces.cuts.coordinates_apply _ _ _).trans
      ((obliqueStripMap_left _ _ _ _).trans (B.faces.cuts.left.line_identity hz))
  have hd := fiber_fderiv_eq_cut_inverse B.faces.cuts.left hQ hη he
  refine ⟨deriv B.faces.cuts.left.parameter.symm η,
    B.faces.cuts.left.inverse_positive_deriv hη, ?_⟩
  dsimp only [ambientOutwardDirection]
  rw [B.faces.cut_first, B.faces.interface.height_first, ← B.faces.height_zero]
  rw [hd, map_smul]



theorem last_outward_direction_eq_pos_smul :
    ∃ r : ℝ, 0 < r ∧ B.ambientOutwardDirection (Fin.last B.faces.interface.count) =
      r • G.frame.symm (ub, wb) := by
  let Q := B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
  let η := B.faces.height 1
  have hband : collarParameterEquiv.symm (1, η) ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using
      (show (1 : ℝ) ∈ Icc 0 1 ∧ 0 ≤ η ∧ η ≤ B.faces.height 1 from
        ⟨by simp, (B.faces.height_pos (by simp)).le, le_rfl⟩)
  have hs := (B.faces.band_subset_source hband).1.1.2
  change collarParameterEquiv (collarParameterEquiv.symm (1, η)) ∈ Q.source at hs
  rw [collarParameterEquiv.apply_symm_apply] at hs
  have hQ := ((B.faces.cuts.smooth_coordinates B.faces.open_domain B.faces.smooth_lower).contDiffAt
    (Q.open_source.mem_nhds hs)).differentiableAt (by simp)
  have hη : η ∈ B.faces.cuts.right.parameter.target := by
    dsimp only [η]
    rw [B.faces.height_one]
    exact B.faces.cuts.right.parameter.map_source B.faces.interface.right_parameter_mem
  have he : (fun z : ℝ => Q (1, z)) =ᶠ[𝓝 η] fun z =>
      (G.parameter b + B.faces.cuts.right.parameter.symm z * ub,
        G.lower (G.parameter b) + B.faces.cuts.right.parameter.symm z * wb) := by
    filter_upwards [B.faces.cuts.right.parameter.open_target.mem_nhds hη] with z hz
    exact (B.faces.cuts.coordinates_apply _ _ _).trans
      ((obliqueStripMap_right _ _ _ _).trans (B.faces.cuts.right.line_identity hz))
  have hd := fiber_fderiv_eq_cut_inverse B.faces.cuts.right hQ hη he
  refine ⟨deriv B.faces.cuts.right.parameter.symm η,
    B.faces.cuts.right.inverse_positive_deriv hη, ?_⟩
  dsimp only [ambientOutwardDirection]
  rw [B.faces.cut_last, B.faces.interface.height_last, ← B.faces.height_one]
  rw [hd, map_smul]



theorem first_top_cut_determinant_pos :
    0 < wa - (B.faces.interface.piece B.faces.firstCell).linear 1 * ua := by
  have h := B.ambientTopFunctional_outward_pos B.faces.firstCell 0 (Or.inl rfl)
  obtain ⟨r, hr, he⟩ := B.first_outward_direction_eq_pos_smul
  rw [he, map_smul] at h
  have hp := (mul_pos_iff_of_pos_left hr).mp h
  simpa only [B.ambientTopFunctional_linear, G.frame.apply_symm_apply] using hp



theorem last_top_cut_determinant_pos :
    0 < wb - (B.faces.interface.piece B.faces.lastCell).linear 1 * ub := by
  have hlast : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
    apply Fin.ext
    dsimp [ObliqueBandFaces.lastCell]
    have hn := B.faces.interface.count_pos
    omega
  have h := B.ambientTopFunctional_outward_pos B.faces.lastCell
    (Fin.last B.faces.interface.count) (Or.inr hlast.symm)
  obtain ⟨r, hr, he⟩ := B.last_outward_direction_eq_pos_smul
  rw [he, map_smul] at h
  have hp := (mul_pos_iff_of_pos_left hr).mp h
  simpa only [B.ambientTopFunctional_linear, G.frame.apply_symm_apply] using hp



theorem first_complementary_positive_rays (c : AffineBasis (Fin 3) ℝ Plane)
    (hc1 : c.coord 1 = -B.ambientEndpointCut false)
    (hc2 : c.coord 2 = B.ambientEndpointTop false) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      B.chartTopVertex B.faces.firstCell.succ - B.chartTopVertex 0 = r • (c 1 - c 0) ∧
      G.frame.symm (ua, wa) = s • (c 2 - c 0) := by
  let v := B.chartTopVertex B.faces.firstCell.succ - B.chartTopVertex 0
  let d := G.frame.symm (ua, wa)
  have htop : (B.ambientEndpointTop false).linear v = 0 := by
    change (B.ambientTopFunctional B.faces.firstCell).linear
      (B.chartTopVertex B.faces.firstCell.succ -ᵥ B.chartTopVertex B.faces.firstCell.castSucc) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub,
      B.ambientTopFunctional_right_vertex, B.ambientTopFunctional_left_vertex, sub_self]
  have hx : 0 < (G.frame v).1 := by
    simp only [v, map_sub, chartTopVertex, G.frame.apply_symm_apply, Prod.fst_sub]
    exact sub_pos.mpr (B.faces.interface.cut_strictMono
      (Fin.castSucc_lt_succ (i := B.faces.firstCell)))
  have hv : 0 < (c.coord 1).linear v := by
    have hy := htop
    change (B.ambientTopFunctional B.faces.firstCell).linear v = 0 at hy
    rw [B.ambientTopFunctional_linear] at hy
    rw [hc1]
    change 0 < -(B.ambientEndpointCut false).linear v
    rw [B.ambientEndpointCut_linear_apply]
    simp only [Bool.false_eq_true, ite_false, neg_neg]
    have hp := mul_pos B.first_top_cut_determinant_pos hx
    nlinarith [congrArg (fun r : ℝ => ua * r) hy]
  have hd : 0 < (c.coord 2).linear d := by
    rw [hc2]
    change 0 < (B.ambientTopFunctional B.faces.firstCell).linear (G.frame.symm (ua, wa))
    simpa only [B.ambientTopFunctional_linear, G.frame.apply_symm_apply] using
      B.first_top_cut_determinant_pos
  have hv2 : (c.coord 2).linear v = 0 := by rw [hc2]; exact htop
  have hd1 : (c.coord 1).linear d = 0 := by
    rw [hc1]
    change -(B.ambientEndpointCut false).linear d = 0
    rw [B.ambientEndpointCut_linear_apply]
    simp [d, mul_comm]
  refine ⟨(c.coord 1).linear v, (c.coord 2).linear d, hv, hd, ?_, ?_⟩
  · simpa only [hv2, zero_smul, add_zero] using affineBasis_direction_expansion c v
  · simpa only [hd1, zero_smul, zero_add] using affineBasis_direction_expansion c d



theorem last_complementary_positive_rays (c : AffineBasis (Fin 3) ℝ Plane)
    (hc1 : c.coord 1 = -B.ambientEndpointCut true)
    (hc2 : c.coord 2 = B.ambientEndpointTop true) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      B.chartTopVertex B.faces.lastCell.castSucc - B.chartTopVertex B.faces.lastCell.succ =
        r • (c 1 - c 0) ∧
      G.frame.symm (ub, wb) = s • (c 2 - c 0) := by
  let v := B.chartTopVertex B.faces.lastCell.castSucc - B.chartTopVertex B.faces.lastCell.succ
  let d := G.frame.symm (ub, wb)
  have htop : (B.ambientEndpointTop true).linear v = 0 := by
    change (B.ambientTopFunctional B.faces.lastCell).linear
      (B.chartTopVertex B.faces.lastCell.castSucc -ᵥ B.chartTopVertex B.faces.lastCell.succ) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub,
      B.ambientTopFunctional_right_vertex, B.ambientTopFunctional_left_vertex, sub_self]
  have hx : (G.frame v).1 < 0 := by
    simp only [v, map_sub, chartTopVertex, G.frame.apply_symm_apply, Prod.fst_sub]
    exact sub_neg.mpr (B.faces.interface.cut_strictMono Fin.castSucc_lt_succ)
  have hv : 0 < (c.coord 1).linear v := by
    have hy := htop
    change (B.ambientTopFunctional B.faces.lastCell).linear v = 0 at hy
    rw [B.ambientTopFunctional_linear] at hy
    rw [hc1]
    change 0 < -(B.ambientEndpointCut true).linear v
    rw [B.ambientEndpointCut_linear_apply]
    simp only [ite_true]
    have hp := mul_neg_of_pos_of_neg B.last_top_cut_determinant_pos hx
    nlinarith [congrArg (fun r : ℝ => ub * r) hy]
  have hd : 0 < (c.coord 2).linear d := by
    rw [hc2]
    change 0 < (B.ambientTopFunctional B.faces.lastCell).linear (G.frame.symm (ub, wb))
    simpa only [B.ambientTopFunctional_linear, G.frame.apply_symm_apply] using
      B.last_top_cut_determinant_pos
  have hv2 : (c.coord 2).linear v = 0 := by rw [hc2]; exact htop
  have hd1 : (c.coord 1).linear d = 0 := by
    rw [hc1]
    change -(B.ambientEndpointCut true).linear d = 0
    rw [B.ambientEndpointCut_linear_apply]
    simp [d, mul_comm]
  refine ⟨(c.coord 1).linear v, (c.coord 2).linear d, hv, hd, ?_, ?_⟩
  · simpa only [hv2, zero_smul, add_zero] using affineBasis_direction_expansion c v
  · simpa only [hd1, zero_smul, zero_add] using affineBasis_direction_expansion c d

theorem chart_first_top_eq_physical (hab : a ≤ b) :
    B.chartTopVertex 0 = C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa) := by
  have h := congrArg (fun z => G.frame.symm (collarParameterEquiv z)) (B.ambient_first_vertex hab)
  simpa only [collarParameterEquiv.apply_symm_apply, G.frame.symm_apply_apply,
    ObliqueBandFaces.planarTopVertex, chartTopVertex] using h.symm

theorem chart_last_top_eq_physical (hab : a ≤ b) :
    B.chartTopVertex (Fin.last B.faces.interface.count) =
      C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb) := by
  have h := congrArg (fun z => G.frame.symm (collarParameterEquiv z)) (B.ambient_last_vertex hab)
  simpa only [collarParameterEquiv.apply_symm_apply, G.frame.symm_apply_apply,
    ObliqueBandFaces.planarTopVertex, chartTopVertex] using h.symm



theorem first_downward_velocity_pos_smul_chart_differential
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) (hab : a ≤ b) :
    ∃ r : ℝ, 0 < r ∧
      coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
        (B.faces.faceBasis (B.faces.firstCell, true)) 1 0 =
        r • mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex 0) (-G.frame.symm (ua, wa)) := by
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have h0 : B.firstUpperChartBasis 0 = B.chartTopVertex 0 := by
    change (collarParameterEquiv.trans G.frame.symm) (B.faces.firstUpperCornerBasis 0) = _
    rw [B.faces.firstUpperCornerBasis_zero]
    simp [chartTopVertex]
  have h2 : B.firstUpperChartBasis 2 = C.symm ((D.edge e.1 e.2).map a) := by
    have hbase := G.graph_coordinates a (G.interval_source (left_mem_Icc.mpr hab))
    change G.frame.symm (G.parameter a, G.lower (G.parameter a)) = _
    rw [← hbase, G.frame.symm_apply_apply]
  have hne : B.chartTopVertex 0 ≠ C.symm ((D.edge e.1 e.2).map a) := by
    rw [← h0, ← h2]
    exact B.firstUpperChartBasis.ind.injective.ne (by decide)
  have hsource : segment ℝ (B.chartTopVertex 0) (C.symm ((D.edge e.1 e.2).map a)) ⊆ C.source := by
    rw [← h0, ← h2]
    exact (subset_union_right).trans B.firstUpperChartSides_subset_source
  have himage : (fun t : ℝ => B.faces.faceCoordinates (B.faces.firstCell, true)
      (AffineMap.lineMap (B.faces.faceBasis (B.faces.firstCell, true) 1)
        (B.faces.faceBasis (B.faces.firstCell, true) 0) t)) '' Icc (0 : ℝ) 1 ⊆
      C '' segment ℝ (B.chartTopVertex 0) (C.symm ((D.edge e.1 e.2).map a)) := by
    rw [B.chart_first_top_eq_physical hab, segment_symm, ← B.leftCut_eq_segment hab]
    have hcut : ((B.faces.pair B.faces.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 =
        B.faces.leftCut := B.faces.left_edge_image
    rw [← hcut]
    have h := B.faces.face_boundary_image (B.faces.firstCell, true) 2
    change ((B.faces.pair B.faces.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 = _ at h
    rw [h]
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    have he : affineChartSegment (B.faces.faceBasis (B.faces.firstCell, true) ((2 : Fin 3).succAbove 0))
        (B.faces.faceBasis (B.faces.firstCell, true) ((2 : Fin 3).succAbove 1)) (1 - t) =
        AffineMap.lineMap (B.faces.faceBasis (B.faces.firstCell, true) 0)
          (B.faces.faceBasis (B.faces.firstCell, true) 1) (1 - t) := by
      rw [show (2 : Fin 3).succAbove 0 = 0 by decide,
        show (2 : Fin 3).succAbove 1 = 1 by decide]
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    dsimp only [Function.comp_apply]
    rw [he]
    change B.faces.faceCoordinates (B.faces.firstCell, true)
      (AffineMap.lineMap (B.faces.faceBasis (B.faces.firstCell, true) 0)
        (B.faces.faceBasis (B.faces.firstCell, true) 1) (1 - t)) = _
    rw [AffineMap.lineMap_apply_one_sub]
  have hpoint : B.faces.faceCoordinates (B.faces.firstCell, true)
      (B.faces.faceBasis (B.faces.firstCell, true) 1) = C (B.chartTopVertex 0) := by
    rw [B.faces.face_corner_eq_vertex]
    exact B.vertex_top_eq_chartTopVertex B.faces.firstCell 0 (Or.inl rfl)
  obtain ⟨r, hr, hv⟩ := coordinateTriangleVelocity_pos_smul_of_chart_segment
    (B.faces.faceCoordinates (B.faces.firstCell, true)) C (B.faces.faceBasis (B.faces.firstCell, true))
    (B.faces.smooth_faceCoordinates hF.1 _) (B.faces.smooth_faceCoordinates_symm hF.2 _)
    hC hCi (B.faces.face_triangle_subset_source _) (by decide : (1 : Fin 3) ≠ 0)
    hne hsource himage hpoint
  refine ⟨r * ra, mul_pos hr B.faces.left_length_pos, ?_⟩
  have he : C.symm ((D.edge e.1 e.2).map a) - B.chartTopVertex 0 = ra • (-G.frame.symm (ua, wa)) := by
    rw [B.chart_first_top_eq_physical hab]
    module
  rw [he, map_smul, smul_smul] at hv
  exact hv



theorem first_refined_fan_add_complementary_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) (hab : a ≤ b)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = B.chartTopVertex 0)
    (hc1 : c.coord 1 = -B.ambientEndpointCut false)
    (hc2 : c.coord 2 = B.ambientEndpointTop false) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C (c 0))) +
      g.cornerAngle (C (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 2 - c 0)) = Real.pi := by
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C (c 0)
  obtain ⟨r, s, hr, hs, hu, hd⟩ := B.first_complementary_positive_rays c hc1 hc2
  obtain ⟨r', hr', ht⟩ := B.topRightChord_pos_smul_chart_differential hC hCi B.faces.firstCell
  let A : Plane → (Plane →L[ℝ] Plane) := fun z => mfderiv (𝓡 2) (𝓡 2) C z
  have hL : (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex 0) : Plane →L[ℝ] Plane) = L :=
    congrArg A hc0.symm
  have ht' : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
      (B.faces.faceBasis (B.faces.firstCell, true)) 1 2 : Plane) =
      (r' * r) • L (c 1 - c 0) := by
    have h : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
        (B.faces.faceBasis (B.faces.firstCell, true)) 1 2 : Plane) =
        r' • L (B.chartTopVertex B.faces.firstCell.succ - B.chartTopVertex 0) :=
      ht.trans (congrArg (fun A : Plane →L[ℝ] Plane =>
        r' • A (B.chartTopVertex B.faces.firstCell.succ - B.chartTopVertex 0)) hL)
    rwa [hu, map_smul, smul_smul] at h
  obtain ⟨s', hs', hv⟩ := B.first_downward_velocity_pos_smul_chart_differential hC hCi hab
  have hv' : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
      (B.faces.faceBasis (B.faces.firstCell, true)) 1 0 : Plane) =
      (s' * s) • (-L (c 2 - c 0)) := by
    have h : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
        (B.faces.faceBasis (B.faces.firstCell, true)) 1 0 : Plane) =
        s' • L (-G.frame.symm (ua, wa)) :=
      hv.trans (congrArg (fun A : Plane →L[ℝ] Plane => s' • A (-G.frame.symm (ua, wa))) hL)
    rwa [hd, map_neg, map_smul, ← smul_neg, smul_smul] at h
  have hx : B.faces.vertex (0, true) = C (c 0) := by
    rw [hc0]
    exact B.vertex_top_eq_chartTopVertex B.faces.firstCell 0 (Or.inl rfl)
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.first_top_refined_vertex_fan g hF.1 hF.2 lines
  rw [hx, ht', hv', g.cornerAngle_smul_pos_left _ _ _ (mul_pos hr' hr),
    g.cornerAngle_smul_pos_right _ _ _ (mul_pos hs' hs), g.cornerAngle_neg_right] at hfan
  change _ + g.cornerAngle (C (c 0)) (L (c 1 - c 0)) (L (c 2 - c 0)) = _
  rw [hfan]
  ring



theorem last_refined_fan_add_complementary_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = B.chartTopVertex (Fin.last B.faces.interface.count))
    (hc1 : c.coord 1 = -B.ambientEndpointCut true)
    (hc2 : c.coord 2 = B.ambientEndpointTop true) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C (c 0))) +
      g.cornerAngle (C (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 2 - c 0)) = Real.pi := by
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C (c 0)
  have hlast : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
    apply Fin.ext
    dsimp [ObliqueBandFaces.lastCell]
    have hn := B.faces.interface.count_pos
    omega
  obtain ⟨r, s, hr, hs, hu, hd⟩ := B.last_complementary_positive_rays c hc1 hc2
  obtain ⟨r', hr', ht⟩ := B.topLeftChord_pos_smul_chart_differential hC hCi B.faces.lastCell
  let A : Plane → (Plane →L[ℝ] Plane) := fun z => mfderiv (𝓡 2) (𝓡 2) C z
  have hL : (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex B.faces.lastCell.succ) : Plane →L[ℝ] Plane) = L := by
    exact congrArg A (by rw [hlast, hc0])
  have ht' : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.lastCell, true))
      (B.faces.faceBasis (B.faces.lastCell, true)) 2 1 : Plane) =
      (r' * r) • L (c 1 - c 0) := by
    have h : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.lastCell, true))
        (B.faces.faceBasis (B.faces.lastCell, true)) 2 1 : Plane) =
        r' • L (B.chartTopVertex B.faces.lastCell.castSucc - B.chartTopVertex B.faces.lastCell.succ) :=
      ht.trans (congrArg (fun A : Plane →L[ℝ] Plane =>
        r' • A (B.chartTopVertex B.faces.lastCell.castSucc - B.chartTopVertex B.faces.lastCell.succ)) hL)
    rwa [hu, map_smul, smul_smul] at h
  obtain ⟨s', hs', hv⟩ := B.last_outward_direction_eq_pos_smul
  have hout := B.topOutwardRay_eq_chart_differential hC hCi B.faces.lastCell
  have hout' : (B.faces.topOutwardRay B.faces.lastCell : Plane) =
      B.faces.interface.height B.faces.lastCell.succ • L (B.ambientOutwardDirection B.faces.lastCell.succ) :=
    hout.trans (congrArg (fun A : Plane →L[ℝ] Plane =>
      B.faces.interface.height B.faces.lastCell.succ • A (B.ambientOutwardDirection B.faces.lastCell.succ)) hL)
  rw [hlast, hv, hd, map_smul, map_smul, smul_smul, smul_smul] at hout'
  have hv' : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.lastCell, false))
      (B.faces.faceBasis (B.faces.lastCell, false)) 2 1 : Plane) =
      (B.faces.interface.height (Fin.last B.faces.interface.count) * (s' * s)) •
        (-L (c 2 - c 0)) := by
    have h := congrArg Neg.neg hout'
    simpa only [ObliqueBandFaces.topOutwardRay, neg_neg, smul_neg, mul_assoc] using h
  have hpos : 0 < B.faces.interface.height (Fin.last B.faces.interface.count) * (s' * s) :=
    mul_pos (B.faces.interface.vertex_height_bounds _).1 (mul_pos hs' hs)
  have hx : B.faces.vertex (Fin.last B.faces.interface.count, true) = C (c 0) := by
    rw [hc0]
    exact B.vertex_top_eq_chartTopVertex B.faces.lastCell _ (Or.inr hlast.symm)
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.last_top_refined_vertex_fan g hF.1 hF.2 lines
  rw [hx, ht', hv', g.cornerAngle_smul_pos_left _ _ _ (mul_pos hr' hr),
    g.cornerAngle_smul_pos_right _ _ _ hpos, g.cornerAngle_neg_right] at hfan
  change _ + g.cornerAngle (C (c 0)) (L (c 1 - c 0)) (L (c 2 - c 0)) = _
  rw [hfan]
  ring



theorem first_actual_fan_add_complementary_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) (hab : a ≤ b)
    (M : (Fin B.faces.interface.count × Bool) → TriangleMesh)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (hM : ∀ p, M p = (TriangleMesh.single (B.faces.faceBasis p)
      (B.faces.faceBasis p).ind).refineByLines (lines p))
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = B.chartTopVertex 0)
    (hc1 : c.coord 1 = -B.ambientEndpointCut false)
    (hc2 : c.coord 2 = B.ambientEndpointTop false) :
    (∑ p, meshVertexAngleContribution g (B.faces.faceCoordinates p) (M p) (C (c 0))) +
      g.cornerAngle (C (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 2 - c 0)) = Real.pi := by
  have heq : M = fun p => (TriangleMesh.single (B.faces.faceBasis p)
      (B.faces.faceBasis p).ind).refineByLines (lines p) := funext hM
  subst M
  exact B.first_refined_fan_add_complementary_angle g hC hCi hab lines c hc0 hc1 hc2



theorem last_actual_fan_add_complementary_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (M : (Fin B.faces.interface.count × Bool) → TriangleMesh)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (hM : ∀ p, M p = (TriangleMesh.single (B.faces.faceBasis p)
      (B.faces.faceBasis p).ind).refineByLines (lines p))
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = B.chartTopVertex (Fin.last B.faces.interface.count))
    (hc1 : c.coord 1 = -B.ambientEndpointCut true)
    (hc2 : c.coord 2 = B.ambientEndpointTop true) :
    (∑ p, meshVertexAngleContribution g (B.faces.faceCoordinates p) (M p) (C (c 0))) +
      g.cornerAngle (C (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) C (c 0)) (c 2 - c 0)) = Real.pi := by
  have heq : M = fun p => (TriangleMesh.single (B.faces.faceBasis p)
      (B.faces.faceBasis p).ind).refineByLines (lines p) := funext hM
  subst M
  exact B.last_refined_fan_add_complementary_angle g hC hCi lines c hc0 hc1 hc2



theorem first_refined_fan_add_physical_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) (hab : a ≤ b)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    let q := B.chartTopVertex 0
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C q)) +
      g.cornerAngle (C q)
        ((mfderiv (𝓡 2) (𝓡 2) C q) (B.chartTopVertex B.faces.firstCell.succ - q))
        ((mfderiv (𝓡 2) (𝓡 2) C q) (G.frame.symm (ua, wa))) = Real.pi := by
  let q := B.chartTopVertex 0
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C q
  obtain ⟨r, hr, ht⟩ := B.topRightChord_pos_smul_chart_differential hC hCi B.faces.firstCell
  obtain ⟨s, hs, hv⟩ := B.first_downward_velocity_pos_smul_chart_differential hC hCi hab
  change (B.faces.topRightChord B.faces.firstCell : Plane) =
    r • L (B.chartTopVertex B.faces.firstCell.succ - q) at ht
  dsimp only [ObliqueBandFaces.topRightChord] at ht
  change (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
    (B.faces.faceBasis (B.faces.firstCell, true)) 1 0 : Plane) =
    s • L (-G.frame.symm (ua, wa)) at hv
  rw [map_neg] at hv
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.first_top_refined_vertex_fan g hF.1 hF.2 lines
  have hx := B.vertex_top_eq_chartTopVertex B.faces.firstCell 0 (Or.inl rfl)
  rw [hx, ht, hv, g.cornerAngle_smul_pos_left _ _ _ hr,
    g.cornerAngle_smul_pos_right _ _ _ hs, g.cornerAngle_neg_right] at hfan
  change _ + g.cornerAngle (C q) (L (B.chartTopVertex B.faces.firstCell.succ - q))
    (L (G.frame.symm (ua, wa))) = _
  rw [hfan]
  ring



theorem last_refined_fan_add_physical_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    let q := B.chartTopVertex B.faces.lastCell.succ
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C q)) +
      g.cornerAngle (C q)
        ((mfderiv (𝓡 2) (𝓡 2) C q) (B.chartTopVertex B.faces.lastCell.castSucc - q))
        ((mfderiv (𝓡 2) (𝓡 2) C q) (G.frame.symm (ub, wb))) = Real.pi := by
  let q := B.chartTopVertex B.faces.lastCell.succ
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C q
  have hlast : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
    apply Fin.ext
    dsimp [ObliqueBandFaces.lastCell]
    have hn := B.faces.interface.count_pos
    omega
  obtain ⟨r, hr, ht⟩ := B.topLeftChord_pos_smul_chart_differential hC hCi B.faces.lastCell
  change (B.faces.topLeftChord B.faces.lastCell : Plane) =
    r • L (B.chartTopVertex B.faces.lastCell.castSucc - q) at ht
  dsimp only [ObliqueBandFaces.topLeftChord] at ht
  obtain ⟨s, hs, hd⟩ := B.last_outward_direction_eq_pos_smul
  have hout := B.topOutwardRay_eq_chart_differential hC hCi B.faces.lastCell
  change (B.faces.topOutwardRay B.faces.lastCell : Plane) =
    B.faces.interface.height B.faces.lastCell.succ •
      L (B.ambientOutwardDirection B.faces.lastCell.succ) at hout
  rw [hlast, hd, map_smul, smul_smul] at hout
  have hv : (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.lastCell, false))
      (B.faces.faceBasis (B.faces.lastCell, false)) 2 1 : Plane) =
      (B.faces.interface.height (Fin.last B.faces.interface.count) * s) •
        (-L (G.frame.symm (ub, wb))) := by
    have h := congrArg Neg.neg hout
    simpa only [ObliqueBandFaces.topOutwardRay, neg_neg, smul_neg] using h
  have hpos := mul_pos (B.faces.interface.vertex_height_bounds (Fin.last B.faces.interface.count)).1 hs
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.last_top_refined_vertex_fan g hF.1 hF.2 lines
  have hx := B.vertex_top_eq_chartTopVertex B.faces.lastCell
    (Fin.last B.faces.interface.count) (Or.inr hlast.symm)
  have hx' : B.faces.vertex (Fin.last B.faces.interface.count, true) = C q := by
    simpa only [q, hlast] using hx
  rw [hx', ht, hv, g.cornerAngle_smul_pos_left _ _ _ hr,
    g.cornerAngle_smul_pos_right _ _ _ hpos, g.cornerAngle_neg_right] at hfan
  change _ + g.cornerAngle (C q) (L (B.chartTopVertex B.faces.lastCell.castSucc - q))
    (L (G.frame.symm (ub, wb))) = _
  rw [hfan]
  ring

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

end PoincareConjecture.Topology.Surface
