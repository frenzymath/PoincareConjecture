import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAttachmentGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCoreSectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientSectorAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Curves

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {D : FiniteChartRegionDecomposition (M := S)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane S} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

theorem ambientEndpointTop_first_base_ne_zero (hab : a ≤ b) :
    B.ambientEndpointTop false (C.symm ((D.edge e.1 e.2).map a)) ≠ 0 := by
  have hbase := G.graph_coordinates a (G.interval_source (left_mem_Icc.mpr hab))
  have h := B.faces.first_upper_line_avoids_lower_left
  change (G.frame (C.symm ((D.edge e.1 e.2).map a))).2 -
    B.faces.interface.piece B.faces.firstCell
      (G.frame (C.symm ((D.edge e.1 e.2).map a))).1 ≠ 0
  rw [hbase]
  exact sub_ne_zero.mpr h.symm

theorem ambient_first_endpoint_independent (hab : a ≤ b) :
    LinearIndependent ℝ
      (![(-B.ambientEndpointCut false).linear, (B.ambientEndpointTop false).linear] :
        Fin 2 → Module.Dual ℝ Plane) := by
  let q := C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)
  let p := C.symm ((D.edge e.1 e.2).map a)
  have hz := B.ambient_first_endpoint_functionals_vanish hab
  have hp := B.ambientEndpointCut_first_base hab
  rw [linearIndependent_fin2]
  refine ⟨?_, ?_⟩
  · intro h
    have hv := B.ambientTopFunctional_vertical B.faces.firstCell
    change (B.ambientEndpointTop false).linear (G.frame.symm (0, 1)) = 1 at hv
    change (B.ambientEndpointTop false).linear = 0 at h
    rw [h, LinearMap.zero_apply] at hv
    exact zero_ne_one hv
  · intro r he
    have he' := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f (p - q)) he
    change r * (B.ambientEndpointTop false).linear (p - q) =
      -(B.ambientEndpointCut false).linear (p - q) at he'
    have hc : (B.ambientEndpointCut false).linear (p - q) = 0 := by
      change (B.ambientEndpointCut false).linear (p -ᵥ q) = 0
      rw [AffineMap.linearMap_vsub, vsub_eq_sub, hp, hz.1, sub_self]
    have ht : (B.ambientEndpointTop false).linear (p - q) = B.ambientEndpointTop false p := by
      change (B.ambientEndpointTop false).linear (p -ᵥ q) = _
      rw [AffineMap.linearMap_vsub, vsub_eq_sub, hz.2, sub_zero]
    rw [hc, ht, neg_zero] at he'
    have hr : r = 0 := (mul_eq_zero.mp he').resolve_right
      (B.ambientEndpointTop_first_base_ne_zero hab)
    obtain ⟨z, hz⟩ := (AffineMap.linear_surjective_iff (B.ambientEndpointCut false)).mpr
      (B.ambientEndpointCut_surjective false) 1
    have hbad := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f z) he
    change r * (B.ambientEndpointTop false).linear z = -(B.ambientEndpointCut false).linear z at hbad
    rw [hr, zero_mul, hz] at hbad
    norm_num at hbad

theorem exists_ambient_first_complementary_coordinates (hab : a ≤ b) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa) ∧
      c.coord 1 = -B.ambientEndpointCut false ∧ c.coord 2 = B.ambientEndpointTop false := by
  have hz := B.ambient_first_endpoint_functionals_vanish hab
  exact exists_affineBasis_coords_of_independent_functionals _ _ _
    (by change -(B.ambientEndpointCut false _) = 0; rw [hz.1, neg_zero]) hz.2
    (B.ambient_first_endpoint_independent hab)

theorem ambientEndpointCut_last_outward_zero :
    (B.ambientEndpointCut true).linear
      (B.ambientOutwardDirection (Fin.last B.faces.interface.count)) = 0 := by
  let Q := B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
  let η := B.faces.height 1
  let n : (ℝ × ℝ) →L[ℝ] ℝ := wb • ContinuousLinearMap.fst ℝ ℝ ℝ -
    ub • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hband : collarParameterEquiv.symm (1, η) ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using
      (show (1 : ℝ) ∈ Icc 0 1 ∧ 0 ≤ η ∧ η ≤ B.faces.height 1 from
        ⟨by simp, (B.faces.height_pos (by simp)).le, le_rfl⟩)
  have hs := B.faces.band_subset_source hband
  have hQs : (1, η) ∈ Q.source := by
    have hs' := hs.1.1.2
    change collarParameterEquiv (collarParameterEquiv.symm (1, η)) ∈ Q.source at hs'
    simpa only [collarParameterEquiv.apply_symm_apply] using hs'
  have hQ := ((B.faces.cuts.smooth_coordinates B.faces.open_domain B.faces.smooth_lower).contDiffAt
    (Q.open_source.mem_nhds hQs)).differentiableAt (by simp)
  have hη : η ∈ B.faces.cuts.right.parameter.target := by
    dsimp only [η]
    rw [B.faces.height_one]
    exact B.faces.cuts.right.parameter.map_source B.faces.interface.right_parameter_mem
  have he : (fun z : ℝ => n (Q (1, z))) =ᶠ[𝓝 η] fun _ => wb * G.parameter b - ub * G.lower (G.parameter b) := by
    filter_upwards [B.faces.cuts.right.parameter.open_target.mem_nhds hη] with z hz
    dsimp only [Q]
    rw [B.faces.cuts.coordinates_apply, obliqueStripMap_right, B.faces.cuts.right.line_identity hz]
    change wb * (G.parameter b + B.faces.cuts.right.parameter.symm z * ub) -
      ub * (G.lower (G.parameter b) + B.faces.cuts.right.parameter.symm z * wb) = _
    ring
  have hd := n.hasFDerivAt.comp_hasDerivAt η
    (hQ.hasFDerivAt.comp_hasDerivAt η ((hasDerivAt_const η (1 : ℝ)).prodMk (hasDerivAt_id η)))
  have hz := hd.unique ((hasDerivAt_const η _).congr_of_eventuallyEq he)
  change n (fderiv ℝ Q (1, η) (0, 1)) = 0 at hz
  rw [B.ambientEndpointCut_linear_apply]
  simp only [ite_true, ambientOutwardDirection, G.frame.apply_symm_apply, B.faces.cut_last,
    B.faces.interface.height_last, ← B.faces.height_one]
  exact hz

theorem ambient_last_endpoint_independent :
    LinearIndependent ℝ
      (![(-B.ambientEndpointCut true).linear, (B.ambientEndpointTop true).linear] :
        Fin 2 → Module.Dual ℝ Plane) := by
  have hlast : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
    apply Fin.ext
    dsimp [ObliqueBandFaces.lastCell]
    have hn := B.faces.interface.count_pos
    omega
  have hp := B.ambientTopFunctional_outward_pos B.faces.lastCell
    (Fin.last B.faces.interface.count) (Or.inr hlast.symm)
  change 0 < (B.ambientEndpointTop true).linear
    (B.ambientOutwardDirection (Fin.last B.faces.interface.count)) at hp
  rw [linearIndependent_fin2]
  refine ⟨?_, ?_⟩
  · intro h
    change (B.ambientEndpointTop true).linear = 0 at h
    rw [h, LinearMap.zero_apply] at hp
    exact lt_irrefl _ hp
  · intro r he
    have h := congrArg (fun f : Plane →ₗ[ℝ] ℝ =>
      f (B.ambientOutwardDirection (Fin.last B.faces.interface.count))) he
    change r * (B.ambientEndpointTop true).linear _ = -(B.ambientEndpointCut true).linear _ at h
    rw [B.ambientEndpointCut_last_outward_zero, neg_zero] at h
    have hr : r = 0 := (mul_eq_zero.mp h).resolve_right hp.ne'
    obtain ⟨z, hz⟩ := (AffineMap.linear_surjective_iff (B.ambientEndpointCut true)).mpr
      (B.ambientEndpointCut_surjective true) 1
    have hbad := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f z) he
    change r * (B.ambientEndpointTop true).linear z = -(B.ambientEndpointCut true).linear z at hbad
    rw [hr, zero_mul, hz] at hbad
    norm_num at hbad

theorem exists_ambient_last_complementary_coordinates (hab : a ≤ b) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb) ∧
      c.coord 1 = -B.ambientEndpointCut true ∧ c.coord 2 = B.ambientEndpointTop true := by
  have hz := B.ambient_last_endpoint_functionals_vanish hab
  exact exists_affineBasis_coords_of_independent_functionals _ _ _
    (by change -(B.ambientEndpointCut true _) = 0; rw [hz.1, neg_zero]) hz.2
    B.ambient_last_endpoint_independent

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {radius : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch radius p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem chordSupportingLine_endpoint_direction (s : Bool × Bool) (vertical : Bool) :
    B.chordSupportingLine s (B.chordEndpoint s vertical) = 0 ∧
      (B.chordSupportingLine s).linear (B.chordDirection s vertical) = 0 := by
  have hfirst : B.chordSupportingLine s (B.planarCoordinates s (B.scale, 0)) = 0 := by
    apply (B.chordSupportingLine_spec s).2
    rw [chartChord, B.planar_first s B.scale ⟨B.scale_pos.le, le_rfl⟩]
    exact left_mem_affineSegment ℝ _ _
  have hsecond : B.chordSupportingLine s (B.planarCoordinates s (0, B.scale)) = 0 := by
    apply (B.chordSupportingLine_spec s).2
    rw [chartChord, B.planar_second s B.scale ⟨B.scale_pos.le, le_rfl⟩]
    exact right_mem_affineSegment ℝ _ _
  cases vertical
  · refine ⟨hfirst, ?_⟩
    change (B.chordSupportingLine s).linear (B.planarCoordinates s (0, B.scale) -ᵥ
      B.planarCoordinates s (B.scale, 0)) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, hfirst, hsecond, sub_self]
  · refine ⟨hsecond, ?_⟩
    change (B.chordSupportingLine s).linear (B.planarCoordinates s (B.scale, 0) -ᵥ
      B.planarCoordinates s (0, B.scale)) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, hfirst, hsecond, sub_self]

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in

theorem first_attachment_cut_eq_smul_cap_line (p : T.decomposition.IncidentEdgeIndex) :
    ∃ r : ℝ, r ≠ 0 ∧ (T.bands p (T.graphs p).firstPiece).ambientEndpointCut false =
      r • (T.caps (T.decomposition.edgeEndpoint p.1.2 false)).chordSupportingLine
        (T.leftCap p).sector := by
  let B := T.bands p (T.graphs p).firstPiece
  let E := T.leftCap p
  have hc := (T.caps (T.decomposition.edgeEndpoint p.1.2 false)).chordSupportingLine_endpoint_direction
    E.sector (decide (E.radialEdge = 1))
  rw [E.chord_base, ← E.direction_eq] at hc
  have hb := B.ambientEndpointCut_first_base ((T.graphs p).cut_lt (T.graphs p).firstPiece).le
  have hd := B.ambientEndpointCut_direction false
  simp only [Prod.eta, Bool.false_eq_true, ↓reduceIte, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).firstPiece_castSucc,
    (T.graphs p).cut_first, (T.chains p).first] at hb hd
  exact affine_functionals_eq_smul_of_common_line _ _
    ((T.caps _).chordSupportingLine_spec E.sector).1
    (B.ambientEndpointCut_surjective false) E.direction_ne_zero hc.1 hb hc.2 hd

omit [T2Space S] in

theorem first_upper_attachment_mem_region (p : T.decomposition.IncidentEdgeIndex) :
    (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
          T.length • (T.leftCap p).direction) ∈
      connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
        T.decomposition.radius)ᶜ p.1.1 := by
  let B := T.bands p (T.graphs p).firstPiece
  have h := T.band_positive_height_mem_region p (T.graphs p).firstPiece
    (t := 0) (z := B.faces.height 0) (by simp) (B.faces.height_pos (by simp)) le_rfl
  rw [B.height_zero, ((T.graphs p).piece (T.graphs p).firstPiece).strip_left_parameter
    ((T.chains p).graphCuts (T.graphs p).firstPiece)
    ((T.graphs p).cut_lt (T.graphs p).firstPiece).le B.left_parameter_mem] at h
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).firstPiece_castSucc,
    (T.graphs p).cut_first, (T.chains p).first,
    FiniteChartRegionDecomposition.edgeFromEndpoint, Bool.false_eq_true, ite_false] using h

theorem exists_first_attachment_core_sector (p : T.decomposition.IncidentEdgeIndex)
    (hr : T.length < 1) :
    let B := T.bands p (T.graphs p).firstPiece
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
          T.length • (T.leftCap p).direction ∧
      c.coord 1 = -B.ambientEndpointCut false ∧ c.coord 2 = B.ambientEndpointTop false ∧
      c 0 ∈ (T.refined.mesh p.1.1).toPlaneComplex.support ∧
      (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  let B := T.bands p (T.graphs p).firstPiece
  obtain ⟨c, hc0, hc1, hc2⟩ := B.exists_ambient_first_complementary_coordinates
    ((T.graphs p).cut_lt (T.graphs p).firstPiece).le
  simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).firstPiece_castSucc,
    (T.graphs p).cut_first, (T.chains p).first] at hc0
  have hcollar : (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
        T.caps T.region p.1.1 =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
    rw [hc0]
    filter_upwards [T.coordinate_collar_first_upper_attachment_reflex_germ p hr] with z hz
    apply propext
    change (chartAt Plane (T.chart p.1.1 : S)).symm z ∈ _ ↔
      c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0
    rw [hc1, hc2]
    change _ ↔ -(B.ambientEndpointCut false z) ≤ 0 ∨ B.ambientEndpointTop false z ≤ 0
    simpa only [neg_nonpos] using hz
  have hg := T.core_complement_germ_of_mem_region p.1.1 (c 0)
    (hc0.symm ▸ (T.leftCap p).attachment_mem_chart_target ⟨T.length_pos.le, hr.le⟩)
    (hc0.symm ▸ T.first_upper_attachment_mem_region p)
  have hi := support_eventuallyEq_interior hcollar
  have hlocal : (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
    have hh : (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
        (interior {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0})ᶜ := by
      filter_upwards [hg, hi] with z hz hiz
      change ((T.refined.mesh p.1.1).toPlaneComplex.support z) = ¬interior _ z at hz ⊢
      rwa [hiz] at hz
    rwa [compl_interior_reflexSector] at hh
  refine ⟨c, hc0, hc1, hc2, ?_, hlocal⟩
  apply (propext_iff.mp hlocal.self_of_nhds).mpr
  change 0 ≤ c.coord 1 (c 0) ∧ 0 ≤ c.coord 2 (c 0)
  simp

set_option maxHeartbeats 600000 in

theorem exists_first_attachment_core_fan (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let B := T.bands p (T.graphs p).firstPiece
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
          T.length • (T.leftCap p).direction ∧
      c.coord 1 = -B.ambientEndpointCut false ∧ c.coord 2 = B.ambientEndpointTop false ∧
      (∑ t : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨p.1.1, t⟩)))
          ((chartAt Plane (T.chart p.1.1 : S)).symm (c 0))) =
        g.cornerAngle ((chartAt Plane (T.chart p.1.1 : S)).symm (c 0))
          ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart p.1.1 : S)).symm (c 0)) (c 1 - c 0))
          ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart p.1.1 : S)).symm (c 0)) (c 2 - c 0)) := by
  let B := T.bands p (T.graphs p).firstPiece
  obtain ⟨c, hc0, hc1, hc2, hq, hlocal⟩ := T.exists_first_attachment_core_sector p hr
  refine ⟨c, hc0, hc1, hc2, T.core_contribution_at_convex_sector g p.1.1 c ?_ ?_ hq hlocal⟩
  · obtain ⟨r, hr, he⟩ := T.first_attachment_cut_eq_smul_cap_line p
    refine ⟨(T.caps (T.decomposition.edgeEndpoint p.1.2 false)).chordSupportingLine
      (T.leftCap p).sector, ?_, -r, neg_ne_zero.mpr hr, ?_⟩
    · apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
      exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region
        (T.leftCap p).sector_region
    · rw [hc1, he, neg_smul]
  · obtain ⟨r, hr, he⟩ := B.ambientTopFunctional_eq_smul_topSupportingLine B.faces.firstCell
    refine ⟨B.topSupportingLine B.faces.firstCell, ?_, r, hr, ?_⟩
    · exact T.decomposition.band_line_mem_fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region p (T.graphs p).firstPiece _
        (by
          change B.topSupportingLine B.faces.firstCell ∈ B.coreContactLines
          simp [FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces.coreContactLines,
            List.mem_ofFn])
    · rw [hc2]
      exact he

omit [T2Space S] in

theorem last_attachment_cut_eq_smul_cap_line (p : T.decomposition.IncidentEdgeIndex) :
    ∃ r : ℝ, r ≠ 0 ∧ (T.bands p (T.graphs p).lastPiece).ambientEndpointCut true =
      r • (T.caps (T.decomposition.edgeEndpoint p.1.2 true)).chordSupportingLine
        (T.rightCap p).sector := by
  let B := T.bands p (T.graphs p).lastPiece
  let E := T.rightCap p
  have hc := (T.caps (T.decomposition.edgeEndpoint p.1.2 true)).chordSupportingLine_endpoint_direction
    E.sector (decide (E.radialEdge = 1))
  rw [E.chord_base, ← E.direction_eq] at hc
  have hb := B.ambientEndpointCut_last_base ((T.graphs p).cut_lt (T.graphs p).lastPiece).le
  have hd := B.ambientEndpointCut_direction true
  simp only [Prod.eta, ↓reduceIte, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).lastPiece_succ,
    (T.graphs p).cut_last, (T.chains p).last] at hb hd
  exact affine_functionals_eq_smul_of_common_line _ _
    ((T.caps _).chordSupportingLine_spec E.sector).1
    (B.ambientEndpointCut_surjective true) E.direction_ne_zero hc.1 hb hc.2 hd

omit [T2Space S] in

theorem last_upper_attachment_mem_region (p : T.decomposition.IncidentEdgeIndex) :
    (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
          T.length • (T.rightCap p).direction) ∈
      connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
        T.decomposition.radius)ᶜ p.1.1 := by
  let B := T.bands p (T.graphs p).lastPiece
  have h := T.band_positive_height_mem_region p (T.graphs p).lastPiece
    (t := 1) (z := B.faces.height 1) (by simp) (B.faces.height_pos (by simp)) le_rfl
  rw [B.height_one, ((T.graphs p).piece (T.graphs p).lastPiece).strip_right_parameter
    ((T.chains p).graphCuts (T.graphs p).lastPiece)
    ((T.graphs p).cut_lt (T.graphs p).lastPiece).le B.right_parameter_mem] at h
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).lastPiece_succ,
    (T.graphs p).cut_last, (T.chains p).last,
    FiniteChartRegionDecomposition.edgeFromEndpoint, ite_true] using h

theorem exists_last_attachment_core_sector (p : T.decomposition.IncidentEdgeIndex)
    (hr : T.length < 1) :
    let B := T.bands p (T.graphs p).lastPiece
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
          T.length • (T.rightCap p).direction ∧
      c.coord 1 = -B.ambientEndpointCut true ∧ c.coord 2 = B.ambientEndpointTop true ∧
      c 0 ∈ (T.refined.mesh p.1.1).toPlaneComplex.support ∧
      (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
        {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  let B := T.bands p (T.graphs p).lastPiece
  obtain ⟨c, hc0, hc1, hc2⟩ := B.exists_ambient_last_complementary_coordinates
    ((T.graphs p).cut_lt (T.graphs p).lastPiece).le
  simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).lastPiece_succ,
    (T.graphs p).cut_last, (T.chains p).last] at hc0
  have hcollar : (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
        T.caps T.region p.1.1 =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
    rw [hc0]
    filter_upwards [T.coordinate_collar_last_upper_attachment_reflex_germ p hr] with z hz
    apply propext
    change (chartAt Plane (T.chart p.1.1 : S)).symm z ∈ _ ↔
      c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0
    rw [hc1, hc2]
    change _ ↔ -(B.ambientEndpointCut true z) ≤ 0 ∨ B.ambientEndpointTop true z ≤ 0
    simpa only [neg_nonpos] using hz
  have hg := T.core_complement_germ_of_mem_region p.1.1 (c 0)
    (hc0.symm ▸ (T.rightCap p).attachment_mem_chart_target ⟨T.length_pos.le, hr.le⟩)
    (hc0.symm ▸ T.last_upper_attachment_mem_region p)
  have hi := support_eventuallyEq_interior hcollar
  have hlocal : (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
    have hh : (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
        (interior {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0})ᶜ := by
      filter_upwards [hg, hi] with z hz hiz
      change ((T.refined.mesh p.1.1).toPlaneComplex.support z) = ¬interior _ z at hz ⊢
      rwa [hiz] at hz
    rwa [compl_interior_reflexSector] at hh
  refine ⟨c, hc0, hc1, hc2, ?_, hlocal⟩
  apply (propext_iff.mp hlocal.self_of_nhds).mpr
  change 0 ≤ c.coord 1 (c 0) ∧ 0 ≤ c.coord 2 (c 0)
  simp

set_option maxHeartbeats 600000 in

theorem exists_last_attachment_core_fan (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let B := T.bands p (T.graphs p).lastPiece
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
          T.length • (T.rightCap p).direction ∧
      c.coord 1 = -B.ambientEndpointCut true ∧ c.coord 2 = B.ambientEndpointTop true ∧
      (∑ t : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨p.1.1, t⟩)))
          ((chartAt Plane (T.chart p.1.1 : S)).symm (c 0))) =
        g.cornerAngle ((chartAt Plane (T.chart p.1.1 : S)).symm (c 0))
          ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart p.1.1 : S)).symm (c 0)) (c 1 - c 0))
          ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart p.1.1 : S)).symm (c 0)) (c 2 - c 0)) := by
  let B := T.bands p (T.graphs p).lastPiece
  obtain ⟨c, hc0, hc1, hc2, hq, hlocal⟩ := T.exists_last_attachment_core_sector p hr
  refine ⟨c, hc0, hc1, hc2, T.core_contribution_at_convex_sector g p.1.1 c ?_ ?_ hq hlocal⟩
  · obtain ⟨r, hr, he⟩ := T.last_attachment_cut_eq_smul_cap_line p
    refine ⟨(T.caps (T.decomposition.edgeEndpoint p.1.2 true)).chordSupportingLine
      (T.rightCap p).sector, ?_, -r, neg_ne_zero.mpr hr, ?_⟩
    · apply T.decomposition.cap_line_mem_fittedCoreRefinementLines
      exact T.decomposition.chordSupportingLine_mem_capCoreContactLines T.caps T.region
        (T.rightCap p).sector_region
    · rw [hc1, he, neg_smul]
  · obtain ⟨r, hr, he⟩ := B.ambientTopFunctional_eq_smul_topSupportingLine B.faces.lastCell
    refine ⟨B.topSupportingLine B.faces.lastCell, ?_, r, hr, ?_⟩
    · exact T.decomposition.band_line_mem_fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region p (T.graphs p).lastPiece _
        (by
          change B.topSupportingLine B.faces.lastCell ∈ B.coreContactLines
          simp [FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces.coreContactLines,
            List.mem_ofFn])
    · rw [hc2]
      exact he

end RetainedCoordinateTriangulation

end PoincareConjecture.Topology.Surface
