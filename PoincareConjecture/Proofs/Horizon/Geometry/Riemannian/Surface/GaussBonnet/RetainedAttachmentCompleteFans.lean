import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAttachmentFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapCoreFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandCoreFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.EndpointAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in

theorem cap_band_core_union_mem_nhds_of_collar_germ
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (v : T.decomposition.vertices) (s : Bool × Bool) {q : S}
    (hregion : q ∈ connectedComponentIn
      (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ p.1.1)
    (hcollar : T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains
      T.bands T.caps T.region p.1.1 =ᶠ[𝓝 q]
        (((T.caps v).face s).carrier ∪ (T.bands p i).faces.carrier : Set S)) :
    (((T.caps v).face s).carrier ∪ (T.bands p i).faces.carrier) ∪
      (chartAt Plane (T.chart p.1.1 : S)).symm ''
        (T.refined.mesh p.1.1).toPlaneComplex.support ∈ 𝓝 q := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  have hU : IsOpen (connectedComponentIn (chartDiskBoundaryUnion T.decomposition.centers
    T.decomposition.radius)ᶜ p.1.1) := (isClosed_chartDiskBoundaryUnion T.decomposition.centers
      T.decomposition.radius).isOpen_compl.connectedComponentIn
  filter_upwards [hU.mem_nhds hregion, hcollar] with z hz hzc
  have hc := T.refined.cover p.1.1 ▸ subset_closure hz
  rcases hc with h | h
  · exact Or.inl ((propext_iff.mp hzc).mp h)
  · exact Or.inr h

set_option maxHeartbeats 800000 in

theorem vertex_contribution_eq_cap_add_band_add_core
    (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (v : T.decomposition.vertices) (s : Bool × Bool) {q : S}
    (hq : q ∈ interior ((((T.caps v).face s).carrier ∪ (T.bands p i).faces.carrier) ∪
      (chartAt Plane (T.chart p.1.1 : S)).symm ''
        (T.refined.mesh p.1.1).toPlaneComplex.support)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      meshVertexAngleContribution g ((T.caps v).coordinates s)
        (T.refinement.mesh (.inl (v, s))) q +
      ((∑ a : Fin (T.bands p i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates a)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))) q) +
        ∑ u : (T.refined.mesh p.1.1).Triangle,
          meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
            (T.refinement.mesh (.inr (.inr ⟨p.1.1, u⟩))) q) := by
  rw [T.vertex_contribution_eq_parent_sum]
  let right : (Fin (T.bands p i).faces.interface.count × Bool) ⊕
      (T.refined.mesh p.1.1).Triangle → T.Parent :=
    Sum.elim (fun a => .inr (.inl ⟨⟨p, i⟩, a⟩)) (fun u => .inr (.inr ⟨p.1.1, u⟩))
  have hr : Function.Injective right := by
    intro a b h
    cases a <;> cases b
    · simpa only [right, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq,
        Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    · simp [right] at h
    · simp [right] at h
    · simpa only [right, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq,
        Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  have h := mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh
    T.parentCoordinates T.refinement.face (T.refinement.mesh_source T.parent_source)
    T.refinement.carrier_eq T.refinement.intersection_frontier
    (fun _ : Unit => (.inl (v, s) : T.Parent)) right
    (fun _ _ _ => Subsingleton.elim _ _) hr
    (by intro a b h; cases b <;> cases h) (q := q) ?_
  · simp only [Fintype.sum_unique] at h
    conv_rhs at h => rw [Fintype.sum_sum_type]
    exact h
  · simp only [iUnion_const, iUnion_sum, right, Sum.elim_inl, Sum.elim_inr]
    have hcap : T.parentCoordinates (.inl (v, s)) ''
        (T.refinement.mesh (.inl (v, s))).toPlaneComplex.support =
          ((T.caps v).face s).carrier := by
      rw [(T.refinement.subdivision (.inl (v, s))).support]
      exact ((T.caps v).carrier_eq s).symm
    have hunion := congrArg₂ (fun A B : Set S => A ∪ B) hcap
      (congrArg₂ (fun A B : Set S => A ∪ B)
        (T.band_parent_support_union p i) (T.core_parent_support_union p.1.1))
    rw [hunion, ← union_assoc]
    exact hq

set_option maxHeartbeats 800000 in

theorem first_attachment_band_core_contribution (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let q := (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
          T.length • (T.leftCap p).direction)
    (∑ a : Fin (T.bands p (T.graphs p).firstPiece).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p (T.graphs p).firstPiece).faces.faceCoordinates a)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, (T.graphs p).firstPiece⟩, a⟩))) q) +
      (∑ u : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨p.1.1, u⟩))) q) = Real.pi := by
  let B := T.bands p (T.graphs p).firstPiece
  obtain ⟨c, hc0, hc1, hc2, hcore⟩ := T.exists_first_attachment_core_fan g p hr
  have hvertex := B.chart_first_top_eq_physical ((T.graphs p).cut_lt (T.graphs p).firstPiece).le
  simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).firstPiece_castSucc,
    (T.graphs p).cut_first, (T.chains p).first] at hvertex
  have hc0' : c 0 = B.chartTopVertex 0 := hc0.trans hvertex.symm
  have hfan := B.first_actual_fan_add_complementary_angle g
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    ((T.graphs p).cut_lt (T.graphs p).firstPiece).le
    (fun a => T.refinement.mesh (.inr (.inl ⟨⟨p, (T.graphs p).firstPiece⟩, a⟩)))
    (fun a => (T.refinement.subdivision
      (.inr (.inl ⟨⟨p, (T.graphs p).firstPiece⟩, a⟩))).refinement_lines)
    (fun a => (T.refinement.subdivision
      (.inr (.inl ⟨⟨p, (T.graphs p).firstPiece⟩, a⟩))).mesh_eq_refineByLines) c hc0' hc1 hc2
  rw [← hcore] at hfan
  simpa only [hc0] using hfan

set_option maxHeartbeats 800000 in

theorem last_attachment_band_core_contribution (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1) :
    let q := (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
          T.length • (T.rightCap p).direction)
    (∑ a : Fin (T.bands p (T.graphs p).lastPiece).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p (T.graphs p).lastPiece).faces.faceCoordinates a)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, (T.graphs p).lastPiece⟩, a⟩))) q) +
      (∑ u : (T.refined.mesh p.1.1).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨p.1.1, u⟩))) q) = Real.pi := by
  let B := T.bands p (T.graphs p).lastPiece
  obtain ⟨c, hc0, hc1, hc2, hcore⟩ := T.exists_last_attachment_core_fan g p hr
  have hvertex := B.chart_last_top_eq_physical ((T.graphs p).cut_lt (T.graphs p).lastPiece).le
  simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs p).lastPiece_succ,
    (T.graphs p).cut_last, (T.chains p).last] at hvertex
  have hc0' : c 0 = B.chartTopVertex (Fin.last B.faces.interface.count) := hc0.trans hvertex.symm
  have hfan := B.last_actual_fan_add_complementary_angle g
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    (fun a => T.refinement.mesh (.inr (.inl ⟨⟨p, (T.graphs p).lastPiece⟩, a⟩)))
    (fun a => (T.refinement.subdivision
      (.inr (.inl ⟨⟨p, (T.graphs p).lastPiece⟩, a⟩))).refinement_lines)
    (fun a => (T.refinement.subdivision
      (.inr (.inl ⟨⟨p, (T.graphs p).lastPiece⟩, a⟩))).mesh_eq_refineByLines) c hc0' hc1 hc2
  rw [← hcore] at hfan
  simpa only [hc0] using hfan

set_option maxHeartbeats 800000 in

theorem canonical_vertex_fan_at_first_upper_attachment (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false)) +
          T.length • (T.leftCap p).direction) = q.1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hn := T.cap_band_core_union_mem_nhds_of_collar_germ p (T.graphs p).firstPiece
    (T.decomposition.edgeEndpoint p.1.2 false) (T.leftCap p).sector
    (T.first_upper_attachment_mem_region p) (T.collar_germ_at_first_upper_attachment p hr)
  rw [hq] at hn
  rw [T.vertex_contribution_eq_cap_add_band_add_core g p (T.graphs p).firstPiece
    (T.decomposition.edgeEndpoint p.1.2 false) (T.leftCap p).sector
    (mem_interior_iff_mem_nhds.mpr hn)]
  have ht : (if (T.leftCap p).radialEdge = 1 then 1 - T.length else T.length) ∈
      Ioo (0 : ℝ) 1 := by
    split_ifs <;> constructor <;> linarith [T.length_pos]
  have hchord : (((T.caps (T.decomposition.edgeEndpoint p.1.2 false)).face
      (T.leftCap p).sector).boundary 0).map
      (if (T.leftCap p).radialEdge = 1 then 1 - T.length else T.length) = q.1 := by
    rw [← (T.leftCap p).chord_map]
    exact hq
  rw [T.cap_contribution_at_open_chord_canonical_vertex g _ _ ht q hchord]
  have hhalf := T.first_attachment_band_core_contribution g p hr
  dsimp only at hhalf
  rw [hq] at hhalf
  rw [hhalf]
  ring

set_option maxHeartbeats 800000 in

theorem canonical_vertex_fan_at_last_upper_attachment (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (hr : T.length < 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : (chartAt Plane (T.chart p.1.1 : S)).symm
      (chartAt Plane (T.chart p.1.1 : S)
        (T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true)) +
          T.length • (T.rightCap p).direction) = q.1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hn := T.cap_band_core_union_mem_nhds_of_collar_germ p (T.graphs p).lastPiece
    (T.decomposition.edgeEndpoint p.1.2 true) (T.rightCap p).sector
    (T.last_upper_attachment_mem_region p) (T.collar_germ_at_last_upper_attachment p hr)
  rw [hq] at hn
  rw [T.vertex_contribution_eq_cap_add_band_add_core g p (T.graphs p).lastPiece
    (T.decomposition.edgeEndpoint p.1.2 true) (T.rightCap p).sector
    (mem_interior_iff_mem_nhds.mpr hn)]
  have ht : (if (T.rightCap p).radialEdge = 1 then 1 - T.length else T.length) ∈
      Ioo (0 : ℝ) 1 := by
    split_ifs <;> constructor <;> linarith [T.length_pos]
  have hchord : (((T.caps (T.decomposition.edgeEndpoint p.1.2 true)).face
      (T.rightCap p).sector).boundary 0).map
      (if (T.rightCap p).radialEdge = 1 then 1 - T.length else T.length) = q.1 := by
    rw [← (T.rightCap p).chord_map]
    exact hq
  rw [T.cap_contribution_at_open_chord_canonical_vertex g _ _ ht q hchord]
  have hhalf := T.last_attachment_band_core_contribution g p hr
  dsimp only at hhalf
  rw [hq] at hhalf
  rw [hhalf]
  ring

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
