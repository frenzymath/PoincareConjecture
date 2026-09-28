import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipLines
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterMetricFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem canonical_vertex_fan_at_collinear_first_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hzq : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (htip : q.1 = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true) - z] : Fin 2 → Plane)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hchart (j : Bool) : (T.chart (T.region p (i, j)) : S) = (T.chart R : S) := by
    rw [hregion (i, j) (((T.caps p).firstOuterTip_mem_carrier_iff i (i, j)).mpr rfl)]
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip i) = z := by
    rw [← htip, ← hzq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have hcap := (T.caps p).sum_refined_first_outer_fan_eq_pi_of_not_independent g i
    (T.chart R : S) hchart (by simpa only [hp] using hind)
    (fun s => (T.refinement.subdivision (.inl (p, s))).refinement_lines)
  have heq (s : Bool × Bool) : T.refinement.mesh (.inl (p, s)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, s))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, s))).mesh_eq_refineByLines
  have hc : (∑ s : Bool × Bool, meshVertexAngleContribution g ((T.caps p).coordinates s)
      (T.refinement.mesh (.inl (p, s))) q.1) = Real.pi := by
    rw [htip]
    simp_rw [heq]
    rw [Fintype.sum_prod_type]
    exact hcap
  have hnh := T.cap_union_core_union_mem_nhds p R
    ⟨(i, true), ((T.caps p).firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl⟩
    hregion hband (T.refined.in_region R ⟨z, hz, hzq.trans htip⟩)
  have hint : q.1 ∈ interior ((⋃ s, ((T.caps p).face s).carrier) ∪
      (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support) := by
    rw [htip]
    exact mem_interior_iff_mem_nhds.mpr hnh
  rw [T.vertex_contribution_eq_cap_union_add_core g p R hint, hc,
    T.core_contribution_at_collinear_first_outer_tip g p R i q hzq hz htip hregion hband hind]
  ring

theorem canonical_vertex_fan_at_collinear_second_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    {z : Plane} (hzq : (chartAt Plane (T.chart R : S)).symm z = q.1)
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (htip : q.1 = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : ¬ LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true) - z] : Fin 2 → Plane)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hchart (j : Bool) : (T.chart (T.region p (j, i)) : S) = (T.chart R : S) := by
    rw [hregion (j, i) (((T.caps p).secondOuterTip_mem_carrier_iff i (j, i)).mpr rfl)]
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip i) = z := by
    rw [← htip, ← hzq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have hcap := (T.caps p).sum_refined_second_outer_fan_eq_pi_of_not_independent g i
    (T.chart R : S) hchart (by simpa only [hp] using hind)
    (fun s => (T.refinement.subdivision (.inl (p, s))).refinement_lines)
  have heq (s : Bool × Bool) : T.refinement.mesh (.inl (p, s)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, s))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, s))).mesh_eq_refineByLines
  have hc : (∑ s : Bool × Bool, meshVertexAngleContribution g ((T.caps p).coordinates s)
      (T.refinement.mesh (.inl (p, s))) q.1) = Real.pi := by
    rw [htip]
    simp_rw [heq]
    rw [Fintype.sum_prod_type]
    exact hcap
  have hnh := T.cap_union_core_union_mem_nhds p R
    ⟨(true, i), ((T.caps p).secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl⟩
    hregion hband (T.refined.in_region R ⟨z, hz, hzq.trans htip⟩)
  have hint : q.1 ∈ interior ((⋃ s, ((T.caps p).face s).carrier) ∪
      (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support) := by
    rw [htip]
    exact mem_interior_iff_mem_nhds.mpr hnh
  rw [T.vertex_contribution_eq_cap_union_add_core g p R hint, hc,
    T.core_contribution_at_collinear_second_outer_tip g p R i q hzq hz htip hregion hband hind]
  ring

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
