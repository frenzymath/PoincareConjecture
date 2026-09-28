import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipSectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipComplements
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterStrictSigns
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterComplementAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem vertex_fan_at_independent_first_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true) - z] : Fin 2 → Plane)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis
      ((T.caps p).firstOuterTip i) = 2 * Real.pi := by
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_affineBasis_of_independent_chord_vectors _ _ _ hind
  have hchart (j : Bool) : (T.chart (T.region p (i, j)) : S) = (T.chart R : S) := by
    rw [hregion (i, j) (((T.caps p).firstOuterTip_mem_carrier_iff i (i, j)).mpr rfl)]
  have hp : c 0 = chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip i) := by
    rw [hc0, ← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have hpoint : (chartAt Plane (T.chart R : S)).symm (c 0) = (T.caps p).firstOuterTip i :=
    (congrArg (chartAt Plane (T.chart R : S)).symm hc0).trans hq
  have hc : ∃ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier :=
    ⟨(i, true), ((T.caps p).firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl⟩
  have hnh := T.cap_union_core_union_mem_nhds p R hc hregion hband
    (T.refined.in_region R ⟨z, hz, hq⟩)
  rw [T.vertex_contribution_eq_cap_union_add_core g p R (mem_interior_iff_mem_nhds.mpr hnh)]
  let μ : S → ℝ := fun q => ∑ t : (T.refined.mesh R).Triangle,
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
      (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)
  let α : S → ℝ := fun q => g.cornerAngle q (L (c 1 - c 0)) (L (c 2 - c 0))
  have hcore : μ ((T.caps p).firstOuterTip i) =
      ∑ j : Bool, g.cornerAngle ((T.caps p).firstOuterTip i)
        ((T.caps p).firstOuterSpoke i) ((T.caps p).firstOuterChord i j) := by
    rcases T.first_outer_core_sector_fan g p R i hz hq hregion hband c hc0 hc1 hc2 with
      ⟨hs, hm⟩ | ⟨hs, hm⟩
    · have hcap := T.cap_union_reflex_germ_of_core_convex_germ p R c
        (hc0.symm ▸ hz) (hpoint.symm ▸ hc)
        (fun s hs => hregion s (hpoint ▸ hs)) (fun a => hpoint.symm ▸ hband a) hs
      obtain ⟨h1, h2⟩ := (T.caps p).firstOuterChartSpoke_pos_of_reflex_cap_germ
        i (T.chart R : S) hchart c hp hc1 hc2 hcap
      have ha := (T.caps p).first_outer_angles_of_positive_spoke g i (T.chart R : S)
        hchart c hp hc1 hc2 h1 h2
      exact (congrArg μ hpoint).symm.trans (hm.trans ((congrArg α hpoint).trans ha.symm))
    · have hcap := T.cap_union_convex_germ_of_core_reflex_germ p R c
        (hc0.symm ▸ hz) (hpoint.symm ▸ hc)
        (fun s hs => hregion s (hpoint ▸ hs)) (fun a => hpoint.symm ▸ hband a) hs
      obtain ⟨h1, h2⟩ := (T.caps p).firstOuterChartSpoke_neg_of_convex_cap_germ
        i (T.chart R : S) hchart c hp hc1 hc2 hcap
      have ha := (T.caps p).first_outer_angles_of_negative_spoke g i (T.chart R : S)
        hchart c hp hc1 hc2 h1 h2
      exact (congrArg μ hpoint).symm.trans (hm.trans
        ((congrArg (fun q => 2 * Real.pi - α q) hpoint).trans ha.symm))
  change _ + μ ((T.caps p).firstOuterTip i) = _
  rw [hcore]
  have heq (s : Bool × Bool) : T.refinement.mesh (.inl (p, s)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, s))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, s))).mesh_eq_refineByLines
  simp_rw [heq]
  rw [Fintype.sum_prod_type]
  exact (T.caps p).sum_refined_first_outer_fan g i
    (fun s => (T.refinement.subdivision (.inl (p, s))).refinement_lines)

theorem vertex_fan_at_independent_second_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices)
    (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier)
    (hind : LinearIndependent ℝ
      (![chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false) - z,
        chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true) - z] : Fin 2 → Plane)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis
      ((T.caps p).secondOuterTip i) = 2 * Real.pi := by
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_affineBasis_of_independent_chord_vectors _ _ _ hind
  have hchart (j : Bool) : (T.chart (T.region p (j, i)) : S) = (T.chart R : S) := by
    rw [hregion (j, i) (((T.caps p).secondOuterTip_mem_carrier_iff i (j, i)).mpr rfl)]
  have hp : c 0 = chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip i) := by
    rw [hc0, ← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  have hpoint : (chartAt Plane (T.chart R : S)).symm (c 0) = (T.caps p).secondOuterTip i :=
    (congrArg (chartAt Plane (T.chart R : S)).symm hc0).trans hq
  have hc : ∃ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier :=
    ⟨(true, i), ((T.caps p).secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl⟩
  have hnh := T.cap_union_core_union_mem_nhds p R hc hregion hband
    (T.refined.in_region R ⟨z, hz, hq⟩)
  rw [T.vertex_contribution_eq_cap_union_add_core g p R (mem_interior_iff_mem_nhds.mpr hnh)]
  let μ : S → ℝ := fun q => ∑ t : (T.refined.mesh R).Triangle,
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
      (T.refinement.mesh (.inr (.inr ⟨R, t⟩))) q
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (T.chart R : S)).symm (c 0)
  let α : S → ℝ := fun q => g.cornerAngle q (L (c 1 - c 0)) (L (c 2 - c 0))
  have hcore : μ ((T.caps p).secondOuterTip i) =
      ∑ j : Bool, g.cornerAngle ((T.caps p).secondOuterTip i)
        ((T.caps p).secondOuterSpoke i) ((T.caps p).secondOuterChord i j) := by
    rcases T.second_outer_core_sector_fan g p R i hz hq hregion hband c hc0 hc1 hc2 with
      ⟨hs, hm⟩ | ⟨hs, hm⟩
    · have hcap := T.cap_union_reflex_germ_of_core_convex_germ p R c
        (hc0.symm ▸ hz) (hpoint.symm ▸ hc)
        (fun s hs => hregion s (hpoint ▸ hs)) (fun a => hpoint.symm ▸ hband a) hs
      obtain ⟨h1, h2⟩ := (T.caps p).secondOuterChartSpoke_pos_of_reflex_cap_germ
        i (T.chart R : S) hchart c hp hc1 hc2 hcap
      have ha := (T.caps p).second_outer_angles_of_positive_spoke g i (T.chart R : S)
        hchart c hp hc1 hc2 h1 h2
      exact (congrArg μ hpoint).symm.trans (hm.trans ((congrArg α hpoint).trans ha.symm))
    · have hcap := T.cap_union_convex_germ_of_core_reflex_germ p R c
        (hc0.symm ▸ hz) (hpoint.symm ▸ hc)
        (fun s hs => hregion s (hpoint ▸ hs)) (fun a => hpoint.symm ▸ hband a) hs
      obtain ⟨h1, h2⟩ := (T.caps p).secondOuterChartSpoke_neg_of_convex_cap_germ
        i (T.chart R : S) hchart c hp hc1 hc2 hcap
      have ha := (T.caps p).second_outer_angles_of_negative_spoke g i (T.chart R : S)
        hchart c hp hc1 hc2 h1 h2
      exact (congrArg μ hpoint).symm.trans (hm.trans
        ((congrArg (fun q => 2 * Real.pi - α q) hpoint).trans ha.symm))
  change _ + μ ((T.caps p).secondOuterTip i) = _
  rw [hcore]
  have heq (s : Bool × Bool) : T.refinement.mesh (.inl (p, s)) =
      (TriangleMesh.single (rightTriangleBasis (T.caps p).scale_pos)
        (rightTriangleBasis (T.caps p).scale_pos).ind).refineByLines
          (T.refinement.subdivision (.inl (p, s))).refinement_lines :=
    (T.refinement.subdivision (.inl (p, s))).mesh_eq_refineByLines
  simp_rw [heq]
  rw [Fintype.sum_prod_type]
  exact (T.caps p).sum_refined_second_outer_fan g i
    (fun s => (T.refinement.subdivision (.inl (p, s))).refinement_lines)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
