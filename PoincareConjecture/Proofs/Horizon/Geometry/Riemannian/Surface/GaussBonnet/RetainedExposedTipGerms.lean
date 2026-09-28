import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapClassification
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterBoundary

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

theorem collar_germ_eq_cap_union_of_not_mem_bands
    (p : T.decomposition.vertices) (R : T.decomposition.regions) {q : S}
    (hq : ∃ s, q ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, q ∈ ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      q ∉ (T.bands a.1 a.2).faces.carrier) :
    T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region R =ᶠ[𝓝 q] ⋃ s, ((T.caps p).face s).carrier := by
  have hc : ∀ᶠ z in 𝓝 q, ∀ a : T.decomposition.vertices × (Bool × Bool),
      q ∉ ((T.caps a.1).face a.2).carrier → z ∉ ((T.caps a.1).face a.2).carrier := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : q ∈ ((T.caps a.1).face a.2).carrier
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h ha))
    · filter_upwards [((T.caps a.1).face a.2).isClosed_carrier.isOpen_compl.mem_nhds ha]
        with z hz
      exact fun _ => hz
  have hb : ∀ᶠ z in 𝓝 q,
      ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
        z ∉ (T.bands a.1 a.2).faces.carrier := by
    apply Filter.eventually_all.mpr
    intro a
    exact (T.bands a.1 a.2).faces.isClosed_carrier.isOpen_compl.mem_nhds (hband a)
  have hp (v : T.decomposition.vertices) (s : Bool × Bool)
      (hv : q ∈ ((T.caps v).face s).carrier) : v = p := by
    by_contra hne
    obtain ⟨j, hj⟩ := hq
    exact disjoint_left.mp (T.caps_disjoint_of_vertices_ne v p hne s j) hv hj
  filter_upwards [hc, hb] with z hzc hzb
  apply propext
  constructor
  · rintro (hc | hb)
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hc
      have hqa : q ∈ ((T.caps a.1.1).face a.1.2).carrier :=
        by_contra (fun hn => hzc a.1 hn ha)
      have he := congrArg (fun v : T.decomposition.vertices =>
        ((T.caps v).face a.1.2).carrier) (hp a.1.1 a.1.2 hqa)
      exact mem_iUnion.mpr ⟨a.1.2, he ▸ ha⟩
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hb
      exact False.elim (hzb a.1 ha)
  · intro h
    obtain ⟨s, hs⟩ := mem_iUnion.mp h
    have hqs : q ∈ ((T.caps p).face s).carrier :=
      by_contra (fun hn => hzc (p, s) hn hs)
    exact Or.inl (mem_iUnion.mpr ⟨⟨(p, s), hregion s hqs⟩, hs⟩)

theorem cap_union_core_union_mem_nhds
    (p : T.decomposition.vertices) (R : T.decomposition.regions) {q : S}
    (hq : ∃ s, q ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, q ∈ ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      q ∉ (T.bands a.1 a.2).faces.carrier)
    (hR : q ∈ connectedComponentIn
      (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R) :
    (⋃ s, ((T.caps p).face s).carrier) ∪
      ((chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support) ∈ 𝓝 q := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  have hopen : IsOpen (connectedComponentIn
      (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R) :=
    (isClosed_chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius).isOpen_compl.connectedComponentIn
  filter_upwards [hopen.mem_nhds hR,
    T.collar_germ_eq_cap_union_of_not_mem_bands p R hq hregion hband] with z hz hzc
  have hcover := T.refined.cover R ▸ subset_closure hz
  rcases hcover with h | h
  · exact Or.inl ((propext_iff.mp hzc).mp h)
  · exact Or.inr h

theorem vertex_contribution_eq_cap_union_add_core
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (R : T.decomposition.regions)
    {q : S} (hq : q ∈ interior ((⋃ s, ((T.caps p).face s).carrier) ∪
      (chartAt Plane (T.chart R : S)).symm '' (T.refined.mesh R).toPlaneComplex.support)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      (∑ s : Bool × Bool, meshVertexAngleContribution g ((T.caps p).coordinates s)
        (T.refinement.mesh (.inl (p, s))) q) +
      ∑ u : (T.refined.mesh R).Triangle,
        meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm
          (T.refinement.mesh (.inr (.inr ⟨R, u⟩))) q := by
  rw [T.vertex_contribution_eq_parent_sum]
  apply mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh T.parentCoordinates
    T.refinement.face (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.intersection_frontier
    (fun s : Bool × Bool => (.inl (p, s) : T.Parent))
    (fun u : (T.refined.mesh R).Triangle => (.inr (.inr ⟨R, u⟩) : T.Parent))
  · intro a b h
    simpa using h
  · intro a b h
    simpa using h
  · intro a b h
    cases h
  · rwa [T.cap_parent_support_union p, T.core_parent_support_union R]

theorem core_complement_cap_union_germ
    (p : T.decomposition.vertices) (R : T.decomposition.regions) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : ∃ s, (chartAt Plane (T.chart R : S)).symm z ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, (chartAt Plane (T.chart R : S)).symm z ∈
      ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (chartAt Plane (T.chart R : S)).symm z ∉ (T.bands a.1 a.2).faces.carrier) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z]
      (interior ((chartAt Plane (T.chart R : S)).symm ⁻¹'
        (⋃ s, ((T.caps p).face s).carrier)))ᶜ := by
  have hc := (T.collar_germ_eq_cap_union_of_not_mem_bands p R hq hregion hband).comp_tendsto
    ((chartAt Plane (T.chart R : S)).symm.continuousAt (T.refined.source R hz))
  change (chartAt Plane (T.chart R : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands T.caps T.region R
    =ᶠ[𝓝 z] (chartAt Plane (T.chart R : S)).symm ⁻¹'
      (⋃ s, ((T.caps p).face s).carrier) at hc
  have hi := support_eventuallyEq_interior hc
  have hk := T.core_complement_germ R z hz
  filter_upwards [hk, hi] with w hkw hiw
  apply propext
  have h := propext_iff.mp hkw
  change _ ↔ ¬ interior _ w at h ⊢
  rwa [hiw] at h

theorem core_frontier_cap_union_germ
    (p : T.decomposition.vertices) (R : T.decomposition.regions) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : ∃ s, (chartAt Plane (T.chart R : S)).symm z ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, (chartAt Plane (T.chart R : S)).symm z ∈
      ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (chartAt Plane (T.chart R : S)).symm z ∉ (T.bands a.1 a.2).faces.carrier) :
    frontier (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z]
      frontier ((chartAt Plane (T.chart R : S)).symm ⁻¹'
        (⋃ s, ((T.caps p).face s).carrier)) := by
  exact (support_eventuallyEq_frontier
    (T.core_complement_cap_union_germ p R hz hq hregion hband)).trans
      (frontier_compl_interior_preimage_eventuallyEq
        (chartAt Plane (T.chart R : S)).symm _
        (isClosed_iUnion_of_finite (fun s => ((T.caps p).face s).isClosed_carrier))
        ((T.caps p).closure_interior_union) (T.refined.source R hz))

theorem core_frontier_first_outer_rays
    (p : T.decomposition.vertices) (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).firstOuterTip i)
    (hregion : ∀ s, (T.caps p).firstOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).firstOuterTip i ∉ (T.bands a.1 a.2).faces.carrier) :
    frontier (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z]
      ⋃ j : Bool, (fun t : ℝ => z + t •
        (chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip j) - z)) '' Ici (0 : ℝ) := by
  have hcap := ((T.caps p).firstOuterTip_mem_carrier_iff i (i, true)).mpr rfl
  have hc := T.core_frontier_cap_union_germ p R hz
    ⟨(i, true), hq.symm ▸ hcap⟩
    (fun s hs => hregion s (hq ▸ hs)) (fun a => hq.symm ▸ hband a)
  have hchart (j : Bool) :
      (T.chart (T.region p (i, j)) : S) = (T.chart R : S) := by
    rw [hregion (i, j) (((T.caps p).firstOuterTip_mem_carrier_iff i (i, j)).mpr rfl)]
  have hr := (T.caps p).chart_frontier_union_eventuallyEq_first_rays i
    (T.chart R : S) hchart
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip i) = z := by
    rw [← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  exact hc.trans (by simpa only [hp] using hr)

theorem core_frontier_second_outer_rays
    (p : T.decomposition.vertices) (R : T.decomposition.regions) (i : Bool) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : (chartAt Plane (T.chart R : S)).symm z = (T.caps p).secondOuterTip i)
    (hregion : ∀ s, (T.caps p).secondOuterTip i ∈ ((T.caps p).face s).carrier →
      T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (T.caps p).secondOuterTip i ∉ (T.bands a.1 a.2).faces.carrier) :
    frontier (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 z]
      ⋃ j : Bool, (fun t : ℝ => z + t •
        (chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip j) - z)) '' Ici (0 : ℝ) := by
  have hcap := ((T.caps p).secondOuterTip_mem_carrier_iff i (true, i)).mpr rfl
  have hc := T.core_frontier_cap_union_germ p R hz
    ⟨(true, i), hq.symm ▸ hcap⟩
    (fun s hs => hregion s (hq ▸ hs)) (fun a => hq.symm ▸ hband a)
  have hchart (j : Bool) :
      (T.chart (T.region p (j, i)) : S) = (T.chart R : S) := by
    rw [hregion (j, i) (((T.caps p).secondOuterTip_mem_carrier_iff i (j, i)).mpr rfl)]
  have hr := (T.caps p).chart_frontier_union_eventuallyEq_second_rays i
    (T.chart R : S) hchart
  have hp : chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip i) = z := by
    rw [← hq, (chartAt Plane (T.chart R : S)).right_inv (T.refined.source R hz)]
  exact hc.trans (by simpa only [hp] using hr)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
