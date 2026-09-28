import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedInteriorFans







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in


theorem not_mem_collar_of_not_mem_caps_bands {q : S}
    (hcap : ∀ p s, q ∉ ((T.caps p).face s).carrier)
    (hband : ∀ p i, q ∉ (T.bands p i).faces.carrier)
    (R : T.decomposition.regions) :
    q ∉ T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
      T.caps T.region R := by
  rintro (hc | hb)
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hc
    exact hcap a.1.1 a.1.2 ha
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hb
    exact hband a.1.1 a.1.2 ha



theorem exists_core_interior_of_not_mem_caps_bands (q : S)
    (hcap : ∀ p s, q ∉ ((T.caps p).face s).carrier)
    (hband : ∀ p i, q ∉ (T.bands p i).faces.carrier) :
    ∃ R : T.decomposition.regions, q ∈ (chartAt Plane (T.chart R : S)).symm ''
      interior (T.refined.mesh R).toPlaneComplex.support := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  have hcover : q ∈ ⋃ R ∈ T.decomposition.regions, closure (connectedComponentIn
      (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R) := by
    rw [T.decomposition.region_closure_cover]
    trivial
  obtain ⟨R, hR, hRq⟩ := mem_iUnion₂.mp hcover
  let r : T.decomposition.regions := ⟨R, hR⟩
  have hnot := T.not_mem_collar_of_not_mem_caps_bands hcap hband r
  rw [T.refined.cover r] at hRq
  have hcore := hRq.resolve_left hnot
  have hreg := T.refined.in_region r hcore
  have hopen : IsOpen (connectedComponentIn (chartDiskBoundaryUnion
      T.decomposition.centers T.decomposition.radius)ᶜ r) :=
    (isClosed_chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius).isOpen_compl.connectedComponentIn
  have hclosed : IsClosed (T.decomposition.fittedRegionCollar T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region r) := by
    apply IsClosed.union
    · exact isClosed_iUnion_of_finite fun a => ((T.caps a.1.1).face a.1.2).isClosed_carrier
    · exact isClosed_iUnion_of_finite fun a => (T.bands a.1.1 a.1.2).faces.isClosed_carrier
  have hint : q ∈ interior ((chartAt Plane (T.chart r : S)).symm ''
      (T.refined.mesh r).toPlaneComplex.support) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hopen.mem_nhds hreg, hclosed.isOpen_compl.mem_nhds hnot] with z hz hn
    exact ((T.refined.cover r) ▸ subset_closure hz).resolve_left hn
  refine ⟨r, ?_⟩
  rwa [interior_smooth_coordinate_image _ (T.refined.source r)] at hint

set_option maxHeartbeats 800000 in


theorem canonical_vertex_fan_of_not_mem_caps_bands (g : RiemannianMetric 2 S)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hcap : ∀ p s, q.1 ∉ ((T.caps p).face s).carrier)
    (hband : ∀ p i, q.1 ∉ (T.bands p i).faces.carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  obtain ⟨R, hR⟩ := T.exists_core_interior_of_not_mem_caps_bands q.1 hcap hband
  exact T.canonical_vertex_fan_in_core_interior g R q hR

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
