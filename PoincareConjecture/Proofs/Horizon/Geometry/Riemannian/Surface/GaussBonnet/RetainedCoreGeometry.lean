import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CoreSupportGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.RestrictionAncestry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Monochromatic








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



theorem core_complement_germ_of_mem_region (R : T.decomposition.regions) (q : Plane)
    (hqs : q ∈ (chartAt Plane (T.chart R : S)).target)
    (hq : (chartAt Plane (T.chart R : S)).symm q ∈ connectedComponentIn
      (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ R) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 q]
      (interior ((chartAt Plane (T.chart R : S)).symm ⁻¹'
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region R))ᶜ := by
  let : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  exact coordinate_core_support_eventuallyEq_compl_interior
    (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R) (T.refined.source R)
    (isClosed_chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius).isOpen_compl.connectedComponentIn
    (T.refined.cover R) (T.refined_core_frontier R)
    hqs hq



theorem core_complement_germ (R : T.decomposition.regions) (q : Plane)
    (hq : q ∈ (T.refined.mesh R).toPlaneComplex.support) :
    (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 q]
      (interior ((chartAt Plane (T.chart R : S)).symm ⁻¹'
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region R))ᶜ :=
  T.core_complement_germ_of_mem_region R q (T.refined.source R hq)
    (T.refined.in_region R (mem_image_of_mem _ hq))

omit [T2Space S] in



theorem core_mesh_straight_boundary_fan_of_scaled_contact (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l)
    (hlines : ∃ k ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R, ∃ a : ℝ, a ≠ 0 ∧ l = a • k)
    (u : (T.refined.mesh R).Triangle) (v : (T.refined.mesh R).Vertex) (hv : v ∈ u.1)
    (hzero : l ((T.refined.mesh R).position v) = 0)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 ((T.refined.mesh R).position v)]
      {z | 0 ≤ l z}) :
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
      ((chartAt Plane (T.chart R : S)).symm ((T.refined.mesh R).position v)) = Real.pi := by
  obtain ⟨b, first, P, hcore, hinside⟩ := T.core_ancestry R
  have hsource : (T.coreMeshes R).toPlaneComplex.support ⊆ (chartAt Plane (T.chart R : S)).target := by
    rw [← T.refined.support R]
    exact T.refined.source R
  have hmono : ((TriangleMesh.single b b.ind).refineByLines
      (first ++ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region R)).IsMonochromatic l := by
    obtain ⟨k, hk, a, _, rfl⟩ := hlines
    exact isMonochromatic_smul _ k
      ((TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem _
        (List.mem_append_right _ hk)) a
  have heq := T.refined.mesh_eq_refineByLines R
  rw [hcore] at heq hsource hinside
  revert u v
  rw [heq]
  intro u v hv hzero hlocal
  have hpos : ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines
      (T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs T.chains T.bands T.caps T.region R)).position v ∈
      (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support := by
    rw [← TriangleMesh.refineByLines_support _
      (T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs T.chains T.bands T.caps T.region R)]
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨u.1, u.2, subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩
  apply single_refineByLines_restrict_refineByLines_straight_boundary_fan_of_source g
    (chartAt Plane (T.chart R : S)).symm b first _ P l hl hmono
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) hsource u v hv
    (hinside hpos) hzero
  simpa only [TriangleMesh.refineByLines_support] using hlocal

omit [T2Space S] in


theorem core_mesh_straight_boundary_fan (g : RiemannianMetric 2 S)
    (R : T.decomposition.regions) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l)
    (hlines : l ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region R)
    (u : (T.refined.mesh R).Triangle) (v : (T.refined.mesh R).Vertex) (hv : v ∈ u.1)
    (hzero : l ((T.refined.mesh R).position v) = 0)
    (hlocal : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 ((T.refined.mesh R).position v)]
      {z | 0 ≤ l z}) :
    meshVertexAngleContribution g (chartAt Plane (T.chart R : S)).symm (T.refined.mesh R)
      ((chartAt Plane (T.chart R : S)).symm ((T.refined.mesh R).position v)) = Real.pi :=
  T.core_mesh_straight_boundary_fan_of_scaled_contact g R l hl
    ⟨l, hlines, 1, one_ne_zero, by simp⟩ u v hv hzero hlocal

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
