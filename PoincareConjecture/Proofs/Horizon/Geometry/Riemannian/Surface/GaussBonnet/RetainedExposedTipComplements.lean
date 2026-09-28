import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.RegularComplementGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem cap_union_complement_core_germ
    (p : T.decomposition.vertices) (R : T.decomposition.regions) {z : Plane}
    (hz : z ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : ∃ s, (chartAt Plane (T.chart R : S)).symm z ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, (chartAt Plane (T.chart R : S)).symm z ∈
      ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (chartAt Plane (T.chart R : S)).symm z ∉ (T.bands a.1 a.2).faces.carrier) :
    (chartAt Plane (T.chart R : S)).symm ⁻¹' (⋃ s, ((T.caps p).face s).carrier)
      =ᶠ[𝓝 z] (interior (T.refined.mesh R).toPlaneComplex.support)ᶜ := by
  apply regular_closed_complement_interior_germ
    (preimage_regular_closed_germ _ _ (T.caps p).closure_interior_union
      (T.refined.source R hz))
  exact T.core_complement_cap_union_germ p R hz hq hregion hband

theorem cap_union_reflex_germ_of_core_convex_germ
    (p : T.decomposition.vertices) (R : T.decomposition.regions)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hz : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : ∃ s, (chartAt Plane (T.chart R : S)).symm (c 0) ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, (chartAt Plane (T.chart R : S)).symm (c 0) ∈
      ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (chartAt Plane (T.chart R : S)).symm (c 0) ∉ (T.bands a.1 a.2).faces.carrier)
    (hcore : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (chartAt Plane (T.chart R : S)).symm ⁻¹' (⋃ s, ((T.caps p).face s).carrier)
      =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
  have hcap := T.cap_union_complement_core_germ p R hz hq hregion hband
  have hi := support_eventuallyEq_interior hcore
  rw [← compl_interior_convexSector c]
  filter_upwards [hcap, hi] with z hz hi
  exact hz.trans (congrArg Not hi)

theorem cap_union_convex_germ_of_core_reflex_germ
    (p : T.decomposition.vertices) (R : T.decomposition.regions)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hz : c 0 ∈ (T.refined.mesh R).toPlaneComplex.support)
    (hq : ∃ s, (chartAt Plane (T.chart R : S)).symm (c 0) ∈ ((T.caps p).face s).carrier)
    (hregion : ∀ s, (chartAt Plane (T.chart R : S)).symm (c 0) ∈
      ((T.caps p).face s).carrier → T.region p s = R)
    (hband : ∀ a : T.decomposition.IncidentGraphPieceIndex T.chart T.cut T.graphs,
      (chartAt Plane (T.chart R : S)).symm (c 0) ∉ (T.bands a.1 a.2).faces.carrier)
    (hcore : (T.refined.mesh R).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    (chartAt Plane (T.chart R : S)).symm ⁻¹' (⋃ s, ((T.caps p).face s).carrier)
      =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  have hcap := T.cap_union_complement_core_germ p R hz hq hregion hband
  have hi := support_eventuallyEq_interior hcore
  rw [← compl_interior_reflexSector c]
  filter_upwards [hcap, hi] with z hz hi
  exact hz.trans (congrArg Not hi)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
