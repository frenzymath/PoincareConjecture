import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedPointClassification







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

set_option maxHeartbeats 800000 in


theorem canonical_vertex_fan_of_not_mem_caps (g : RiemannianMetric 2 S)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hcap : ∀ p s, q.1 ∉ ((T.caps p).face s).carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  by_cases hband : ∃ (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count),
      q.1 ∈ (T.bands p i).faces.carrier
  · obtain ⟨p, i, hi⟩ := hband
    exact T.canonical_vertex_fan_in_band_of_not_mem_caps g p i q hi hcap
  · exact T.canonical_vertex_fan_of_not_mem_caps_bands g q hcap
      (fun p i hi => hband ⟨p, i, hi⟩)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
