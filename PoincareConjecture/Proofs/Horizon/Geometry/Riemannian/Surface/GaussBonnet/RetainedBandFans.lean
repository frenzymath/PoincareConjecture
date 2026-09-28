import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandClassification
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandJunctionFans

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

theorem canonical_vertex_fan_in_band_of_not_mem_caps
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (T.bands p i).faces.carrier)
    (hcap : ∀ v s, q.1 ∉ ((T.caps v).face s).carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  classical
  by_cases hcut : q.1 ∈ (T.bands p i).faces.leftCut ∪ (T.bands p i).faces.rightCut
  · obtain ⟨j, k, hjk, u, hu, he⟩ :=
      T.exists_internal_band_cut_of_endpoint_cut_not_mem_caps p i hcap hcut
    by_cases hupper : u = T.length
    · exact T.canonical_vertex_fan_at_upper_band_junction g p j k hjk q
        (he.symm.trans (congrArg ((T.chains p).cutRay j.succ) hupper))
    · exact T.canonical_vertex_fan_on_half_open_band_cut_of_not_mem_caps g p j k hjk q hcap
        ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2 hupper⟩, he⟩
  · exact T.canonical_vertex_fan_in_band_off_endpoint_cuts_of_not_mem_caps g p i q hq hcap
      (fun h => hcut (Or.inl h)) (fun h => hcut (Or.inr h))

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
