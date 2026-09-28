import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedExposedTipLineFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapAvoidance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedNonCapFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem canonical_vertex_fan_at_cap_outer_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (hr : T.length < 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (htip : T.IsCapOuterTip p q.1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  by_cases hint : q.1 ∈ interior (⋃ s, ((T.caps p).face s).carrier)
  · exact T.canonical_vertex_fan_in_cap_interior g p q hint
  by_cases htrim : T.IsTrimTip q.1
  · obtain ⟨e, terminal, he⟩ := htrim
    rw [he]
    exact T.vertex_fan_at_cap_tip g e terminal
  obtain ⟨R, ⟨z, hz, hzq⟩, _, hregion, hband⟩ :=
    T.unmatched_cap_outer_tip_core_incidence p hr (T.caps_disjoint_open_trimmed_arc p)
      htip htrim hint
  rcases htip with ⟨i, hi⟩ | ⟨i, hi⟩
  · by_cases hind : LinearIndependent ℝ
        (![chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip false) - z,
          chartAt Plane (T.chart R : S) ((T.caps p).secondOuterTip true) - z] : Fin 2 → Plane)
    · rw [hi]
      exact T.vertex_fan_at_independent_first_outer_tip g p R i hz (hzq.trans hi)
        (fun s hs => hregion s (hi.symm ▸ hs)) (fun a => hi ▸ hband a) hind
    · exact T.canonical_vertex_fan_at_collinear_first_outer_tip g p R i q hzq hz hi
        (fun s hs => hregion s (hi.symm ▸ hs)) (fun a => hi ▸ hband a) hind
  · by_cases hind : LinearIndependent ℝ
        (![chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip false) - z,
          chartAt Plane (T.chart R : S) ((T.caps p).firstOuterTip true) - z] : Fin 2 → Plane)
    · rw [hi]
      exact T.vertex_fan_at_independent_second_outer_tip g p R i hz (hzq.trans hi)
        (fun s hs => hregion s (hi.symm ▸ hs)) (fun a => hi ▸ hband a) hind
    · exact T.canonical_vertex_fan_at_collinear_second_outer_tip g p R i q hzq hz hi
        (fun s hs => hregion s (hi.symm ▸ hs)) (fun a => hi ▸ hband a) hind



theorem canonical_vertex_fan (g : RiemannianMetric 2 S) (hr : T.length < 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  by_cases hcap : ∃ p s, q.1 ∈ ((T.caps p).face s).carrier
  · obtain ⟨p, s, hs⟩ := hcap
    by_cases htip : T.IsCapOuterTip p q.1
    · exact T.canonical_vertex_fan_at_cap_outer_tip g p hr q htip
    · exact T.canonical_vertex_fan_in_cap_of_not_unmatched_tip g p hr
        (T.caps_disjoint_open_trimmed_arc p) q ⟨s, hs⟩ (fun h => False.elim (htip h))
  · exact T.canonical_vertex_fan_of_not_mem_caps g q (fun p s hs => hcap ⟨p, s, hs⟩)

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
