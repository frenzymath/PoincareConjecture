import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapClassification
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapCoreFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedAttachmentCompleteFans

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

set_option maxHeartbeats 1200000 in

theorem canonical_vertex_fan_in_cap_of_not_unmatched_tip
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (hr : T.length < 1)
    (htrim : ∀ (s : Bool × Bool) (e : T.decomposition.EdgeIndex),
      Disjoint ((T.caps p).face s).carrier
        ((T.decomposition.edge e.1 e.2).map '' Ioo (T.cut e false) (1 - T.cut e true)))
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : ∃ s, q.1 ∈ ((T.caps p).face s).carrier)
    (htip : T.IsCapOuterTip p q.1 → T.IsTrimTip q.1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  rcases T.cap_point_cases p htrim hq with hint | htrimtip | houter | hchord | hopen | htop
  · exact T.canonical_vertex_fan_in_cap_interior g p q hint
  · obtain ⟨e, terminal, he⟩ := htrimtip
    rw [he]
    exact T.vertex_fan_at_cap_tip g e terminal
  · exact False.elim (houter.2.1 (htip houter.1))
  · obtain ⟨s, t, ht, he, hbands⟩ := hchord
    exact T.canonical_vertex_fan_on_open_cap_chord_of_not_mem_bands g p s ht
      (fun a => he ▸ hbands a) q he
  · obtain ⟨a, ha⟩ := hopen
    exact ha.elim (T.canonical_vertex_fan_on_open_left_attachment g a q)
      (T.canonical_vertex_fan_on_open_right_attachment g a q)
  · obtain ⟨a, terminal, he⟩ := htop
    cases terminal
    · apply T.canonical_vertex_fan_at_first_upper_attachment g a hr q
      simpa only [capBandAttachmentTop, Bool.false_eq_true, ite_false] using he.symm
    · apply T.canonical_vertex_fan_at_last_upper_attachment g a hr q
      simpa only [capBandAttachmentTop, ite_true] using he.symm

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
