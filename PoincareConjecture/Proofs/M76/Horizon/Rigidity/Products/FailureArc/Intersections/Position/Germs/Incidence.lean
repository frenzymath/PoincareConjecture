import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Germs.Interior
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Germs.Boundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.GraphIncidence



set_option autoImplicit false
open Set Geometry Filter Topology
open scoped Topology

namespace PoincareConjecture.M76

open Classical in
theorem source_intersection_graph_incidence
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hG : G.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : Set X) (Q : Set E) (hGs : G.space = {z | z ∈ K.space ∧ g z ∈ S})
    (hboundary : ∀ x ∈ G.space ∩ Q,
      Nonempty (OriginalSurfacePairChart e S (g '' K.space) (g x) true))
    (hinterior : ∀ x ∈ G.space \ Q,
      Nonempty (OriginalSurfacePairChart e S (g '' K.space) (g x) false)) :
    (∀ a ∈ G.faces, a.card ≤ 2) ∧
    (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
      if (v : E) ∈ Q then 1 else 2) ∧
    G.space ∩ Q = Subtype.val '' {v : G.vertices |
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
  apply G.face_card_and_degree_of_boundary_segment_germs hG Q
  intro x hx
  have hxK := (hGs.subset hx).1
  by_cases hxQ : x ∈ Q
  · obtain ⟨C⟩ := hboundary x ⟨hx, hxQ⟩
    obtain ⟨d, rim, hd, hxr, _, hnear⟩ := exists_source_intersection_boundary_germ
      K hK hg hgi C.chart C.compatible C.coordinates C.forwardPL
      (by simpa using C.first_surface) (by simpa using C.second_surface)
      ⟨x, hxK⟩ C.center_source C.center_coordinates C.center_zero
    obtain ⟨u, hu, hgerm⟩ := hd.exists_segment_germ_of_mem_boundary hxr
    refine ⟨u, u, hu, hu, fun _ => rfl, fun hn => (hn hxQ).elim, ?_⟩
    filter_upwards [hnear, hgerm] with z hz hz'
    simpa only [union_self, hGs, mem_ofPred_eq] using hz.trans hz'
  · obtain ⟨C⟩ := hinterior x ⟨hx, hxQ⟩
    obtain ⟨d, rim, hd, hxd, _, hnear⟩ := exists_source_intersection_interval_germ
      K hK hg hgi C.chart C.compatible C.coordinates C.forwardPL
      (by simpa using C.first_surface) (by simpa using C.second_surface)
      ⟨x, hxK⟩ C.center_source C.center_coordinates C.center_zero
    obtain ⟨u, v, hu, hv, hinter, hgerm⟩ := hd.exists_two_segment_germ hxd
    refine ⟨u, v, hu, hv, fun h => (hxQ h).elim, fun _ => hinter, ?_⟩
    filter_upwards [hnear, hgerm] with z hz hz'
    simpa only [hGs, mem_ofPred_eq] using hz.trans hz'

end PoincareConjecture.M76
