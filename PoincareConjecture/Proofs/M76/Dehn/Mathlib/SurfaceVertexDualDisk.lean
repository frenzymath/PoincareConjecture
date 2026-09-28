import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence
import PoincareConjecture.Proofs.M76.Mathlib.CenteredDerivedSurface
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonClosedStarDisk
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseLinkSection











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]




theorem connected_barycentric_vertex_link_of_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.barycentricSubdivision.vertices) :
    (K.barycentricSubdivision.link p).vertexAbstractComplex.edgeGraph.Connected := by
  obtain ⟨s, hs, rfl⟩ := (K.mem_barycentricSubdivision_vertices_iff p).mp hp
  unfold barycentricSubdivision
  exact K.connected_derived_faceCenter_link_of_pure_triangles _ _ hpure hlinks ⟨s, hs⟩



theorem isConnected_barycentric_vertex_link_of_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.barycentricSubdivision.vertices) :
    IsConnected (K.barycentricSubdivision.link p).space :=
  ((K.barycentricSubdivision.link p).isPathConnected_space_of_connected_edgeGraph
    (K.connected_barycentric_vertex_link_of_pure_triangles hpure hlinks hp)).isConnected





theorem isFinitePLBallPair_barycentricDualBlock_vertex
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    {p : E} (hp : p ∈ K.vertices) (hlink : IsConnected (K.link p).space) :
    IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock {p}).space
      (K.barycentricSubdivision.link p).space := by
  have hbound (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    obtain ⟨t, _, ht, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hpM := K.vertices_subset_barycentricSubdivision_vertices hp
  have hconn := K.isConnected_barycentric_original_vertex_link hp hlink
  have hgraph := (K.barycentricSubdivision.link p).connected_edgeGraph_of_isConnected
    (finite_link_faces K.barycentricSubdivision_finite p) hconn
  obtain ⟨n, P, hPi, hPe, hPlink⟩ :=
    K.barycentricSubdivision.exists_surface_link_polygon K.barycentricSubdivision_finite
      (K.barycentricSubdivision_pure_triangles hpure)
      (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces) p hgraph
  rw [K.barycentricDualBlock_singleton_eq_closedStar hp]
  exact K.barycentricSubdivision.isFinitePLBallPair_closedStar_of_polygon_link
    K.barycentricSubdivision_finite hpM P hPe hPi hPlink

end Geometry.SimplicialComplex
