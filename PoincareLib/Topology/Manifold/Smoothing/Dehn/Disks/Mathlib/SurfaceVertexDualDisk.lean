import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricDualSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricSurfaceIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.CenteredDerivedSurface
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.SurfaceLinkPolygon
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolygonClosedStarDisk
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderBaseLinkSection

/-!
# Actual vertex disks in the derived surface

The full original vertex links and triangular incidence construct a polygon
on each derived link. Its actual closed star is a finite PL disk with that
entire link as rim. Every centroid vertex also retains a connected full link.
See Hudson 1969, pp. 58--63, Putman, Theorem 5.1, pp. 15--16, and M76 Dehn
derivation 021, section 2.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- Each vertex of the actual centroid subdivision has a connected whole
link, including edge and triangle centroids. This follows from the original
pure triangular carrier and its original vertex links. See Dehn 021, section 2. -/
theorem connected_barycentric_vertex_link_of_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.barycentricSubdivision.vertices) :
    (K.barycentricSubdivision.link p).vertexAbstractComplex.edgeGraph.Connected := by
  obtain ⟨s, hs, rfl⟩ := (K.mem_barycentricSubdivision_vertices_iff p).mp hp
  unfold barycentricSubdivision
  exact K.connected_derived_faceCenter_link_of_pure_triangles _ _ hpure hlinks ⟨s, hs⟩

/-- The whole geometric link at every centroid-subdivision vertex is
connected, in the topology of the same carrier. See Dehn 021, section 2. -/
theorem isConnected_barycentric_vertex_link_of_pure_triangles
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.barycentricSubdivision.vertices) :
    IsConnected (K.barycentricSubdivision.link p).space :=
  ((K.barycentricSubdivision.link p).isPathConnected_space_of_connected_edgeGraph
    (K.connected_barycentric_vertex_link_of_pure_triangles hpure hlinks hp)).isConnected

/-- The actual dual block of an original surface vertex is a finite PL disk
whose specified rim is the entire link in the same centroid subdivision.
Purity, paired edge cofaces and the original link produce the disk internally.
See Hudson pp. 58--63 and Dehn derivation 021, section 2. -/
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
