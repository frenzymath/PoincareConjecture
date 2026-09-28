import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.IncidentCaps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Intersections

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))

theorem region_vertex_caps_cover_closure
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (region : D.vertices → Bool × Bool → D.regions)
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    {N : Set M} (hN : IsOpen N) (hcover : N ⊆ ⋃ p, ⋃ i, ((B p).face i).carrier)
    (R : D.regions) :
    N ∩ closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ⊆
      D.vertexCapsInRegion B region R := by
  apply D.region_closure_subset_assigned_pieces
    (fun a : D.vertices × (Bool × Bool) => region a.1 a.2)
    (fun a => ((B a.1).face a.2).carrier)
    (fun a => ((B a.1).face a.2).isClosed_carrier)
    (fun a => hregion a.1 a.2) hN
  intro q hq
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover hq)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨(p, i), hi⟩

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
