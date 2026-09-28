


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Coverage
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.CutNeighborhoods
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Neighborhoods








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))
  {dLeft dRight : D.IncidentEdgeIndex → EuclideanSpace ℝ (Fin 2)}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  (region : D.vertices → Bool × Bool → D.regions)
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun i => (chart (region p i) : M)))
  (L : ∀ p, D.CapGraphEndpoint P region (fun R => (chart R : M)) caps p.1.2 p.1.1
    ((S p).piece (S p).firstPiece) false (cut p.1.2 false))
  (T : ∀ p, D.CapGraphEndpoint P region (fun R => (chart R : M)) caps p.1.2 p.1.1
    ((S p).piece (S p).lastPiece) true (cut p.1.2 true))

include L T

theorem exists_fittedRegionCollar_neighborhood
    (hbands : ∀ p i, (B p i).faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1))
    (hcaps : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    {N : Set M} (hN : IsOpen N) (hvertices : (D.vertices : Set M) ⊆ N)
    (hcover : N ⊆ ⋃ p, ⋃ i, ((caps p).face i).carrier)
    (R : D.regions) {J : Set M} (hJ : IsClosed J)
    (hJK : Disjoint J (chartDiskBoundaryUnion D.centers D.radius))
    (hfront : frontier (D.fittedRegionCollar chart cut S K B caps region R) ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪ J)
    {q : M} (hq : q ∈ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ∩
        chartDiskBoundaryUnion D.centers D.radius) :
    ∃ W : Set M, IsOpen W ∧ q ∈ W ∧ W ∩ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ⊆
        D.fittedRegionCollar chart cut S K B caps region R := by
  classical
  by_cases hv : q ∈ D.vertices
  · refine ⟨N, hN, hvertices hv, ?_⟩
    exact (D.region_vertex_caps_cover_closure caps region hcaps hN hcover R).trans
      subset_union_left
  have hboundary := hq.2
  rw [← D.boundary_cover] at hboundary
  obtain ⟨e, t, ht, rfl⟩ := mem_iUnion.mp hboundary
  have ht0 : t ≠ 0 := by
    intro h
    exact hv (h ▸ (D.endpoints_mem_vertices e).1)
  have ht1 : t ≠ 1 := by
    intro h
    exact hv (h ▸ (D.endpoints_mem_vertices e).2)
  exact D.exists_region_closure_neighborhood_of_frontier_subset e R
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    (D.isCompact_fittedRegionCollar chart cut S K B caps region R).isClosed
    (D.fittedRegionCollar_regular_closed chart cut S K B caps region R)
    (D.fittedRegionCollar_subset_region_closure chart cut S K B caps region hbands hcaps R)
    (D.region_closure_inter_arrangement_subset_fittedRegionCollar chart cut S K B
      region caps L T R hq) hJ
    (fun h => disjoint_left.mp hJK h hq.2) hfront

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
