


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapEndpoints







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

omit [T2Space M] in
theorem incident_middleArc_subset_fittedRegionCollar (p : D.IncidentEdgeIndex) :
    D.middleArc cut p.1.2 ⊆ D.fittedRegionCollar chart cut S K B caps region p.1.1 := by
  rw [← D.incident_middleArc_pieceArcs_cover chart cut S p]
  apply iUnion_subset
  intro i q hq
  apply Or.inr
  exact mem_iUnion.mpr ⟨⟨⟨p, i⟩, rfl⟩,
    (B p i).baseArc_subset_carrier ((S p).cut_lt i) hq⟩

include L T

theorem incident_edge_subset_fittedRegionCollar (p : D.IncidentEdgeIndex) :
    (D.edge p.1.2.1 p.1.2.2).map '' Icc (0 : ℝ) 1 ⊆
      D.fittedRegionCollar chart cut S K B caps region p.1.1 := by
  intro q hq
  rcases D.edge_subset_endpoint_segments_union_middleArc (cut := cut) p.1.2 hq with
    (hleft | hmiddle) | hright
  · apply Or.inl
    exact mem_iUnion.mpr ⟨⟨(D.edgeEndpoint p.1.2 false, (L p).sector), (L p).sector_region⟩,
      ((caps (D.edgeEndpoint p.1.2 false)).face (L p).sector).isClosed_carrier.frontier_subset
        ((((caps (D.edgeEndpoint p.1.2 false)).face (L p).sector).boundary_image_subset_frontier
          (L p).radialEdge) ((L p).radial_image.symm ▸ hleft))⟩
  · exact D.incident_middleArc_subset_fittedRegionCollar chart cut S K B region caps p hmiddle
  · apply Or.inl
    exact mem_iUnion.mpr ⟨⟨(D.edgeEndpoint p.1.2 true, (T p).sector), (T p).sector_region⟩,
      ((caps (D.edgeEndpoint p.1.2 true)).face (T p).sector).isClosed_carrier.frontier_subset
        ((((caps (D.edgeEndpoint p.1.2 true)).face (T p).sector).boundary_image_subset_frontier
          (T p).radialEdge) ((T p).radial_image.symm ▸ hright))⟩

theorem region_closure_inter_arrangement_subset_fittedRegionCollar (R : D.regions) :
    closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ∩
      chartDiskBoundaryUnion D.centers D.radius ⊆
        D.fittedRegionCollar chart cut S K B caps region R := by
  rintro q ⟨hq, hK⟩
  have hfront : q ∈ frontier (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) :=
    ⟨hq, fun hi => (connectedComponentIn_subset _ _ (interior_subset hi)) hK⟩
  rw [D.region_frontier R] at hfront
  obtain ⟨e, he⟩ := mem_iUnion.mp hfront
  exact D.incident_edge_subset_fittedRegionCollar chart cut S K B region caps L T
    ⟨(R, e.1), e.2⟩ he

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
