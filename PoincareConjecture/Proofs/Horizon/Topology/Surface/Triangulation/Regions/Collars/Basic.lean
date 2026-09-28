import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.FamilyWidths
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.RegionBands
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing

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

def graphBandsInRegion (R : D.regions) : Set M :=
  ⋃ a : {a : D.IncidentGraphPieceIndex chart cut S // a.1.1.1 = R},
    (B a.1.1 a.1.2).faces.carrier

omit [T2Space M] in
theorem graphBandsInRegion_eq_iUnion_chains (R : D.regions) :
    D.graphBandsInRegion chart cut S K B R =
      ⋃ p : {p : D.IncidentEdgeIndex // p.1.1 = R}, ⋃ i, (B p.1 i).faces.carrier := by
  ext q
  constructor
  · rintro hq
    obtain ⟨a, ha⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨a.1.1, a.2⟩, mem_iUnion.mpr ⟨a.1.2, ha⟩⟩
  · intro hq
    obtain ⟨p, hp⟩ := mem_iUnion.mp hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨⟨⟨p.1, i⟩, p.2⟩, hi⟩

omit [T2Space M] in
theorem isCompact_graphBandsInRegion (R : D.regions) :
    IsCompact (D.graphBandsInRegion chart cut S K B R) :=
  isCompact_iUnion (fun a => isCompact_iUnion
    (fun i => ((B a.1.1 a.1.2).faces.face i).isCompact_carrier_image))

theorem graphBandsInRegion_regular_closed (R : D.regions) :
    closure (interior (D.graphBandsInRegion chart cut S K B R)) =
      D.graphBandsInRegion chart cut S K B R :=
  Poincare.Topology.closure_interior_iUnion_of_regular_closed _
    (fun a => (B a.1.1 a.1.2).faces.isClosed_carrier)
    (fun a => (B a.1.1 a.1.2).faces.closure_interior_carrier)

omit [T2Space M] in
theorem graphBandsInRegion_subset_region_closure
    (hregion : ∀ p i, (B p i).faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1)) (R : D.regions) :
    D.graphBandsInRegion chart cut S K B R ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
  apply iUnion_subset
  intro a
  simpa only [a.2] using hregion a.1.1 a.1.2

variable {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)

def fittedRegionCollar (R : D.regions) : Set M :=
  D.vertexCapsInRegion caps region R ∪ D.graphBandsInRegion chart cut S K B R

omit [T2Space M] in
theorem isCompact_fittedRegionCollar (R : D.regions) :
    IsCompact (D.fittedRegionCollar chart cut S K B caps region R) :=
  (D.isCompact_vertexCapsInRegion caps region R).union
    (D.isCompact_graphBandsInRegion chart cut S K B R)

theorem fittedRegionCollar_regular_closed (R : D.regions) :
    closure (interior (D.fittedRegionCollar chart cut S K B caps region R)) =
      D.fittedRegionCollar chart cut S K B caps region R := by
  apply subset_antisymm
    (closure_minimal interior_subset (D.isCompact_fittedRegionCollar chart cut S K B caps region R).isClosed)
  apply union_subset
  · rw [← D.vertexCapsInRegion_regular_closed caps region R]
    exact closure_mono (interior_mono subset_union_left)
  · rw [← D.graphBandsInRegion_regular_closed chart cut S K B R]
    exact closure_mono (interior_mono subset_union_right)

omit [T2Space M] in
theorem fittedRegionCollar_subset_region_closure
    (hbands : ∀ p i, (B p i).faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1))
    (hcaps : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) (R : D.regions) :
    D.fittedRegionCollar chart cut S K B caps region R ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) :=
  union_subset (D.vertexCapsInRegion_subset_region_closure caps region hcaps R)
    (D.graphBandsInRegion_subset_region_closure chart cut S K B hbands R)

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
