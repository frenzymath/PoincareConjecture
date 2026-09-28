


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Basic








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



theorem exists_vertex_sector_regions {p : D.vertices}
    (P : ChartCircleArrangementVertexPatch D.radius (p : M))
    (hlocal : ∀ q ∈ P.carrier,
      q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ P.circles) :
    ∃ region : Bool × Bool → D.regions,
      (∀ i, P.sector i ⊆ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i)) ∧
      (∀ i, P.closedSector i ⊆ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i))) ∧
      (∀ i, (p : M) ∈ frontier (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i))) ∧
      P.carrier ⊆ ⋃ i, closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i)) := by
  have houtside (i : Bool × Bool) :
      P.sector i ⊆ (chartDiskBoundaryUnion D.centers D.radius)ᶜ := by
    intro q hq hK
    exact disjoint_left.mp (P.sector_disjoint_circles i) hq
      ((hlocal q (P.closedSector_subset_carrier i (P.sector_subset_closed i hq))).mp hK)
  choose q hq using fun i => (P.isPathConnected_sector i).nonempty
  choose region hregion using fun i => D.region_representative (q i) (houtside i (hq i))
  have hsector (i : Bool × Bool) : P.sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i) := by
    rw [← hregion i]
    exact (P.isPathConnected_sector i).isConnected.isPreconnected.subset_connectedComponentIn
      (hq i) (houtside i)
  have hclosed (i : Bool × Bool) : P.closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region i)) := by
    rw [← P.closure_sector i]
    exact closure_mono (hsector i)
  refine ⟨region, hsector, hclosed, ?_, ?_⟩
  · intro i
    refine ⟨hclosed i (P.mem_closedSector i), ?_⟩
    intro hp
    exact connectedComponentIn_subset _ _ (interior_subset hp)
      (D.vertices_subset_boundary p.property)
  · rw [← P.closedSectors_cover]
    exact iUnion_mono hclosed



theorem exists_vertex_patches_with_regions :
    ∃ (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
      (region : D.vertices → Bool × Bool → D.regions),
      (∀ p, (P p).centers ⊆ (D.centers : Set M)) ∧
      (∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier) ∧
      (∀ (p : D.vertices) (a : D.EdgeIndex),
        (p : M) ∉ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 →
        Disjoint (P p).carrier ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1)) ∧
      (∀ p q, q ∈ (P p).carrier →
        (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles)) ∧
      (∀ p i, (P p).sector i ⊆ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)) ∧
      (∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) ∧
      (∀ p i, (p : M) ∈ frontier (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) ∧
      (∀ p, (P p).carrier ⊆ ⋃ i, closure (connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) := by
  obtain ⟨P, hcenters, hdisjoint, havoid, hlocal⟩ := D.exists_vertex_patches
  choose region hsector hclosed hfront hcover using
    fun p => D.exists_vertex_sector_regions (P p) (hlocal p)
  exact ⟨P, region, hcenters, hdisjoint, havoid, hlocal, hsector, hclosed, hfront, hcover⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
