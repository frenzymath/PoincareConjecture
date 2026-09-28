


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Neighborhoods
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing.Frontier








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)


def vertexCapChordsInRegion (R : D.regions) : Set M :=
  ⋃ a : {a : D.vertices × (Bool × Bool) // region a.1 a.2 = R},
    (((B a.1.1).face a.1.2).boundary 0).map '' Icc (0 : ℝ) 1

omit [T2Space M] in
theorem isCompact_vertexCapChordsInRegion (R : D.regions) :
    IsCompact (D.vertexCapChordsInRegion B region R) :=
  isCompact_iUnion (fun a => isCompact_Icc.image_of_continuousOn
    (((B a.1.1).face a.1.2).boundary 0).smooth.continuousOn)

theorem vertexCapsInRegion_regular_closed (R : D.regions) :
    closure (interior (D.vertexCapsInRegion B region R)) = D.vertexCapsInRegion B region R := by
  apply Poincare.Topology.closure_interior_iUnion_of_regular_closed
    (fun a : {a : D.vertices × (Bool × Bool) // region a.1 a.2 = R} =>
      ((B a.1.1).face a.1.2).carrier)
    (fun a => ((B a.1.1).face a.1.2).isClosed_carrier)
  intro a
  rw [(B a.1.1).carrier_eq a.1.2]
  exact coordinate_triangle_closure_interior _ _ ((B a.1.1).triangle_subset_source a.1.2)

omit [T2Space M] in
theorem vertexCapsInRegion_subset_region_closure
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) (R : D.regions) :
    D.vertexCapsInRegion B region R ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
  apply iUnion_subset
  intro a
  simpa only [a.2] using hregion a.1.1 a.1.2

theorem frontier_vertexCapsInRegion_subset
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))) (R : D.regions) :
    frontier (D.vertexCapsInRegion B region R) ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪ D.vertexCapChordsInRegion B region R := by
  have hselected := D.frontier_assigned_pieces_subset
    (fun a : D.vertices × (Bool × Bool) => region a.1 a.2)
    (fun a => ((B a.1).face a.2).carrier)
    (fun a => ((B a.1).face a.2).isClosed_carrier) (fun a => hregion a.1 a.2) R
  have htotal : frontier (⋃ a : D.vertices × (Bool × Bool), ((B a.1).face a.2).carrier) ⊆
      ⋃ p, ⋃ i, (((B p).face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
    rw [iUnion_prod']
    exact (Poincare.Topology.frontier_iUnion_subset_iUnion_frontier_of_isClosed
      (fun p => ⋃ i, ((B p).face i).carrier)
      (fun p => isClosed_iUnion_of_finite (fun i => ((B p).face i).isClosed_carrier))).trans
        (iUnion_mono (fun p => (B p).frontier_union_subset_chords))
  intro q hq
  by_cases hqK : q ∈ chartDiskBoundaryUnion D.centers D.radius
  · exact Or.inl hqK
  have hqTotal := (hselected hq).resolve_left hqK
  obtain ⟨p, hp⟩ := mem_iUnion.mp (htotal hqTotal)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hqCap : q ∈ ((B p).face i).carrier :=
    ((B p).face i).isClosed_carrier.frontier_subset
      (((B p).face i).boundary_image_subset_frontier 0 hi)
  have hqR := D.region_closure_diff_arrangement_subset R
    ⟨D.vertexCapsInRegion_subset_region_closure B region hregion R
      ((D.isClosed_vertexCapsInRegion B region R).frontier_subset hq), hqK⟩
  have hqI := D.region_closure_diff_arrangement_subset (region p i) ⟨hregion p i hqCap, hqK⟩
  have hpi : region p i = R := by
    by_contra hne
    exact disjoint_left.mp (D.regions_disjoint hne) hqI hqR
  exact Or.inr (mem_iUnion.mpr ⟨⟨(p, i), hpi⟩, hi⟩)

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
