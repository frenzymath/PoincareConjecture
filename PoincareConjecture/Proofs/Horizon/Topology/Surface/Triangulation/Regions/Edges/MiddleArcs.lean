import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Endpoints

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

def middleArc (cut : D.EdgeIndex → Bool → ℝ) (a : D.EdgeIndex) : Set M :=
  (D.edge a.1 a.2).map '' Icc (cut a false) (1 - cut a true)

omit [T2Space M] in

theorem middleArc_parameters {cut : D.EdgeIndex → Bool → ℝ}
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3)) (a : D.EdgeIndex) :
    0 < cut a false ∧ cut a false < 1 - cut a true ∧ 1 - cut a true < 1 := by
  have h0 := hcut a false
  have h1 := hcut a true
  exact ⟨h0.1, by linarith [h0.2, h1.2], by linarith [h1.1]⟩

omit [T2Space M] in

theorem middleArc_subset_open_edge {cut : D.EdgeIndex → Bool → ℝ}
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3)) (a : D.EdgeIndex) :
    D.middleArc cut a ⊆ (D.edge a.1 a.2).map '' Ioo (0 : ℝ) 1 := by
  apply image_mono
  intro t ht
  have h := D.middleArc_parameters hcut a
  exact ⟨h.1.trans_le ht.1, ht.2.trans_lt h.2.2⟩

omit [T2Space M] in

theorem isCompact_middleArc {cut : D.EdgeIndex → Bool → ℝ}
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3)) (a : D.EdgeIndex) :
    IsCompact (D.middleArc cut a) := by
  have h := D.middleArc_parameters hcut a
  exact isCompact_Icc.image_of_continuousOn ((D.edge a.1 a.2).smooth.continuousOn.mono
    (Icc_subset_Icc h.1.le h.2.2.le))

omit [T2Space M] in

theorem middleArc_disjoint_edge {cut : D.EdgeIndex → Bool → ℝ}
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3))
    {a b : D.EdgeIndex} (hab : a ≠ b) :
    Disjoint (D.middleArc cut a) ((D.edge b.1 b.2).map '' Icc (0 : ℝ) 1) :=
  (Poincare.Topology.disjoint_arc_interior_of_endpoint_intersections
    (D.edge_injective a.1 a.2) (fun _ hq => (D.edge_intersection a b hab hq).1)).mono_left
      (D.middleArc_subset_open_edge hcut a)

omit [T2Space M] in

theorem middleArc_disjoint_vertices {cut : D.EdgeIndex → Bool → ℝ}
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3)) (a : D.EdgeIndex) :
    Disjoint (D.middleArc cut a) (D.vertices : Set M) :=
  (D.open_edge_disjoint_vertices a).mono_left (D.middleArc_subset_open_edge hcut a)

omit [T2Space M] in

theorem edge_subset_endpoint_segments_union_middleArc
    {cut : D.EdgeIndex → Bool → ℝ} (a : D.EdgeIndex) :
    (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 ⊆
      (D.edgeFromEndpoint a false '' Icc 0 (cut a false)) ∪
        D.middleArc cut a ∪ (D.edgeFromEndpoint a true '' Icc 0 (cut a true)) := by
  rintro q ⟨t, ht, rfl⟩
  by_cases h0 : t ≤ cut a false
  · exact Or.inl (Or.inl ⟨t, ⟨ht.1, h0⟩, rfl⟩)
  by_cases h1 : t ≤ 1 - cut a true
  · exact Or.inl (Or.inr ⟨t, ⟨(lt_of_not_ge h0).le, h1⟩, rfl⟩)
  · apply Or.inr
    rw [D.edgeFromEndpoint_image_terminal]
    exact ⟨t, ⟨(lt_of_not_ge h1).le, ht.2⟩, rfl⟩

omit [T2Space M] in

theorem boundary_subset_endpoint_cover_union_middleArcs
    {cut : D.EdgeIndex → Bool → ℝ} {C : Set M}
    (hC : ∀ a b, D.edgeFromEndpoint a b '' Icc 0 (cut a b) ⊆ C) :
    chartDiskBoundaryUnion D.centers D.radius ⊆ C ∪ ⋃ a, D.middleArc cut a := by
  rw [← D.boundary_cover]
  intro q hq
  obtain ⟨a, ha⟩ := mem_iUnion.mp hq
  rcases D.edge_subset_endpoint_segments_union_middleArc a ha with (h | h) | h
  · exact Or.inl (hC a false h)
  · exact Or.inr (mem_iUnion.mpr ⟨a, h⟩)
  · exact Or.inl (hC a true h)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
