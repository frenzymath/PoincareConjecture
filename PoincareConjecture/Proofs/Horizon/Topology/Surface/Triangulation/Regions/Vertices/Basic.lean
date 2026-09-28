


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Decomposition
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.VertexPatches
import PoincareConjecture.Proofs.Horizon.Topology.Paths.Trimming







set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace FiniteChartRegionDecomposition

variable (D : FiniteChartRegionDecomposition (M := M))


abbrev EdgeIndex := Σ i, Fin (D.edgeCount i)


noncomputable def vertices : Finset M := by
  classical
  exact Finset.univ.biUnion fun a : D.EdgeIndex =>
    {(D.edge a.1 a.2).map 0, (D.edge a.1 a.2).map 1}

omit [T2Space M] in
theorem mem_vertices {x : M} : x ∈ D.vertices ↔
    ∃ a : D.EdgeIndex, x = (D.edge a.1 a.2).map 0 ∨ x = (D.edge a.1 a.2).map 1 := by
  classical
  simp [vertices]

omit [T2Space M] in
theorem endpoints_mem_vertices (a : D.EdgeIndex) :
    (D.edge a.1 a.2).map 0 ∈ D.vertices ∧ (D.edge a.1 a.2).map 1 ∈ D.vertices :=
  ⟨D.mem_vertices.mpr ⟨a, Or.inl rfl⟩, D.mem_vertices.mpr ⟨a, Or.inr rfl⟩⟩

omit [T2Space M] in
theorem vertices_subset_boundary : (D.vertices : Set M) ⊆
    chartDiskBoundaryUnion D.centers D.radius := by
  intro x hx
  rw [← D.boundary_cover]
  obtain ⟨a, rfl | rfl⟩ := D.mem_vertices.mp hx
  · exact mem_iUnion.mpr ⟨a, mem_image_of_mem _ (by norm_num)⟩
  · exact mem_iUnion.mpr ⟨a, mem_image_of_mem _ (by norm_num)⟩

omit [T2Space M] in
theorem edge_endpoints_distinct (a : D.EdgeIndex) :
    (D.edge a.1 a.2).map 0 ≠ (D.edge a.1 a.2).map 1 := by
  intro h
  have := D.edge_injective a.1 a.2 (by norm_num) (by norm_num) h
  norm_num at this

omit [T2Space M] in
theorem open_edge_disjoint_vertices (a : D.EdgeIndex) :
    Disjoint ((D.edge a.1 a.2).map '' Ioo (0 : ℝ) 1) (D.vertices : Set M) := by
  apply disjoint_left.mpr
  rintro _ ⟨t, ht, rfl⟩ hv
  obtain ⟨b, hb⟩ := D.mem_vertices.mp hv
  by_cases hab : a = b
  · subst b
    rcases hb with hb | hb
    · exact ht.1.ne' (D.edge_injective a.1 a.2 ⟨ht.1.le, ht.2.le⟩ (by norm_num) hb)
    · exact ht.2.ne (D.edge_injective a.1 a.2 ⟨ht.1.le, ht.2.le⟩ (by norm_num) hb)
  · have hdis := Poincare.Topology.disjoint_arc_interior_of_endpoint_intersections
      (D.edge_injective a.1 a.2) (fun z hz => (D.edge_intersection a b hab hz).1)
    apply disjoint_left.mp hdis (mem_image_of_mem _ ht)
    rcases hb with hb | hb
    · exact hb ▸ mem_image_of_mem _ (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    · exact hb ▸ mem_image_of_mem _ (by norm_num : (1 : ℝ) ∈ Icc 0 1)

omit [T2Space M] in
theorem isCompact_edge (a : D.EdgeIndex) :
    IsCompact ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.image_of_continuousOn (D.edge a.1 a.2).smooth.continuousOn


theorem exists_vertex_patches :
    ∃ P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius p,
      (∀ p, (P p).centers ⊆ (D.centers : Set M)) ∧
      (∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier) ∧
      (∀ (p : D.vertices) (a : D.EdgeIndex), (p : M) ∉ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1 →
        Disjoint (P p).carrier ((D.edge a.1 a.2).map '' Icc (0 : ℝ) 1)) ∧
      (∀ p q, q ∈ (P p).carrier →
        (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles)) := by
  classical
  let N (p : M) := (⋃ a : {a : D.EdgeIndex |
    p ∉ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1},
      (D.edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1)ᶜ
  have hN (p : M) : N p ∈ 𝓝 p := by
    change (⋃ a : {a : D.EdgeIndex | p ∉ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1},
      (D.edge a.val.1 a.val.2).map '' Icc (0 : ℝ) 1)ᶜ ∈ 𝓝 p
    apply IsOpen.mem_nhds
    · exact (isClosed_iUnion_of_finite fun
        (a : {a : D.EdgeIndex | p ∉ (D.edge a.1 a.2).map '' Icc (0 : ℝ) 1}) =>
          (D.isCompact_edge a.val).isClosed).isOpen_compl
    · simp only [mem_compl_iff, mem_iUnion, not_exists]
      exact fun a => a.property
  have hcircles := chartDiskBoundaryUnion_eq_iUnion_chartCircle D.centers D.radius
    D.radius_pos D.closedBall_subset_target
  obtain ⟨P, hcenters, _, hNsub, hdis, _, hcirclesP⟩ :=
    exists_disjoint_chartCircle_arrangement_vertex_patches D.centers D.radius D.radius_pos
      D.closedBall_subset_target D.no_triple D.circle_regular D.vertices
      (fun p hp => hcircles ▸ D.vertices_subset_boundary hp) N (fun p _ => hN p)
  refine ⟨P, hcenters, hdis, ?_, ?_⟩
  · intro p a ha
    apply disjoint_left.mpr
    intro z hz hza
    exact hNsub p hz (mem_iUnion.mpr ⟨⟨a, ha⟩, hza⟩)
  · intro p q hq
    rw [hcircles]
    exact hcirclesP p q hq

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
