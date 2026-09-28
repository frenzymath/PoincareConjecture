


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Collars








set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



theorem exists_boundary_neighborhood
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius p) :
    ∃ (l r ε : D.EdgeIndex → ℝ)
      (C : D.EdgeIndex → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M),
      (∀ a, 0 < l a ∧ l a < r a ∧ r a < 1 ∧ 0 < ε a) ∧
      (∀ a, (D.edge a.1 a.2).map '' Icc 0 (l a) ⊆
          (P ⟨(D.edge a.1 a.2).map 0, (D.endpoints_mem_vertices a).1⟩).openCarrier ∧
        (D.edge a.1 a.2).map '' Icc (r a) 1 ⊆
          (P ⟨(D.edge a.1 a.2).map 1, (D.endpoints_mem_vertices a).2⟩).openCarrier) ∧
      (∀ a, collarParameterEquiv ⁻¹' (Icc (l a) (r a) ×ˢ Ioo (-ε a) (ε a)) ⊆
        (C a).source) ∧
      (∀ a t, C a (collarParameterEquiv.symm (t, 0)) = (D.edge a.1 a.2).map t) ∧
      (∀ a, (C a).target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).source) ∧
      (∀ a, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C a) (C a).source) ∧
      (∀ a, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C a).symm (C a).target) ∧
      Pairwise (fun a b => Disjoint (C a).target (C b).target) ∧
      (∀ a b, a ≠ b → Disjoint (C a).target ((D.edge b.1 b.2).map '' Icc (0 : ℝ) 1)) ∧
      chartDiskBoundaryUnion D.centers D.radius ⊆
        (⋃ p, (P p).openCarrier) ∪ (⋃ a, (C a).target) := by
  let U (a : D.EdgeIndex) :=
    (P ⟨(D.edge a.1 a.2).map 0, (D.endpoints_mem_vertices a).1⟩).openCarrier
  let V (a : D.EdgeIndex) :=
    (P ⟨(D.edge a.1 a.2).map 1, (D.endpoints_mem_vertices a).2⟩).openCarrier
  obtain ⟨l, r, ε, C, hbounds, hends, hstrip, haxis, hchart, hC, hCinv, hdis, havoid⟩ :=
    D.exists_trimmed_collars U V
      (fun a => (P _).isOpen_openCarrier.mem_nhds (P _).mem_openCarrier)
      (fun a => (P _).isOpen_openCarrier.mem_nhds (P _).mem_openCarrier)
  refine ⟨l, r, ε, C, hbounds, hends, hstrip, haxis, hchart, hC, hCinv, hdis, havoid, ?_⟩
  rw [← D.boundary_cover]
  rintro z hz
  obtain ⟨a, t, ht, rfl⟩ := mem_iUnion.mp hz
  by_cases htl : t ≤ l a
  · exact Or.inl (mem_iUnion.mpr ⟨_, (hends a).1 ⟨t, ⟨ht.1, htl⟩, rfl⟩⟩)
  by_cases hrt : r a ≤ t
  · exact Or.inl (mem_iUnion.mpr ⟨_, (hends a).2 ⟨t, ⟨hrt, ht.2⟩, rfl⟩⟩)
  · apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨a, ?_⟩
    rw [← haxis a t]
    apply (C a).map_source
    apply hstrip a
    change collarParameterEquiv (collarParameterEquiv.symm (t, 0)) ∈
      Icc (l a) (r a) ×ˢ Ioo (-ε a) (ε a)
    rw [collarParameterEquiv.apply_symm_apply]
    exact ⟨⟨(lt_of_not_ge htl).le, (lt_of_not_ge hrt).le⟩,
      neg_neg_of_pos (hbounds a).2.2.2, (hbounds a).2.2.2⟩


def regionCore (N : Set M) (x : M) : Set M :=
  closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x) \ N

omit [T2Space M] in
theorem regionCore_subset_component {N : Set M}
    (hN : chartDiskBoundaryUnion D.centers D.radius ⊆ N) (x : M) :
    D.regionCore N x ⊆ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  intro z hz
  by_contra hzc
  apply hz.2
  apply hN
  apply Poincare.Topology.frontier_connectedComponentIn_compl_subset
    (isClosed_chartDiskBoundaryUnion D.centers D.radius) x
  exact ⟨hz.1, fun hi => hzc (interior_subset hi)⟩

omit [T2Space M] in
theorem isCompact_regionCore {N : Set M} (hN : IsOpen N) (x : D.regions) :
    IsCompact (D.regionCore N x) := by
  obtain ⟨p, hp, hcomponent, hclosed, hcompact, hchart⟩ :=
    D.region_containment x (D.regions_outside x x.property)
  exact hcompact.diff hN

omit [T2Space M] in
theorem regionCores_disjoint {N : Set M}
    (hN : chartDiskBoundaryUnion D.centers D.radius ⊆ N) :
    Pairwise (fun x y : D.regions => Disjoint (D.regionCore N x) (D.regionCore N y)) := by
  intro x y hxy
  apply disjoint_left.mpr
  intro z hzx hzy
  apply hxy
  apply Subtype.ext
  apply D.regions_distinct x x.property y y.property
  exact (connectedComponentIn_eq (D.regionCore_subset_component hN x hzx)).trans
    (connectedComponentIn_eq (D.regionCore_subset_component hN y hzy)).symm

omit [T2Space M] in
theorem regionCores_cover (N : Set M) : (⋃ x : D.regions, D.regionCore N x) = Nᶜ := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    exact hx.2
  · intro hz
    have hzcover : z ∈ ⋃ x ∈ D.regions,
        closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x) := by
      rw [D.region_closure_cover]
      trivial
    obtain ⟨x, hx, hzclosure⟩ := mem_iUnion₂.mp hzcover
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hzclosure, hz⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
