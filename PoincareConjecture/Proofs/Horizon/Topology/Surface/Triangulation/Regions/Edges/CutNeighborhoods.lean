


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Sides









set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

namespace Poincare.Topology



theorem local_region_subset_of_regular_closed
    {X : Type*} [TopologicalSpace X] {C R W : Set X} {p : X}
    (hCclosed : IsClosed C) (hCregular : closure (interior C) = C)
    (hCregion : C ⊆ closure R) (hpC : p ∈ C) (hW : IsOpen W) (hpW : p ∈ W)
    (hconnected : IsPreconnected (W ∩ R))
    (hfrontier : Disjoint (W ∩ R) (frontier C)) :
    W ∩ R ⊆ interior C ∧ W ∩ closure R ⊆ C := by
  have hpclosure : p ∈ closure (interior C) := hCregular.symm ▸ hpC
  obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.mp hpclosure W hW hpW
  have hzclosure : z ∈ closure R := hCregion (interior_subset hzC)
  obtain ⟨q, ⟨hqW, hqC⟩, hqR⟩ :=
    mem_closure_iff.mp hzclosure (W ∩ interior C) (hW.inter isOpen_interior) ⟨hzW, hzC⟩
  have hside : W ∩ R ⊆ interior C :=
    preconnected_subset_interior_of_disjoint_frontier hconnected hfrontier ⟨q, ⟨hqW, hqR⟩, hqC⟩
  exact ⟨hside, hW.inter_closure.trans
    (closure_minimal (hside.trans interior_subset) hCclosed)⟩

end Poincare.Topology

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))





theorem exists_region_closure_neighborhood_of_frontier_subset_within
    (e : D.EdgeIndex) (q : D.regions) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {C L : Set M} (hCclosed : IsClosed C) (hCregular : closure (interior C) = C)
    (hCregion : C ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ q))
    (hpC : (D.edge e.1 e.2).map t ∈ C)
    (hL : IsClosed L) (hpL : (D.edge e.1 e.2).map t ∉ L)
    (hfrontier : frontier C ⊆ chartDiskBoundaryUnion D.centers D.radius ∪ L)
    {N : Set M} (hN : N ∈ 𝓝 ((D.edge e.1 e.2).map t)) :
    ∃ W : Set M, IsOpen W ∧ (D.edge e.1 e.2).map t ∈ W ∧ W ⊆ N ∧
      W ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (e.1.1 : M)).source ∧ Disjoint W L ∧
      W ∩ connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ q ⊆ interior C ∧
      W ∩ closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ q) ⊆ C := by
  let K := chartDiskBoundaryUnion D.centers D.radius
  let R := connectedComponentIn Kᶜ q
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (e.1.1 : M)
  have hsource : (D.edge e.1 e.2).map '' Icc (0 : ℝ) 1 ⊆ c.source := by
    rintro p ⟨s, hs, rfl⟩
    rw [D.edge_map_eq e s]
    exact c.map_target (D.edgeCurve_target e ⟨s, hs, rfl⟩)
  have hpchart : (D.edge e.1 e.2).map t ∈ c.source :=
    hsource ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  have hsmall : N ∩ (c.source ∩ Lᶜ) ∈ 𝓝 ((D.edge e.1 e.2).map t) :=
    Filter.inter_mem hN (Filter.inter_mem (c.open_source.mem_nhds hpchart)
      (hL.isOpen_compl.mem_nhds hpL))
  obtain ⟨W, U, V, hW, hpW, hWsmall, _, _, hU, hV, _, hpartition, hpUV⟩ :=
    exists_two_sided_edge_family_neighborhood_of_endpoint_intersections
      (fun a : D.EdgeIndex => D.edge a.1 a.2) e (e.1.1 : M)
      (D.edge_injective e.1 e.2) hsource
      (fun a hae _ hz => (D.edge_intersection e a hae.symm hz).1) ht hsmall
  rw [D.boundary_cover] at hpartition
  obtain ⟨upper, lower, _, hpair, _, _, hupper, hlower⟩ :=
    D.exists_regions_of_two_sided_neighborhood e ht (hW.mem_nhds hpW) hpartition
      hU.isConnected.isPreconnected hV.isConnected.isPreconnected hU.nonempty hV.nonempty
      hpUV.1 hpUV.2
  have hpK : (D.edge e.1 e.2).map t ∈ K := by
    dsimp only [K]
    rw [← D.boundary_cover]
    exact mem_iUnion.mpr ⟨e, t, Ioo_subset_Icc_self ht, rfl⟩
  have hincident : q = D.regionLeft e ∨ q = D.regionRight e := by
    apply (D.edge_interior_incidence e t ht q).mp
    refine ⟨hCregion hpC, ?_⟩
    intro hpint
    exact connectedComponentIn_subset _ _ (interior_subset hpint) hpK
  have hconnected : IsPreconnected (W ∩ R) := by
    rcases (hpair q).mpr hincident with hq | hq
    · change IsPreconnected (W ∩ connectedComponentIn Kᶜ q)
      rw [hq, hupper]
      exact hU.isConnected.isPreconnected
    · change IsPreconnected (W ∩ connectedComponentIn Kᶜ q)
      rw [hq, hlower]
      exact hV.isConnected.isPreconnected
  have havoid : Disjoint (W ∩ R) (frontier C) := by
    apply disjoint_left.mpr
    rintro z ⟨hzW, hzR⟩ hzfront
    rcases hfrontier hzfront with hzK | hzL
    · exact connectedComponentIn_subset _ _ hzR hzK
    · exact (hWsmall hzW).2.2 hzL
  obtain ⟨hinterior, hclosure⟩ := Poincare.Topology.local_region_subset_of_regular_closed
    hCclosed hCregular hCregion hpC hW hpW hconnected havoid
  exact ⟨W, hW, hpW, fun _ hz => (hWsmall hz).1, fun _ hz => (hWsmall hz).2.1,
    disjoint_left.mpr (fun z hzW hzL => (hWsmall hzW).2.2 hzL), hinterior, hclosure⟩



theorem exists_region_closure_neighborhood_of_frontier_subset
    (e : D.EdgeIndex) (q : D.regions) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {C L : Set M} (hCclosed : IsClosed C) (hCregular : closure (interior C) = C)
    (hCregion : C ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ q))
    (hpC : (D.edge e.1 e.2).map t ∈ C)
    (hL : IsClosed L) (hpL : (D.edge e.1 e.2).map t ∉ L)
    (hfrontier : frontier C ⊆ chartDiskBoundaryUnion D.centers D.radius ∪ L) :
    ∃ W : Set M, IsOpen W ∧ (D.edge e.1 e.2).map t ∈ W ∧
      W ∩ closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ q) ⊆ C := by
  obtain ⟨W, hW, hpW, _, _, _, _, hcover⟩ :=
    D.exists_region_closure_neighborhood_of_frontier_subset_within e q ht
      hCclosed hCregular hCregion hpC hL hpL hfrontier (N := univ) Filter.univ_mem
  exact ⟨W, hW, hpW, hcover⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
