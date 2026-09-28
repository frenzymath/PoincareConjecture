import PoincareConjecture.Proofs.Horizon.Topology.Connected.TwoSidedUnion
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Interior
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface

private theorem affineChartSegment_mem_triangle
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (i : Fin 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈
      convexHull ℝ (range b) := by
  apply segment_subset_convexHull (mem_range_self (i.succAbove 0))
    (mem_range_self (i.succAbove 1))
  rw [← affineSegment_eq_segment]
  refine ⟨t, ht, ?_⟩
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem coord_affineChartSegment
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (i j k : Fin 3) (t : ℝ) :
    b.coord i (affineChartSegment (b j) (b k) t) =
      (1 - t) * (if i = j then 1 else 0) + t * (if i = k then 1 else 0) := by
  have heq : affineChartSegment (b j) (b k) t = AffineMap.lineMap (b j) (b k) t := by
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
  rw [heq, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
    b.coord_apply, b.coord_apply]

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] in

theorem coordinate_triangle_boundary_avoids_other_edges
    (f : SmoothFace M) (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (hboundary : ∀ i : Fin 3, (f.boundary i).map = F ∘
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)))
    {i j : Fin 3} (hij : i ≠ j) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (f.boundary i).map t ∉ (f.boundary j).map '' Icc (0 : ℝ) 1 := by
  rintro ⟨s, hs, heq⟩
  rw [hboundary i, hboundary j] at heq
  have h := F.injOn (hsource (affineChartSegment_mem_triangle b j hs))
    (hsource (affineChartSegment_mem_triangle b i ⟨ht.1.le, ht.2.le⟩)) heq
  have hc := congrArg (b.coord j) h
  rw [coord_affineChartSegment, coord_affineChartSegment] at hc
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def] at hc <;>
    linarith [ht.1, ht.2]

theorem SmoothFace.mem_interior_union_of_shared_edge
    (f g : SmoothFace M) (i j : Fin 3)
    (hfregular : closure (interior f.carrier) = f.carrier)
    (hgregular : closure (interior g.carrier) = g.carrier)
    (hinter : f.carrier ∩ g.carrier ⊆ frontier f.carrier)
    (hinj : InjOn (f.boundary i).map (Icc (0 : ℝ) 1))
    (hagreement : EqOn (f.boundary i).map (g.boundary j).map (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (havoidf : ∀ k, k ≠ i → (f.boundary i).map t ∉ (f.boundary k).map '' Icc (0 : ℝ) 1)
    (havoidg : ∀ k, k ≠ j → (g.boundary j).map t ∉ (g.boundary k).map '' Icc (0 : ℝ) 1) :
    (f.boundary i).map t ∈ interior (f.carrier ∪ g.carrier) := by
  let Kf : Set M := ⋃ k : {k : Fin 3 // k ≠ i}, (f.boundary k).map '' Icc (0 : ℝ) 1
  let Kg : Set M := ⋃ k : {k : Fin 3 // k ≠ j}, (g.boundary k).map '' Icc (0 : ℝ) 1
  have hKf : IsCompact Kf := isCompact_iUnion (fun k =>
    isCompact_Icc.image_of_continuousOn (f.boundary k).smooth.continuousOn)
  have hKg : IsCompact Kg := isCompact_iUnion (fun k =>
    isCompact_Icc.image_of_continuousOn (g.boundary k).smooth.continuousOn)
  have hteq := hagreement ⟨ht.1.le, ht.2.le⟩
  have hnot : (f.boundary i).map t ∉ Kf ∪ Kg := by
    rintro (hf | hg)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hf
      exact havoidf k k.property hk
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hg
      rw [hteq] at hk
      exact havoidg k k.property hk
  have hchart : (f.boundary i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) f.chart).source :=
    (f.boundary_image_subset_frontier i).trans
      (f.isClosed_carrier.frontier_subset.trans f.carrier_subset_chart)
  obtain ⟨W, U, V, hWopen, htW, hWsub, _, _, hUpath, hVpath, _, hpartition, _⟩ :=
    (f.boundary i).exists_two_sided_neighborhood f.chart hinj hchart ht
      ((hKf.union hKg).isClosed.isOpen_compl.mem_nhds hnot)
  have hfrontf : W ∩ frontier f.carrier ⊆ (f.boundary i).map '' Icc (0 : ℝ) 1 := by
    rintro q ⟨hqW, hqf⟩
    rw [f.boundary_carrier] at hqf
    obtain ⟨k, hk⟩ := mem_iUnion.mp hqf
    by_cases hki : k = i
    · simpa only [hki] using hk
    · exact False.elim (hWsub hqW (Or.inl (mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩)))
  have hfrontg : W ∩ frontier g.carrier ⊆ (f.boundary i).map '' Icc (0 : ℝ) 1 := by
    rintro q ⟨hqW, hqg⟩
    rw [g.boundary_carrier] at hqg
    obtain ⟨k, hk⟩ := mem_iUnion.mp hqg
    by_cases hkj : k = j
    · subst k
      rw [image_congr hagreement]
      exact hk
    · exact False.elim (hWsub hqW (Or.inr (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩)))
  have hdense : Dense ((f.boundary i).map '' Icc (0 : ℝ) 1)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (f.interior_boundary_image i)
  have hWdense : W ⊆ closure (U ∪ V) := by
    rw [← hpartition]
    intro q hq
    apply mem_closure_iff.mpr
    intro O hO hqO
    obtain ⟨z, ⟨hzO, hzW⟩, hzK⟩ :=
      hdense.inter_open_nonempty (O ∩ W) (hO.inter hWopen) ⟨q, hqO, hq⟩
    exact ⟨z, hzO, hzW, hzK⟩
  have htf : (f.boundary i).map t ∈ f.carrier := f.isClosed_carrier.frontier_subset
    (f.boundary_image_subset_frontier i ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
  have htg : (f.boundary i).map t ∈ g.carrier := by
    rw [hteq]
    exact g.isClosed_carrier.frontier_subset
      (g.boundary_image_subset_frontier j ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
  have hcover := Poincare.Topology.subset_union_of_two_sided_neighborhood
    f.isClosed_carrier g.isClosed_carrier hfregular hgregular
    (f.disjoint_interiors_of_inter_subset_frontier g hinter) htf htg
    (hWopen.mem_nhds htW) hpartition hUpath.isConnected.isPreconnected
    hVpath.isConnected.isPreconnected hUpath.nonempty hVpath.nonempty hWdense hfrontf hfrontg
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hWopen.mem_nhds htW) hcover)

theorem mem_interior_union_of_coordinate_triangles_shared_edge
    (f g : SmoothFace M)
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hFsource : convexHull ℝ (range b) ⊆ F.source)
    (hGsource : convexHull ℝ (range c) ⊆ G.source)
    (hfcarrier : f.carrier = F '' convexHull ℝ (range b))
    (hgcarrier : g.carrier = G '' convexHull ℝ (range c))
    (hfboundary : ∀ k : Fin 3, (f.boundary k).map = F ∘
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    (hgboundary : ∀ k : Fin 3, (g.boundary k).map = G ∘
      affineChartSegment (c (k.succAbove 0)) (c (k.succAbove 1)))
    (hinter : f.carrier ∩ g.carrier ⊆ frontier f.carrier)
    (i j : Fin 3) (hinj : InjOn (f.boundary i).map (Icc (0 : ℝ) 1))
    (hagreement : EqOn (f.boundary i).map (g.boundary j).map (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (f.boundary i).map t ∈ interior (f.carrier ∪ g.carrier) := by
  refine f.mem_interior_union_of_shared_edge g i j ?_ ?_ hinter hinj hagreement ht ?_ ?_
  · rw [hfcarrier]
    exact coordinate_triangle_closure_interior F b hFsource
  · rw [hgcarrier]
    exact coordinate_triangle_closure_interior G c hGsource
  · intro k hki
    exact coordinate_triangle_boundary_avoids_other_edges f F b hFsource hfboundary hki.symm ht
  · intro k hkj
    exact coordinate_triangle_boundary_avoids_other_edges g G c hGsource hgboundary hkj.symm ht

end PoincareConjecture.Topology.Surface
