


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.RefinementIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Assembly







set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface.Euler

theorem affineChartSegment_image (a b : Plane) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

theorem affineChartSegment_eq_lineMap (a b : Plane) (t : ℝ) :
    affineChartSegment a b t = AffineMap.lineMap a b t := by
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

theorem coordinate_edge_subset_hull (b : AffineBasis (Fin 3) ℝ Plane) (k : Fin 3) :
    affineSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) ⊆ convexHull ℝ (range b) := by
  rw [affineSegment_eq_segment]
  exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)

theorem coordinate_edge_subset_frontier (b : AffineBasis (Fin 3) ℝ Plane) (k : Fin 3) :
    affineSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) ⊆
      frontier (convexHull ℝ (range b)) := by
  rw [frontier_convexHull_affineBasis_fin3_segments]
  intro z hz
  exact mem_iUnion.mpr ⟨k, hz⟩

theorem coordinate_vertices_subset_frontier (b : AffineBasis (Fin 3) ℝ Plane) :
    range b ⊆ frontier (convexHull ℝ (range b)) := by
  rintro z ⟨v, rfl⟩
  fin_cases v
  · exact coordinate_edge_subset_frontier b 1 (by
      rw [← affineChartSegment_image]
      exact ⟨0, by simp, by simp [affineChartSegment]⟩)
  · exact coordinate_edge_subset_frontier b 0 (by
      rw [← affineChartSegment_image]
      exact ⟨0, by simp, by simp [affineChartSegment]⟩)
  · exact coordinate_edge_subset_frontier b 0 (by
      rw [← affineChartSegment_image]
      exact ⟨1, by simp, by simp [affineChartSegment]⟩)

universe u v

variable {M : Type u} [TopologicalSpace M]

theorem coordinate_vertex_on_edge
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (k v : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (heq : F (affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) t) = F (b v)) :
    t = 0 ∨ t = 1 := by
  have hseg := coordinate_edge_subset_hull b k
    (affineChartSegment_image _ _ ▸ mem_image_of_mem _ ht)
  have h := congrArg (b.coord (k.succAbove 1))
    (F.injOn (hsource hseg) (hsource (subset_convexHull ℝ _ (mem_range_self v))) heq)
  rw [affineChartSegment_eq_lineMap, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring] at h
  have hne : k.succAbove 1 ≠ k.succAbove 0 := by
    intro h
    have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective h
    norm_num at h10
  rw [b.coord_apply_ne hne, b.coord_apply_eq, b.coord_apply] at h
  split_ifs at h <;> simp_all

theorem coordinate_distinct_edges
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (k l : Fin 3) (hkl : k ≠ l) :
    ((F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1) ∩
      ((F ∘ affineChartSegment (b (l.succAbove 0)) (b (l.succAbove 1))) '' Icc (0 : ℝ) 1) ⊆
      {F (b (k.succAbove 0)), F (b (k.succAbove 1))} := by
  rintro q ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
  have hsrc (i : Fin 3) (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) w ∈ F.source :=
    hsource (coordinate_edge_subset_hull b i
      (affineChartSegment_image _ _ ▸ mem_image_of_mem _ hw))
  have h := congrArg (b.coord l) (F.injOn (hsrc l t ht) (hsrc k s hs) heq)
  simp only [affineChartSegment_eq_lineMap, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring, b.coord_apply] at h
  have hend : s = 0 ∨ s = 1 := by
    fin_cases k <;> fin_cases l
    all_goals first | exact (hkl rfl).elim |
      (norm_num [Fin.succAbove, Fin.lt_def, Fin.ext_iff] at h
       first | (left; linarith) | (right; linarith))
  rcases hend with rfl | rfl <;> simp [affineChartSegment]

theorem coordinate_edge_images_injective
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) :
    Function.Injective (fun k : Fin 3 =>
      (F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1) := by
  intro k l heq
  dsimp only at heq
  by_contra hkl
  have ht : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hk := mem_image_of_mem
    (F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) ht
  have hl := heq ▸ hk
  have hend := coordinate_distinct_edges F b hsource k l hkl ⟨hk, hl⟩
  rcases hend with hzero | hone
  · have := coordinate_vertex_on_edge F b hsource k (k.succAbove 0) ht hzero
    norm_num at this
  · have := coordinate_vertex_on_edge F b hsource k (k.succAbove 1) ht
      (mem_singleton_iff.mp hone)
    norm_num at this

variable [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

theorem equal_coordinate_edge_endpoints_mem
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (k : Fin 3) (edge : SmoothEdge M)
    (hinj : InjOn edge.map (Icc (0 : ℝ) 1))
    (himage : edge.map '' Icc (0 : ℝ) 1 =
      (F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1) :
    edge.map 0 ∈ ({F (b (k.succAbove 0)), F (b (k.succAbove 1))} : Set M) ∧
      edge.map 1 ∈ ({F (b (k.succAbove 0)), F (b (k.succAbove 1))} : Set M) := by
  let e := F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))
  let param : M → ℝ := fun q => b.coord (k.succAbove 1) (F.symm q)
  let f := param ∘ edge.map
  have hsrc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) t ∈ F.source :=
    hsource (coordinate_edge_subset_hull b k
      (affineChartSegment_image _ _ ▸ mem_image_of_mem _ ht))
  have hparam (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : param (e t) = t := by
    dsimp only [param, e, Function.comp_apply]
    rw [F.left_inv (hsrc t ht), affineChartSegment_eq_lineMap,
      AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    have hne : k.succAbove 1 ≠ k.succAbove 0 := by
      intro h
      have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective h
      norm_num at h10
    rw [b.coord_apply_ne hne, b.coord_apply_eq]
    ring
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f t ∈ Icc (0 : ℝ) 1 ∧ e (f t) = edge.map t := by
    obtain ⟨s, hs, heq⟩ := himage ▸ mem_image_of_mem edge.map ht
    have hfs : f t = s := by change param (edge.map t) = s; rw [← heq, hparam s hs]
    exact ⟨hfs ▸ hs, by rw [hfs]; exact heq⟩
  have htarget : MapsTo edge.map (Icc (0 : ℝ) 1) F.target := by
    intro t ht
    rw [← (hf t ht).2]
    exact F.map_source (hsrc _ (hf t ht).1)
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (continuous_barycentric_coord b (k.succAbove 1)).comp_continuousOn
      (F.symm.continuousOn.comp edge.smooth.continuousOn htarget)
  have hfi : InjOn f (Icc (0 : ℝ) 1) := by
    intro s hs t ht heq
    apply hinj hs ht
    rw [← (hf s hs).2, ← (hf t ht).2, heq]
  have hsurj (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : ∃ t ∈ Icc (0 : ℝ) 1, f t = v := by
    have hev : e v ∈ edge.map '' Icc (0 : ℝ) 1 := by rw [himage]; exact mem_image_of_mem e hv
    obtain ⟨t, ht, heq⟩ := hev
    exact ⟨t, ht, by change param (edge.map t) = v; rw [heq, hparam v hv]⟩
  obtain ⟨s, hs, hs0⟩ := hsurj 0 (by simp)
  obtain ⟨t, ht, ht1⟩ := hsurj 1 (by simp)
  have hz : (0 : ℝ) ∈ Icc 0 1 := by simp
  have ho : (1 : ℝ) ∈ Icc 0 1 := by simp
  have hend : (f 0 = 0 ∧ f 1 = 1) ∨ (f 0 = 1 ∧ f 1 = 0) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' (by norm_num) hfi with hmono | hanti
    · left
      constructor
      · have hle := hmono.monotoneOn hz hs hs.1
        rw [hs0] at hle
        exact le_antisymm hle (hf 0 hz).1.1
      · have hle := hmono.monotoneOn ht ho ht.2
        rw [ht1] at hle
        exact le_antisymm (hf 1 ho).1.2 hle
    · right
      constructor
      · have hle := hanti.antitoneOn hz ht ht.1
        rw [ht1] at hle
        exact le_antisymm (hf 0 hz).1.2 hle
      · have hle := hanti.antitoneOn hs ho hs.2
        rw [hs0] at hle
        exact le_antisymm hle (hf 1 ho).1.1
  rw [← (hf 0 (by simp)).2, ← (hf 1 (by simp)).2]
  rcases hend with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;>
    simp [e, affineChartSegment]

theorem equal_coordinate_edge_endpoint_sets
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (k : Fin 3) (edge : SmoothEdge M)
    (hinj : InjOn edge.map (Icc (0 : ℝ) 1))
    (himage : edge.map '' Icc (0 : ℝ) 1 =
      (F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1) :
    ({edge.map 0, edge.map 1} : Set M) =
      {F (b (k.succAbove 0)), F (b (k.succAbove 1))} := by
  have hne : edge.map 0 ≠ edge.map 1 := by
    intro h
    have := hinj (by simp) (by simp) h
    norm_num at this
  obtain ⟨hzero, hone⟩ := equal_coordinate_edge_endpoints_mem F b hsource k edge hinj himage
  simp only [mem_insert_iff, mem_singleton_iff] at hzero hone
  rcases hzero with hzero | hzero <;> rcases hone with hone | hone
  · exact (hne (hzero.trans hone.symm)).elim
  · rw [hzero, hone]
  · rw [hzero, hone, pair_comm]
  · exact (hne (hzero.trans hone.symm)).elim

theorem coordinate_cover_edge_meet
    [T2Space M] {I : Type v} (face : I → SmoothFace M)
    (F : I → OpenPartialHomeomorph Plane M) (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (i j : I) (k l : Fin 3)
    (hne : ((face i).boundary k).map '' Icc (0 : ℝ) 1 ≠
      ((face j).boundary l).map '' Icc (0 : ℝ) 1) :
    (((face i).boundary k).map '' Icc (0 : ℝ) 1) ∩
      (((face j).boundary l).map '' Icc (0 : ℝ) 1) ⊆
      {((face i).boundary k).map 0, ((face i).boundary k).map 1} := by
  have hend (i : I) (k : Fin 3) :
      ({((face i).boundary k).map 0, ((face i).boundary k).map 1} : Set M) =
        {F i (b i (k.succAbove 0)), F i (b i (k.succAbove 1))} := by
    simp [hboundary, affineChartSegment]
  have hinc (i : I) (k : Fin 3) :
      ((face i).boundary k).map '' Icc (0 : ℝ) 1 ⊆ (face i).carrier :=
    ((face i).boundary_image_subset_frontier k).trans (face i).isClosed_carrier.frontier_subset
  have hsame (i : I) (k l : Fin 3) (hkl : k ≠ l) :
      (((face i).boundary k).map '' Icc (0 : ℝ) 1) ∩
        (((face i).boundary l).map '' Icc (0 : ℝ) 1) ⊆
        {((face i).boundary k).map 0, ((face i).boundary k).map 1} := by
    rw [hend, hboundary, hboundary]
    exact coordinate_distinct_edges (F i) (b i) (hsource i) k l hkl
  by_cases hij : i = j
  · subst j
    exact hsame i k l (fun hkl => hne (hkl ▸ rfl))
  intro q hq
  have hqcarrier : q ∈ (face i).carrier ∩ (face j).carrier := ⟨hinc i k hq.1, hinc j l hq.2⟩
  rcases hinter i j hij with ⟨k', l', hk, hl⟩ | ⟨w, hw⟩
  · have hqi : q ∈ ((face i).boundary k').map '' Icc (0 : ℝ) 1 := hk ▸ hqcarrier
    have hqj : q ∈ ((face j).boundary l').map '' Icc (0 : ℝ) 1 := hl ▸ hqi
    by_cases hkk : k = k'
    · subst k'
      have hll : l' ≠ l := fun h => hne (h ▸ hl)
      have hqend := hsame j l' l hll ⟨hqj, hq.2⟩
      obtain ⟨hzero, hone⟩ := equal_coordinate_edge_endpoints_mem (F i) (b i)
        (hsource i) k ((face j).boundary l') (hinj j l') (by rw [← hboundary]; exact hl.symm)
      rw [hend]
      rcases hqend with hq0 | hq1
      · exact hq0 ▸ hzero
      · exact hq1 ▸ hone
    · exact hsame i k k' hkk ⟨hq.1, hqi⟩
  · obtain ⟨t, ht, htq⟩ := hq.1
    have htvertex : F i (affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)) t) =
        F i (b i w) := by
      change (F i ∘ affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1))) t = _
      rw [← hboundary, htq]
      exact mem_singleton_iff.mp (hw hqcarrier)
    rcases coordinate_vertex_on_edge (F i) (b i) (hsource i) k w ht htvertex with rfl | rfl
    · exact Or.inl htq.symm
    · exact Or.inr (mem_singleton_iff.mpr htq.symm)

end PoincareConjecture.Topology.Surface.Euler
