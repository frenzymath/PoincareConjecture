


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.RefinementIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Assembly
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.RefinementData







set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

private theorem compatibleCover_segment_image (a b : Plane) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem compatibleCover_segment_eq_lineMap (a b : Plane) (t : ℝ) :
    affineChartSegment a b t = AffineMap.lineMap a b t := by
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem compatibleCover_edge_subset (b : AffineBasis (Fin 3) ℝ Plane) (k : Fin 3) :
    affineSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) ⊆ convexHull ℝ (range b) := by
  rw [affineSegment_eq_segment]
  exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)

private theorem compatibleCover_edge_frontier (b : AffineBasis (Fin 3) ℝ Plane) (k : Fin 3) :
    affineSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) ⊆
      frontier (convexHull ℝ (range b)) := by
  rw [frontier_convexHull_affineBasis_fin3_segments]
  intro z hz
  exact mem_iUnion.mpr ⟨k, hz⟩

private theorem compatibleCover_vertex_frontier (b : AffineBasis (Fin 3) ℝ Plane) :
    range b ⊆ frontier (convexHull ℝ (range b)) := by
  rintro z ⟨v, rfl⟩
  fin_cases v
  · exact compatibleCover_edge_frontier b 1 (by
      rw [← compatibleCover_segment_image]
      exact ⟨0, by simp, by simp [affineChartSegment]⟩)
  · exact compatibleCover_edge_frontier b 0 (by
      rw [← compatibleCover_segment_image]
      exact ⟨0, by simp, by simp [affineChartSegment]⟩)
  · exact compatibleCover_edge_frontier b 0 (by
      rw [← compatibleCover_segment_image]
      exact ⟨1, by simp, by simp [affineChartSegment]⟩)

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M] in
private theorem compatibleCover_vertex_on_edge
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (k v : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (heq : F (affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) t) = F (b v)) :
    t = 0 ∨ t = 1 := by
  have hseg := compatibleCover_edge_subset b k
    (compatibleCover_segment_image _ _ ▸ mem_image_of_mem _ ht)
  have h := congrArg (b.coord (k.succAbove 1))
    (F.injOn (hsource hseg) (hsource (subset_convexHull ℝ _ (mem_range_self v))) heq)
  rw [compatibleCover_segment_eq_lineMap, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring] at h
  have hne : k.succAbove 1 ≠ k.succAbove 0 := by
    intro h
    have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective h
    norm_num at h10
  rw [b.coord_apply_ne hne, b.coord_apply_eq, b.coord_apply] at h
  split_ifs at h <;> simp_all

omit [T2Space M] [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M] in
private theorem compatibleCover_distinct_edges
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (k l : Fin 3) (hkl : k ≠ l) :
    ((F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1) ∩
      ((F ∘ affineChartSegment (b (l.succAbove 0)) (b (l.succAbove 1))) '' Icc (0 : ℝ) 1) ⊆
      {F (b (k.succAbove 0)), F (b (k.succAbove 1))} := by
  rintro q ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
  have hsrc (i : Fin 3) (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) w ∈ F.source :=
    hsource (compatibleCover_edge_subset b i
      (compatibleCover_segment_image _ _ ▸ mem_image_of_mem _ hw))
  have h := congrArg (b.coord l) (F.injOn (hsrc l t ht) (hsrc k s hs) heq)
  simp only [compatibleCover_segment_eq_lineMap, AffineMap.apply_lineMap,
    AffineMap.lineMap_apply_ring, b.coord_apply] at h
  have hend : s = 0 ∨ s = 1 := by
    fin_cases k <;> fin_cases l
    all_goals first | exact (hkl rfl).elim |
      (norm_num [Fin.succAbove, Fin.lt_def, Fin.ext_iff] at h
       first | (left; linarith) | (right; linarith))
  rcases hend with rfl | rfl <;> simp [affineChartSegment]

omit [T2Space M] in
private theorem compatibleCover_equal_edge_endpoints
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
    hsource (compatibleCover_edge_subset b k
      (compatibleCover_segment_image _ _ ▸ mem_image_of_mem _ ht))
  have hparam (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : param (e t) = t := by
    dsimp only [param, e, Function.comp_apply]
    rw [F.left_inv (hsrc t ht), compatibleCover_segment_eq_lineMap,
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

private theorem compatibleCover_assemble
    {I : Type v} [Finite I] (face : I → SmoothFace M)
    (F : I → OpenPartialHomeomorph Plane M) (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFinv : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (hcover : (⋃ i, (face i).carrier) = univ) :
    Nonempty (FiniteSmoothTriangulationWithCoordinates (M := M)) := by
  classical
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
    exact compatibleCover_distinct_edges (F i) (b i) (hsource i) k l hkl
  have hmeet (i j : I) (k l : Fin 3)
      (hne : ((face i).boundary k).map '' Icc (0 : ℝ) 1 ≠
        ((face j).boundary l).map '' Icc (0 : ℝ) 1) :
      (((face i).boundary k).map '' Icc (0 : ℝ) 1) ∩
        (((face j).boundary l).map '' Icc (0 : ℝ) 1) ⊆
        {((face i).boundary k).map 0, ((face i).boundary k).map 1} := by
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
        obtain ⟨hzero, hone⟩ := compatibleCover_equal_edge_endpoints (F i) (b i)
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
      rcases compatibleCover_vertex_on_edge (F i) (b i) (hsource i) k w ht htvertex with rfl | rfl
      · exact Or.inl htq.symm
      · exact Or.inr (mem_singleton_iff.mpr htq.symm)
  let vertices : Finset M := (finite_range (fun p : I × Fin 3 => F p.1 (b p.1 p.2))).toFinset
  apply nonempty_finiteSmoothTriangulationWithCoordinates_of_coordinate_triangle_cover
    (normalizeFaceBoundary face) (faceBoundaryEdge face) (faceBoundaryIndex face)
    (normalizeFaceBoundary_boundary face) ?_ ?_ ?_ F b hF hFinv hsource hcarrier ?_ hfront hcover vertices ?_
  · intro i
    exact ⟨i.out.1, i.out.2, Quotient.out_eq i⟩
  · intro e
    exact hinj e.out.1 e.out.2
  · intro e d hed
    apply hmeet e.out.1 d.out.1 e.out.2 d.out.2
    intro heq
    apply hed
    have h := (faceBoundaryIndex_eq_iff face e.out.1 d.out.1 e.out.2 d.out.2).mpr heq
    exact (Quotient.out_eq e).symm.trans (h.trans (Quotient.out_eq d))
  · intro i k
    rw [normalizeFaceBoundary_boundary, faceBoundaryEdge_image, hboundary]
    rw [image_comp, compatibleCover_segment_image]
  · intro i j hij
    rcases hinter i j hij with ⟨k, l, hk, _⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨faceBoundaryIndex face i k, by rw [faceBoundaryEdge_image]; exact hk⟩
    · refine Or.inr ⟨F i (b i w), ?_, hw⟩
      exact (Set.Finite.mem_toFinset _).mpr ⟨(i, w), rfl⟩



inductive CoordinateTriangleBoundaryIntersection
    (F G : OpenPartialHomeomorph Plane M) (b c : AffineBasis (Fin 3) ℝ Plane) : Prop
  | disjoint
      (h : Disjoint (F '' convexHull ℝ (range b)) (G '' convexHull ℝ (range c)))
  | point (q : M)
      (hF : q ∈ F '' frontier (convexHull ℝ (range b)))
      (hG : q ∈ G '' frontier (convexHull ℝ (range c)))
      (h : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆ {q})
  | subsegment (i j : Fin 3) (a d a' d' : ℝ)
      (ha : a ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
      (ha' : a' ∈ Icc (0 : ℝ) 1) (hd' : d' ∈ Icc (0 : ℝ) 1)
      (hF : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
        (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a d)
      (hG : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
        (G ∘ affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1))) '' uIcc a' d')

namespace CoordinateTriangleBoundaryIntersection

variable {F G : OpenPartialHomeomorph Plane M} {b c : AffineBasis (Fin 3) ℝ Plane}

omit [T2Space M] [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M] in
theorem symm (h : CoordinateTriangleBoundaryIntersection F G b c) :
    CoordinateTriangleBoundaryIntersection G F c b := by
  cases h with
  | disjoint hd => exact .disjoint hd.symm
  | point q hF hG hq => exact .point q hG hF (by simpa only [inter_comm] using hq)
  | subsegment i j a d a' d' ha hd ha' hd' hF hG =>
      exact .subsegment j i a' d' a d ha' hd' ha hd
        (by simpa only [inter_comm] using hG) (by simpa only [inter_comm] using hF)

omit [T2Space M] [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M] in
theorem subset_frontiers (h : CoordinateTriangleBoundaryIntersection F G b c) :
    (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆
      (F '' frontier (convexHull ℝ (range b))) ∩ (G '' frontier (convexHull ℝ (range c))) := by
  cases h with
  | disjoint hd => rw [disjoint_iff_inter_eq_empty.mp hd]; exact empty_subset _
  | point q hF hG hq =>
      intro p hp
      rw [mem_singleton_iff.mp (hq hp)]
      exact ⟨hF, hG⟩
  | subsegment i j a d a' d' ha hd ha' hd' hF hG =>
      have hedge (K : OpenPartialHomeomorph Plane M) (B : AffineBasis (Fin 3) ℝ Plane)
          (k : Fin 3) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
          (K ∘ affineChartSegment (B (k.succAbove 0)) (B (k.succAbove 1))) '' uIcc s t ⊆
            K '' frontier (convexHull ℝ (range B)) := by
        rintro p ⟨v, hv, rfl⟩
        apply mem_image_of_mem K
        apply compatibleCover_edge_frontier B k
        rw [← compatibleCover_segment_image]
        exact mem_image_of_mem _ ⟨(le_min hs.1 ht.1).trans hv.1, hv.2.trans (max_le hs.2 ht.2)⟩
      intro p hp
      exact ⟨hedge F b i ha hd (hF ▸ hp), hedge G c j ha' hd' (hG ▸ hp)⟩



theorem exists_marks (h : CoordinateTriangleBoundaryIntersection F G b c) :
    ∃ P : Finset M,
      (P : Set M) ⊆ (F '' frontier (convexHull ℝ (range b))) ∩
        (G '' frontier (convexHull ℝ (range c))) ∧
      ∀ (S T : Finset M), (P : Set M) ⊆ S → (P : Set M) ⊆ T →
      ∀ (R : SmoothTriangleBoundarySubdivision F b S) (Q : SmoothTriangleBoundarySubdivision G c T),
      (S : Set M) ∩ (G '' convexHull ℝ (range c)) =
        (T : Set M) ∩ (F '' convexHull ℝ (range b)) →
      ∀ (t : R.mesh.Triangle) (u : Q.mesh.Triangle),
      ((∃ k l : Fin 3, (R.face t).carrier ∩ (Q.face u).carrier =
            ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ∧
          ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 =
            ((Q.face u).boundary l).map '' Icc (0 : ℝ) 1) ∨
        ∃ v : Fin 3, (R.face t).carrier ∩ (Q.face u).carrier ⊆
          {F (meshTriangleBasis R.mesh t v)}) ∧
      (R.face t).carrier ∩ (Q.face u).carrier ⊆
        frontier (R.face t).carrier ∩ frontier (Q.face u).carrier := by
  classical
  cases h with
  | disjoint hd =>
      refine ⟨∅, by simp, ?_⟩
      intro S T _ _ R Q _ t u
      have hempty := disjoint_iff_inter_eq_empty.mp
        (R.disjoint_children_of_disjoint_parents Q hd t u)
      exact ⟨Or.inr ⟨0, by rw [hempty]; exact empty_subset _⟩,
        by rw [hempty]; exact empty_subset _⟩
  | point q hF hG hq =>
      refine ⟨{q}, ?_, ?_⟩
      · simpa only [Finset.coe_singleton, singleton_subset_iff, mem_inter_iff] using And.intro hF hG
      · intro S T hS hT R Q _ t u
        obtain ⟨hp, hf⟩ := R.cross_intersections_of_marked_parent_point Q hq
          (hS (by simp)) (hT (by simp)) t u
        exact ⟨Or.inr hp, hf⟩
  | subsegment i j a d a' d' ha hd ha' hd' hF hG =>
      let e := F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))
      let f := G ∘ affineChartSegment (c (j.succAbove 0)) (c (j.succAbove 1))
      let P : Finset M := {e a, e d, f a', f d'}
      have hP : (P : Set M) ⊆
          (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) := by
        intro p hp
        change p ∈ P at hp
        simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · rw [hF]; exact mem_image_of_mem e left_mem_uIcc
        · rw [hF]; exact mem_image_of_mem e right_mem_uIcc
        · rw [hG]; exact mem_image_of_mem f left_mem_uIcc
        · rw [hG]; exact mem_image_of_mem f right_mem_uIcc
      refine ⟨P, hP.trans (subset_frontiers (.subsegment i j a d a' d' ha hd ha' hd' hF hG)), ?_⟩
      intro S T hS hT R Q hsync t u
      exact R.cross_intersections_of_shared_parent_subsegment Q i j a d a' d' ha hd ha' hd'
        (hS (by simp [P, e])) (hS (by simp [P, e]))
        (hT (by simp [P, f])) (hT (by simp [P, f])) hF hG hsync t u

end CoordinateTriangleBoundaryIntersection

omit [T2Space M] in
private theorem compatibleCover_subdivision_intersections
    {F : OpenPartialHomeomorph Plane M} {b : AffineBasis (Fin 3) ℝ Plane} {S : Finset M}
    (R : SmoothTriangleBoundarySubdivision F b S) (t u : R.mesh.Triangle) (htu : t ≠ u) :
    (∃ k l : Fin 3, (R.face t).carrier ∩ (R.face u).carrier =
        ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 =
        ((R.face u).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin 3, (R.face t).carrier ∩ (R.face u).carrier ⊆
      {F (meshTriangleBasis R.mesh t v)} := by
  have hedge (s : R.mesh.Triangle) (k : Fin 3) :
      ((R.face s).boundary k).map '' Icc (0 : ℝ) 1 =
        F '' affineSegment ℝ (meshTriangleBasis R.mesh s (k.succAbove 0))
          (meshTriangleBasis R.mesh s (k.succAbove 1)) := by
    rw [R.boundary_map, image_comp, compatibleCover_segment_image]
  rw [R.carrier_eq, R.carrier_eq, ← F.injOn.image_inter (R.source_subset t) (R.source_subset u)]
  rcases meshTriangleBasis_pair_intersections R.mesh t u htu with ⟨k, l, hk, hl⟩ | ⟨v, hvt, hv⟩
  · exact Or.inl ⟨k, l, by rw [hk, hedge], by rw [hedge, hedge, hl]⟩
  · obtain ⟨j, hj⟩ : v ∈ range (R.mesh.orderedVertex t) := by
      rw [R.mesh.range_orderedVertex]
      exact hvt
    refine Or.inr ⟨j, ?_⟩
    rintro q ⟨z, hz, rfl⟩
    rw [mem_singleton_iff.mp (hv hz), ← hj]
    exact mem_singleton _




theorem nonempty_compatibleCoordinateTriangleRefinement
    {I : Type v} [Finite I]
    (F : I → OpenPartialHomeomorph Plane M) (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFinv : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (chart : I → M)
    (hchart : ∀ i, F i '' convexHull ℝ (range (b i)) ⊆ (chartAt Plane (chart i)).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    (hcover : (⋃ i, F i '' convexHull ℝ (range (b i))) = univ) :
    Nonempty (CompatibleCoordinateTriangleRefinement F b) := by
  classical
  let J := {ij : I × I // ij.1 ≠ ij.2}
  choose P hP using fun ij : J => (hparents ij.1.1 ij.1.2 ij.2).exists_marks
  let V : Set M := (⋃ i, F i '' range (b i)) ∪ ⋃ ij : J, (P ij : Set M)
  have hV : V.Finite :=
    (finite_iUnion (fun i => (finite_range (b i)).image (F i))).union
      (finite_iUnion (fun ij => (P ij).finite_toSet))
  let allmarks := hV.toFinset
  let S (i : I) : Finset M := allmarks.filter (fun q => q ∈ F i '' frontier (convexHull ℝ (range (b i))))
  have hS (i : I) : (S i : Set M) ⊆ F i '' frontier (convexHull ℝ (range (b i))) :=
    fun _ hq => (Finset.mem_filter.mp hq).2
  have hvertices (i : I) : F i '' range (b i) ⊆ (S i : Set M) := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨?_, image_mono (compatibleCover_vertex_frontier (b i)) hq⟩
    exact (Set.Finite.mem_toFinset hV).mpr (Or.inl (mem_iUnion.mpr ⟨i, hq⟩))
  have hpairmarks (ij : J) : (P ij : Set M) ⊆ S ij.1.1 ∧ (P ij : Set M) ⊆ S ij.1.2 := by
    have hglobal {q : M} (hq : q ∈ (P ij : Set M)) : q ∈ allmarks :=
      (Set.Finite.mem_toFinset hV).mpr (Or.inr (mem_iUnion.mpr ⟨ij, hq⟩))
    exact ⟨fun _ hq => Finset.mem_filter.mpr ⟨hglobal hq, ((hP ij).1 hq).1⟩,
      fun _ hq => Finset.mem_filter.mpr ⟨hglobal hq, ((hP ij).1 hq).2⟩⟩
  have hfrontsub (i : I) : F i '' frontier (convexHull ℝ (range (b i))) ⊆
      F i '' convexHull ℝ (range (b i)) :=
    image_mono ((finite_range (b i)).isCompact_convexHull ℝ).isClosed.frontier_subset
  have hsync (i j : I) (hij : i ≠ j) :
      (S i : Set M) ∩ (F j '' convexHull ℝ (range (b j))) =
        (S j : Set M) ∩ (F i '' convexHull ℝ (range (b i))) := by
    ext q
    constructor
    · rintro ⟨hqi, hqj⟩
      have hqKi := hfrontsub i (hS i hqi)
      exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqi).1,
        ((hparents i j hij).subset_frontiers ⟨hqKi, hqj⟩).2⟩, hqKi⟩
    · rintro ⟨hqj, hqi⟩
      have hqKj := hfrontsub j (hS j hqj)
      exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqj).1,
        ((hparents i j hij).subset_frontiers ⟨hqi, hqKj⟩).1⟩, hqKj⟩
  choose R hRchart using fun i => exists_smoothTriangleBoundarySubdivision_with_refinement (F i) (hF i) (hFinv i)
    (b i) (hsource i) (S i) (hS i) (hvertices i) (chart i) (hchart i)
  let A := (i : I) × (R i).mesh.Triangle
  let face (a : A) := (R a.1).face a.2
  let coordinates (a : A) := F a.1
  let basis (a : A) := meshTriangleBasis (R a.1).mesh a.2
  have hchild (a d : A) (had : a ≠ d) :
      ((∃ k l : Fin 3, (face a).carrier ∩ (face d).carrier =
            ((face a).boundary k).map '' Icc (0 : ℝ) 1 ∧
          ((face a).boundary k).map '' Icc (0 : ℝ) 1 =
            ((face d).boundary l).map '' Icc (0 : ℝ) 1) ∨
        ∃ w : Fin 3, (face a).carrier ∩ (face d).carrier ⊆ {coordinates a (basis a w)}) ∧
      (face a).carrier ∩ (face d).carrier ⊆ frontier (face a).carrier := by
    rcases a with ⟨i, t⟩
    rcases d with ⟨j, u⟩
    by_cases hij : i = j
    · subst j
      have htu : t ≠ u := fun h => had (h ▸ rfl)
      exact ⟨compatibleCover_subdivision_intersections (R i).toSmoothTriangleBoundarySubdivision t u htu,
        (R i).intersection_frontier t u htu⟩
    · let ij : J := ⟨(i, j), hij⟩
      have h := (hP ij).2 (S i) (S j) (hpairmarks ij).1 (hpairmarks ij).2
        (R i).toSmoothTriangleBoundarySubdivision (R j).toSmoothTriangleBoundarySubdivision (hsync i j hij) t u
      exact ⟨h.1, h.2.trans inter_subset_left⟩
  refine ⟨{
    marks := S
    subdivision := R
    intersections := fun a d had => (hchild a d had).1
    intersection_frontier := fun a d had => (hchild a d had).2
    cover := ?_ }⟩
  apply subset_antisymm (subset_univ _)
  intro q hq
  obtain ⟨i, hqi⟩ := mem_iUnion.mp (hcover.symm ▸ hq)
  rw [← (R i).cover] at hqi
  obtain ⟨t, hqt⟩ := mem_iUnion.mp hqi
  exact mem_iUnion.mpr ⟨⟨i, t⟩, hqt⟩



theorem CompatibleCoordinateTriangleRefinement.nonempty_triangulationWithCoordinates
    {I : Type v} [Finite I]
    {F : I → OpenPartialHomeomorph Plane M} {b : I → AffineBasis (Fin 3) ℝ Plane}
    (R : CompatibleCoordinateTriangleRefinement F b)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFinv : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target) :
    Nonempty (FiniteSmoothTriangulationWithCoordinates (M := M)) := by
  exact compatibleCover_assemble R.face R.coordinates R.basis
    (fun a => hF a.1) (fun a => hFinv a.1) R.source_subset R.carrier_eq
    R.boundary_map R.boundary_injective R.intersections R.intersection_frontier R.cover



theorem nonempty_finiteSmoothTriangulationWithCoordinates_of_compatible_coordinate_cover
    {I : Type v} [Finite I]
    (F : I → OpenPartialHomeomorph Plane M) (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFinv : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (chart : I → M)
    (hchart : ∀ i, F i '' convexHull ℝ (range (b i)) ⊆ (chartAt Plane (chart i)).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    (hcover : (⋃ i, F i '' convexHull ℝ (range (b i))) = univ) :
    Nonempty (FiniteSmoothTriangulationWithCoordinates (M := M)) := by
  obtain ⟨R⟩ := nonempty_compatibleCoordinateTriangleRefinement
    F b hF hFinv hsource chart hchart hparents hcover
  exact R.nonempty_triangulationWithCoordinates hF hFinv



theorem nonempty_finiteSmoothTriangulation_of_compatible_coordinate_cover
    {I : Type v} [Finite I]
    (F : I → OpenPartialHomeomorph Plane M) (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFinv : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (chart : I → M)
    (hchart : ∀ i, F i '' convexHull ℝ (range (b i)) ⊆ (chartAt Plane (chart i)).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    (hcover : (⋃ i, F i '' convexHull ℝ (range (b i))) = univ) :
    Nonempty (FiniteSmoothTriangulation (M := M)) := by
  obtain ⟨W⟩ := nonempty_finiteSmoothTriangulationWithCoordinates_of_compatible_coordinate_cover
    F b hF hFinv hsource chart hchart hparents hcover
  exact ⟨W.triangulation⟩

end PoincareConjecture.Topology.Surface
