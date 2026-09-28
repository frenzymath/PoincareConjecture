import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCandidate











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {p : Polygon E (n + 2)}

private theorem normalized_vertexTriangle_image (k : Fin (n + 2))
    (f : E ≃ᴬ[ℝ] (ℝ × ℝ)) (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1)) :
    f '' polygonVertexTriangle p k = unitTriangle := by
  have him := f.toAffineEquiv.toAffineMap.image_convexHull
    {p k, p ((finRotate (n + 2)).symm k), p (finRotate (n + 2) k)}
  change f '' polygonVertexTriangle p k =
    convexHull ℝ (f '' {p k, p ((finRotate (n + 2)).symm k),
      p (finRotate (n + 2) k)}) at him
  rw [him, image_insert_eq, image_insert_eq, image_singleton, hfk, hfp, hfs,
    ← unitTriangle_eq_convexHull]

private theorem openSegment_mem_normalized_low_triangle (k j : Fin (n + 2))
    (f : E ≃ᴬ[ℝ] (ℝ × ℝ)) (hfk : f (p k) = (0, 0))
    (hpos : 0 < (f (p j)).1 ∧ 0 < (f (p j)).2) {x : E}
    (hx : x ∈ openSegment ℝ (p k) (p j)) :
    0 < (f x).1 ∧ 0 < (f x).2 ∧
      (f x).1 + (f x).2 < (f (p j)).1 + (f (p j)).2 := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hfz : f (AffineMap.lineMap (p k) (p j) t) =
      (t * (f (p j)).1, t * (f (p j)).2) := by
    have h := f.toAffineEquiv.toAffineMap.apply_lineMap (p k) (p j) t
    change f (AffineMap.lineMap (p k) (p j) t) =
      AffineMap.lineMap (f (p k)) (f (p j)) t at h
    rw [h, hfk]
    ext <;> simp [AffineMap.lineMap_apply_module]
  rw [hfz]
  refine ⟨mul_pos ht.1 hpos.1, mul_pos ht.1 hpos.2, ?_⟩
  dsimp only
  nlinarith [mul_pos (sub_pos.mpr ht.2) (add_pos hpos.1 hpos.2)]

section OneCandidate

variable (hp : IsSimplePolygonalArc p) (k j : Fin (n + 2))
  (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
  (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1))
  (hj0 : j ≠ 0) (hjl : j ≠ Fin.last (n + 1))
  (hfk : f (p k) = (0, 0))
  (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
  (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
  (hjk : j ≠ k) (hjp : j ≠ (finRotate (n + 2)).symm k)
  (hjs : j ≠ finRotate (n + 2) k) (hjT : f (p j) ∈ unitTriangle)
  (hmin : ∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
    l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
      (f (p j)).1 + (f (p j)).2 ≤ (f (p l)).1 + (f (p l)).2)

include hp hk0 hkl hj0 hjl hfk hfp hfs hjk hjp hjs hjT hmin



theorem IsSimplePolygonalArc.normalized_minimal_candidate_neighbor_height :
    (f (p j)).1 + (f (p j)).2 ≤
        (f (p ((finRotate (n + 2)).symm j))).1 +
          (f (p ((finRotate (n + 2)).symm j))).2 ∧
      (f (p j)).1 + (f (p j)).2 ≤
        (f (p (finRotate (n + 2) j))).1 + (f (p (finRotate (n + 2) j))).2 := by
  have hpos := hp.normalized_triangle_vertex_pos k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT
  let d := (f (p j)).1 + (f (p j)).2
  have hd : 0 < d := add_pos hpos.1 hpos.2
  have hdis := hp.normalized_low_triangle_disjoint_arcBoundary
    k hk0 hkl f hfk hfp hfs hd hjT.2.2 hmin
  have hbound (i : Fin (n + 2))
      (hedge : segment ℝ (p j) (p i) ⊆ polygonArcBoundary p) :
      d ≤ (f (p i)).1 + (f (p i)).2 := by
    by_contra! hlow
    let u : ℝ × ℝ := ((f (p j)).1 / d, (f (p j)).2 / d)
    let v : ℝ × ℝ := ((f (p i)).1 / d, (f (p i)).2 / d)
    have hu : 0 < u.1 ∧ 0 < u.2 := ⟨div_pos hpos.1 hd, div_pos hpos.2 hd⟩
    have huH : u.1 + u.2 ≤ 1 := by
      change (f (p j)).1 / d + (f (p j)).2 / d ≤ 1
      rw [← add_div, div_self hd.ne']
    have hvH : v.1 + v.2 < 1 := by
      change (f (p i)).1 / d + (f (p i)).2 / d < 1
      rw [← add_div, div_lt_one hd]
      exact hlow
    obtain ⟨w, hw, hwT⟩ := exists_openSegment_mem_interior_unitTriangle hu huH hvH
    rw [openSegment_eq_image_lineMap] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    let x := AffineMap.lineMap (p j) (p i) t
    have hxB : x ∈ polygonArcBoundary p := hedge (lineMap_mem_segment ℝ _ _ ⟨ht.1.le, ht.2.le⟩)
    have hfx : f x = d • AffineMap.lineMap u v t := by
      have hh := f.toAffineEquiv.toAffineMap.apply_lineMap (p j) (p i) t
      change f x = AffineMap.lineMap (f (p j)) (f (p i)) t at hh
      rw [hh]
      ext <;> simp only [AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, u, v] <;> field_simp
    rw [interior_unitTriangle] at hwT
    apply Set.disjoint_left.mp hdis _ (mem_image_of_mem f hxB)
    rw [hfx]
    change 0 < d * (AffineMap.lineMap u v t).1 ∧
      0 < d * (AffineMap.lineMap u v t).2 ∧
        d * (AffineMap.lineMap u v t).1 + d * (AffineMap.lineMap u v t).2 < d
    refine ⟨mul_pos hd hwT.1, mul_pos hd hwT.2.1, ?_⟩
    nlinarith [mul_pos hd (sub_pos.mpr hwT.2.2)]
  have harms := polygonArcIncidentEdges_subset_triangle_inter_boundary p j hj0 hjl
  constructor
  · exact hbound _ (fun _ hx => (harms (Or.inl hx)).2)
  · exact hbound _ (fun _ hx => (harms (Or.inr hx)).2)



theorem IsSimplePolygonalArc.normalized_minimal_candidate_triangle_height :
    ∀ x ∈ polygonVertexTriangle p j,
      (f (p j)).1 + (f (p j)).2 ≤ (f x).1 + (f x).2 := by
  have hneighbors := hp.normalized_minimal_candidate_neighbor_height k j f
    hk0 hkl hj0 hjl hfk hfp hfs hjk hjp hjs hjT hmin
  let H : E →ᵃ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap.comp f.toAffineEquiv.toAffineMap
  have hconv : Convex ℝ {x | (f (p j)).1 + (f (p j)).2 ≤ (f x).1 + (f x).2} :=
    (convex_Ici (𝕜 := ℝ) ((f (p j)).1 + (f (p j)).2)).affine_preimage H
  have hsub : polygonVertexTriangle p j ⊆
      {x | (f (p j)).1 + (f (p j)).2 ≤ (f x).1 + (f x).2} := by
    apply convexHull_min
    · rintro x (rfl | rfl | rfl)
      · exact le_refl ((f (p j)).1 + (f (p j)).2)
      · exact hneighbors.1
      · exact hneighbors.2
    · exact hconv
  exact fun _ hx => hsub hx



theorem IsSimplePolygonalArc.base_not_mem_minimal_candidate_triangle :
    p k ∉ polygonVertexTriangle p j := by
  intro hkT
  have hheight := hp.normalized_minimal_candidate_triangle_height k j f
    hk0 hkl hj0 hjl hfk hfp hfs hjk hjp hjs hjT hmin (p k) hkT
  have hpos := hp.normalized_triangle_vertex_pos k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT
  rw [hfk] at hheight
  change (f (p j)).1 + (f (p j)).2 ≤ 0 + 0 at hheight
  linarith [hpos.1, hpos.2]

omit hj0 hjl hjk hjp hjs in


theorem IsSimplePolygonalArc.normalized_low_triangle_disjoint_visible_chord
    (_hj0 : j ≠ 0) (_hjl : j ≠ Fin.last (n + 1)) (_hjk : j ≠ k)
    (_hjp : j ≠ (finRotate (n + 2)).symm k) (_hjs : j ≠ finRotate (n + 2) k)
    (r s : Fin (n + 2)) (hrk : r ≠ k) (hsk : s ≠ k)
    (hvis : Disjoint (openSegment ℝ (p r) (p s)) (polygonArcBoundary p)) :
    Disjoint {w : ℝ × ℝ | 0 < w.1 ∧ 0 < w.2 ∧
      w.1 + w.2 < (f (p j)).1 + (f (p j)).2} (f '' segment ℝ (p r) (p s)) := by
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hback (x y z : E) (h : f z ∈ segment ℝ (f x) (f y)) :
      z ∈ segment ℝ x y := by
    have him := image_segment ℝ f.toAffineEquiv.toAffineMap x y
    change f '' segment ℝ x y = segment ℝ (f x) (f y) at him
    rw [← him] at h
    obtain ⟨w, hw, heq⟩ := h
    exact f.injective heq ▸ hw
  have hcornerBack (x : E) (hx : f x ∈ unitCorner) :
      x ∈ segment ℝ (p k) (p ((finRotate (n + 2)).symm k)) ∪
        segment ℝ (p k) (p (finRotate (n + 2) k)) := by
    rcases hx with hx | hx
    · left
      rw [← hfk, ← hfp] at hx
      exact hback _ _ _ hx
    · right
      rw [← hfk, ← hfs] at hx
      exact hback _ _ _ hx
  have hcornerVertex (i : Fin (n + 2)) (hik : i ≠ k) (hi : f (p i) ∈ unitCorner) :
      f (p i) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
    rcases hcornerBack (p i) hi with hi | hi
    · have he : p i ∈ p.edgeSet ℝ a.castSucc := by
        rw [polygon_arcEdge_eq_segment, hap, hak, segment_symm]
        exact hi
      have hh := (hp.vertex_mem_edgeSet_iff i a).mp he
      rw [hap, hak] at hh
      left
      rw [hh.resolve_right hik, hfp]
    · have he : p i ∈ p.edgeSet ℝ b.castSucc := by
        rw [polygon_arcEdge_eq_segment, hbk, hbs]
        exact hi
      have hh := (hp.vertex_mem_edgeSet_iff i b).mp he
      rw [hbk, hbs] at hh
      right
      change f (p i) = (0, 1)
      rw [hh.resolve_left hik, hfs]
  have him : f '' segment ℝ (p r) (p s) = segment ℝ (f (p r)) (f (p s)) :=
    image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  have havoid : segment ℝ (f (p r)) (f (p s)) ∩ unitCorner ⊆ {(1, 0), (0, 1)} := by
    rintro w ⟨hwS, hwC⟩
    rw [← him] at hwS
    obtain ⟨x, hx, rfl⟩ := hwS
    have hxB : x ∈ polygonArcBoundary p :=
      (polygonArcIncidentEdges_subset_triangle_inter_boundary p k hk0 hkl
        (hcornerBack x hwC)).2
    have hxend : x = p r ∨ x = p s := by
      by_contra! hne
      exact Set.disjoint_left.mp hvis
        (mem_openSegment_of_ne_left_right (Ne.symm hne.1) (Ne.symm hne.2) hx) hxB
    rcases hxend with rfl | rfl
    · exact hcornerVertex r hrk hwC
    · exact hcornerVertex s hsk hwC
  apply Set.disjoint_left.mpr
  rintro w ⟨hwx, hwy, hwH⟩ hwS
  have hwT : w ∈ interior unitTriangle := by
    rw [interior_unitTriangle]
    exact ⟨hwx, hwy, hwH.trans_le hjT.2.2⟩
  obtain ⟨c, hc, hcT, hcH⟩ := exists_endpoint_interior_unitTriangle_le_sum
    (him ▸ hwS) hwT havoid
  obtain ⟨i, hci⟩ : ∃ i : Fin (n + 2), c = f (p i) := by
    rcases hc with hc | hc
    · exact ⟨r, hc⟩
    · exact ⟨s, hc⟩
  rw [hci] at hcT hcH
  have hcoords := hcT
  rw [interior_unitTriangle] at hcoords
  have hik : i ≠ k := by
    intro heq
    rw [heq, hfk] at hcoords
    exact (lt_irrefl 0) hcoords.1
  have hip : i ≠ (finRotate (n + 2)).symm k := by
    intro heq
    rw [heq, hfp] at hcoords
    exact (lt_irrefl 0) hcoords.2.1
  have his : i ≠ finRotate (n + 2) k := by
    intro heq
    rw [heq, hfs] at hcoords
    exact (lt_irrefl 0) hcoords.1
  exact (not_lt_of_ge (hmin i hik hip his (interior_subset hcT))) (hcH.trans_lt hwH)

variable (l m : Fin (n + 2)) (g : E ≃ᴬ[ℝ] (ℝ × ℝ))
  (hl0 : l ≠ 0) (hll : l ≠ Fin.last (n + 1))
  (hm0 : m ≠ 0) (hml : m ≠ Fin.last (n + 1))
  (hgl : g (p l) = (0, 0))
  (hgp : g (p ((finRotate (n + 2)).symm l)) = (1, 0))
  (hgs : g (p (finRotate (n + 2) l)) = (0, 1))
  (hmln : m ≠ l) (hmp : m ≠ (finRotate (n + 2)).symm l)
  (hms : m ≠ finRotate (n + 2) l) (hmT : g (p m) ∈ unitTriangle)
  (hgmin : ∀ i, i ≠ l → i ≠ (finRotate (n + 2)).symm l →
    i ≠ finRotate (n + 2) l → g (p i) ∈ unitTriangle →
      (g (p m)).1 + (g (p m)).2 ≤ (g (p i)).1 + (g (p i)).2)
  (hklne : k ≠ l)

include hl0 hll hm0 hml hgl hgp hgs hmln hmp hms hmT hgmin hklne



theorem IsSimplePolygonalArc.openSegments_disjoint_of_minimal_arc_candidates :
    Disjoint (openSegment ℝ (p k) (p j)) (openSegment ℝ (p l) (p m)) := by
  have hfpos := hp.normalized_triangle_vertex_pos k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT
  have hgpos := hp.normalized_triangle_vertex_pos l hl0 hll g hgl hgp hgs m hmln hmp hms hmT
  apply Set.disjoint_left.mpr
  intro x hxF hxG
  by_cases hmk : m = k
  · have hnorm := normalized_vertexTriangle_image k f hfk hfp hfs
    have hjTri : p j ∈ polygonVertexTriangle p k := by
      obtain ⟨y, hy, heq⟩ := hnorm.symm ▸ hjT
      exact f.injective heq ▸ hy
    have hkTri : p k ∈ polygonVertexTriangle p k := subset_convexHull ℝ _ (by simp)
    have hxTri : x ∈ polygonVertexTriangle p k :=
      (convex_convexHull ℝ _).openSegment_subset hkTri hjTri hxF
    have hheight := hp.normalized_minimal_candidate_triangle_height l m g
      hl0 hll hm0 hml hgl hgp hgs hmln hmp hms hmT hgmin x (hmk.symm ▸ hxTri)
    exact (not_lt_of_ge hheight)
      (openSegment_mem_normalized_low_triangle l m g hgl hgpos hxG).2.2
  · have hgvis := hp.openSegment_disjoint_arcBoundary_of_minimal_triangle_vertex
      l hl0 hll g hgl hgp hgs m hmln hmp hms hmT hgmin
    have hdis := hp.normalized_low_triangle_disjoint_visible_chord k j f
      hk0 hkl hfk hfp hfs hjT hmin hj0 hjl hjk hjp hjs l m hklne.symm hmk hgvis
    exact Set.disjoint_left.mp hdis
      (openSegment_mem_normalized_low_triangle k j f hfk hfpos hxF)
      (mem_image_of_mem f (openSegment_subset_segment ℝ _ _ hxG))



theorem IsSimplePolygonalArc.segments_inter_eq_of_minimal_arc_candidates :
    segment ℝ (p k) (p j) ∩ segment ℝ (p l) (p m) =
      {p k, p j} ∩ {p l, p m} := by
  have hdis := hp.openSegments_disjoint_of_minimal_arc_candidates k j f
    hk0 hkl hj0 hjl hfk hfp hfs hjk hjp hjs hjT hmin l m g
      hl0 hll hm0 hml hgl hgp hgs hmln hmp hms hmT hgmin hklne
  have hfvis := hp.openSegment_disjoint_arcBoundary_of_minimal_triangle_vertex
    k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT hmin
  have hgvis := hp.openSegment_disjoint_arcBoundary_of_minimal_triangle_vertex
    l hl0 hll g hgl hgp hgs m hmln hmp hms hmT hgmin
  apply subset_antisymm
  · rintro x ⟨hxF, hxG⟩
    have hfirst : x ∈ ({p k, p j} : Set E) := by
      by_contra hx
      have hxk : p k ≠ x := fun h => hx (Or.inl h.symm)
      have hxj : p j ≠ x := fun h => hx (Or.inr h.symm)
      have hxFo := mem_openSegment_of_ne_left_right hxk hxj hxF
      have hxB : x ∉ polygonArcBoundary p := Set.disjoint_left.mp hfvis hxFo
      have hxl : p l ≠ x := fun h => hxB (h ▸ polygon_vertex_mem_arcBoundary p l)
      have hxm : p m ≠ x := fun h => hxB (h ▸ polygon_vertex_mem_arcBoundary p m)
      exact Set.disjoint_left.mp hdis hxFo (mem_openSegment_of_ne_left_right hxl hxm hxG)
    have hxB : x ∈ polygonArcBoundary p := by
      rcases hfirst with rfl | rfl <;> exact polygon_vertex_mem_arcBoundary p _
    refine ⟨hfirst, ?_⟩
    by_contra hx
    have hxl : p l ≠ x := fun h => hx (Or.inl h.symm)
    have hxm : p m ≠ x := fun h => hx (Or.inr h.symm)
    exact Set.disjoint_left.mp hgvis (mem_openSegment_of_ne_left_right hxl hxm hxG) hxB
  · intro x hx
    constructor
    · rcases hx.1 with rfl | hx
      · exact left_mem_segment ℝ _ _
      · exact hx ▸ right_mem_segment ℝ _ _
    · rcases hx.2 with rfl | hx
      · exact left_mem_segment ℝ _ _
      · exact hx ▸ right_mem_segment ℝ _ _

end OneCandidate

end PoincareConjecture.M25.Topology3D
