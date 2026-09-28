import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleEntry
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.LocalInsideWedge
import Mathlib.Data.Finset.Max












set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {p : Polygon E n}



theorem IsSimplePolygon.normalized_nonincident_edge_inter_corner_subset
    (hp : IsSimplePolygon p) (k : Fin n) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate n).symm k)) = (1, 0))
    (hfs : f (p (finRotate n k)) = (0, 1))
    (i : Fin n) (hik : i ≠ k) (hip : i ≠ (finRotate n).symm k) :
    segment ℝ (f (p i)) (f (p (finRotate n i))) ∩ unitCorner ⊆
      {(1, 0), (0, 1)} := by
  have himage (a b : E) : f '' segment ℝ a b = segment ℝ (f a) (f b) :=
    image_segment ℝ f.toAffineEquiv.toAffineMap a b
  have hback (a b w : E) (hw : f w ∈ segment ℝ (f a) (f b)) :
      w ∈ segment ℝ a b := by
    rw [← himage] at hw
    obtain ⟨v, hv, heq⟩ := hw
    exact f.injective heq ▸ hv
  intro z hz
  rw [← himage] at hz
  obtain ⟨⟨w, hw, rfl⟩, hwC⟩ := hz
  have hwi : w ∈ p.edgeSet ℝ i := by
    rw [polygon_edgeSet_eq_segment]
    exact hw
  have hwk : w ≠ p k := by
    intro heq
    rw [heq] at hwi
    rcases (hp.vertex_mem_edgeSet_iff k i).mp hwi with hki | hki
    · exact hik hki.symm
    · exact hip ((finRotate n).injective
        (hki.symm.trans ((finRotate n).apply_symm_apply k).symm))
  rcases hwC with hwC | hwC
  · rw [← hfk, ← hfp] at hwC
    have hwp : w ∈ p.edgeSet ℝ ((finRotate n).symm k) := by
      rw [polygon_edgeSet_eq_segment, (finRotate n).apply_symm_apply, segment_symm]
      exact hback _ _ _ hwC
    rcases (hp.edges_inter i _ hip ⟨hwi, hwp⟩).2 with heq | heq
    · exact Or.inl (by rw [heq, hfp])
    · exact (hwk (by
        simpa only [mem_singleton_iff, (finRotate n).apply_symm_apply] using heq)).elim
  · rw [← hfk, ← hfs] at hwC
    have hwout : w ∈ p.edgeSet ℝ k := by
      rw [polygon_edgeSet_eq_segment]
      exact hback _ _ _ hwC
    rcases (hp.edges_inter i k hik ⟨hwi, hwout⟩).2 with heq | heq
    · exact (hwk heq).elim
    · right
      change f w = (0, 1)
      rw [heq, hfs]



theorem IsSimplePolygon.normalized_triangle_vertex_pos (hp : IsSimplePolygon p)
    (k : Fin n) (f : E ≃ᴬ[ℝ] (ℝ × ℝ)) (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate n).symm k)) = (1, 0))
    (hfs : f (p (finRotate n k)) = (0, 1))
    (j : Fin n) (hjk : j ≠ k) (hjp : j ≠ (finRotate n).symm k)
    (hjs : j ≠ finRotate n k) (hjT : f (p j) ∈ unitTriangle) :
    0 < (f (p j)).1 ∧ 0 < (f (p j)).2 := by
  have hback (a b : E) (h : f (p j) ∈ segment ℝ (f a) (f b)) :
      p j ∈ segment ℝ a b := by
    have him := image_segment ℝ f.toAffineEquiv.toAffineMap a b
    change f '' segment ℝ a b = segment ℝ (f a) (f b) at him
    rw [← him] at h
    obtain ⟨w, hw, heq⟩ := h
    exact f.injective heq ▸ hw
  have hjC : f (p j) ∉ unitCorner := by
    rintro (h | h)
    · rw [← hfk, ← hfp] at h
      have hjedge : p j ∈ p.edgeSet ℝ ((finRotate n).symm k) := by
        rw [polygon_edgeSet_eq_segment, (finRotate n).apply_symm_apply, segment_symm]
        exact hback _ _ h
      rcases (hp.vertex_mem_edgeSet_iff j _).mp hjedge with heq | heq
      · exact hjp heq
      · exact hjk (by simpa only [(finRotate n).apply_symm_apply] using heq)
    · rw [← hfk, ← hfs] at h
      have hjedge : p j ∈ p.edgeSet ℝ k := by
        rw [polygon_edgeSet_eq_segment]
        exact hback _ _ h
      exact ((hp.vertex_mem_edgeSet_iff j k).mp hjedge).elim hjk hjs
  constructor
  · by_contra! h
    have heq : (f (p j)).1 = 0 := le_antisymm h hjT.1
    exact hjC ((mem_unitCorner_iff _).mpr (Or.inr ⟨heq, hjT.2.1, by linarith [hjT.2.2]⟩))
  · by_contra! h
    have heq : (f (p j)).2 = 0 := le_antisymm h hjT.2.1
    exact hjC ((mem_unitCorner_iff _).mpr (Or.inl ⟨hjT.1, by linarith [hjT.2.2], heq⟩))



theorem IsSimplePolygon.openSegment_disjoint_boundary_of_minimal_triangle_vertex
    (hp : IsSimplePolygon p) (k : Fin n) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate n).symm k)) = (1, 0))
    (hfs : f (p (finRotate n k)) = (0, 1))
    (j : Fin n) (hjk : j ≠ k) (hjp : j ≠ (finRotate n).symm k)
    (hjs : j ≠ finRotate n k) (hjT : f (p j) ∈ unitTriangle)
    (hmin : ∀ l, l ≠ k → l ≠ (finRotate n).symm k → l ≠ finRotate n k →
      f (p l) ∈ unitTriangle → (f (p j)).1 + (f (p j)).2 ≤ (f (p l)).1 + (f (p l)).2) :
    Disjoint (openSegment ℝ (p k) (p j)) (p.boundary ℝ) := by
  have hpos := hp.normalized_triangle_vertex_pos k f hfk hfp hfs j hjk hjp hjs hjT
  apply Set.disjoint_left.mpr
  intro z hz hzB
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let z := AffineMap.lineMap (p k) (p j) t
  have hfz : f z = (t * (f (p j)).1, t * (f (p j)).2) := by
    have h := f.toAffineEquiv.toAffineMap.apply_lineMap (p k) (p j) t
    change f z = AffineMap.lineMap (f (p k)) (f (p j)) t at h
    rw [h, hfk]
    ext <;> simp [AffineMap.lineMap_apply_module]
  have hzx : 0 < (f z).1 := by rw [hfz]; exact mul_pos ht.1 hpos.1
  have hzy : 0 < (f z).2 := by rw [hfz]; exact mul_pos ht.1 hpos.2
  have hzH : (f z).1 + (f z).2 < (f (p j)).1 + (f (p j)).2 := by
    rw [hfz]
    dsimp only
    nlinarith [mul_pos (sub_pos.mpr ht.2) (add_pos hpos.1 hpos.2)]
  have hzT : f z ∈ interior unitTriangle := by
    rw [interior_unitTriangle]
    exact ⟨hzx, hzy, hzH.trans_le hjT.2.2⟩
  have hzC : f z ∉ unitCorner := by
    intro h
    rcases (mem_unitCorner_iff _).mp h with h | h
    · exact hzy.ne' h.2.2
    · exact hzx.ne' h.1
  obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p z).mp hzB
  have himage (l : Fin n) :
      f '' p.edgeSet ℝ l = segment ℝ (f (p l)) (f (p (finRotate n l))) := by
    rw [polygon_edgeSet_eq_segment]
    exact image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  have hzi : f z ∈ segment ℝ (f (p i)) (f (p (finRotate n i))) := by
    rw [← himage]
    exact mem_image_of_mem f hi
  have hik : i ≠ k := by
    intro heq
    rw [heq, hfk, hfs] at hzi
    exact hzC (Or.inr hzi)
  have hip : i ≠ (finRotate n).symm k := by
    intro heq
    rw [heq, (finRotate n).apply_symm_apply, hfp, hfk, segment_symm] at hzi
    exact hzC (Or.inl hzi)
  obtain ⟨c, hc, hcT, hcH⟩ := exists_endpoint_interior_unitTriangle_le_sum hzi hzT
    (hp.normalized_nonincident_edge_inter_corner_subset k f hfk hfp hfs i hik hip)
  obtain ⟨l, hcl⟩ : ∃ l : Fin n, c = f (p l) := by
    rcases hc with hc | hc
    · exact ⟨i, hc⟩
    · exact ⟨finRotate n i, hc⟩
  rw [hcl] at hcT hcH
  have hcoords := hcT
  rw [interior_unitTriangle] at hcoords
  have hlk : l ≠ k := by
    intro heq
    rw [heq, hfk] at hcoords
    exact (lt_irrefl 0) hcoords.1
  have hlp : l ≠ (finRotate n).symm k := by
    intro heq
    rw [heq, hfp] at hcoords
    exact (lt_irrefl 0) hcoords.2.1
  have hls : l ≠ finRotate n k := by
    intro heq
    rw [heq, hfs] at hcoords
    exact (lt_irrefl 0) hcoords.1
  exact (not_lt_of_ge (hmin l hlk hlp hls (interior_subset hcT))) (hcH.trans_lt hzH)




theorem IsSimplePolygon.exists_visible_diagonal_of_triangle_vertex
    [FiniteDimensional ℝ E] (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (k : Fin n)
    (hli : LinearIndependent ℝ
      ![p ((finRotate n).symm k) - p k, p (finRotate n k) - p k])
    (X : E →L[ℝ] ℝ) (hX : Function.Surjective X)
    (hsupport : ∀ l, X (p k) ≤ X (p l))
    (hcandidate : ∃ j, j ≠ k ∧ j ≠ (finRotate n).symm k ∧ j ≠ finRotate n k ∧
      p j ∈ convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)}) :
    ∃ j, j ≠ k ∧ j ≠ (finRotate n).symm k ∧ j ≠ finRotate n k ∧
      openSegment ℝ (p k) (p j) ⊆ polygonInterior p ∧
      segment ℝ (p k) (p j) ⊆ closure (polygonInterior p) := by
  classical
  obtain ⟨f, hfk, hfp, hfs, r, hr, hr1, hwedge, _⟩ :=
    hp.exists_local_inside_wedge hdim k hli X hX hsupport
  have hnorm :
      f '' convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)} =
        unitTriangle := by
    have him := f.toAffineEquiv.toAffineMap.image_convexHull
      {p k, p ((finRotate n).symm k), p (finRotate n k)}
    change f '' convexHull ℝ {p k, p ((finRotate n).symm k), p (finRotate n k)} =
      convexHull ℝ (f '' {p k, p ((finRotate n).symm k), p (finRotate n k)}) at him
    rw [him, image_insert_eq, image_insert_eq, image_singleton, hfk, hfp, hfs,
      ← unitTriangle_eq_convexHull]
  let S := Finset.univ.filter fun l =>
    l ≠ k ∧ l ≠ (finRotate n).symm k ∧ l ≠ finRotate n k ∧ f (p l) ∈ unitTriangle
  have hS (l : Fin n) : l ∈ S ↔
      l ≠ k ∧ l ≠ (finRotate n).symm k ∧ l ≠ finRotate n k ∧ f (p l) ∈ unitTriangle := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hSne : S.Nonempty := by
    obtain ⟨l, hlk, hlp, hls, hlT⟩ := hcandidate
    refine ⟨l, (hS l).mpr ⟨hlk, hlp, hls, ?_⟩⟩
    rw [← hnorm]
    exact mem_image_of_mem f hlT
  obtain ⟨j, hjS, hjmin⟩ := S.exists_min_image (fun l => (f (p l)).1 + (f (p l)).2) hSne
  obtain ⟨hjk, hjp, hjs, hjT⟩ := (hS j).mp hjS
  have hpos := hp.normalized_triangle_vertex_pos k f hfk hfp hfs j hjk hjp hjs hjT
  have hdis := hp.openSegment_disjoint_boundary_of_minimal_triangle_vertex
    k f hfk hfp hfs j hjk hjp hjs hjT
    (fun l hlk hlp hls hlT => hjmin l ((hS l).mpr ⟨hlk, hlp, hls, hlT⟩))
  have ht : r / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  let z := AffineMap.lineMap (p k) (p j) (r / 2)
  have hzseg : z ∈ openSegment ℝ (p k) (p j) := lineMap_mem_openSegment ℝ _ _ ht
  have hfz : f z = (r / 2 * (f (p j)).1, r / 2 * (f (p j)).2) := by
    have h := f.toAffineEquiv.toAffineMap.apply_lineMap (p k) (p j) (r / 2)
    change f z = AffineMap.lineMap (f (p k)) (f (p j)) (r / 2) at h
    rw [h, hfk]
    ext <;> simp [AffineMap.lineMap_apply_module]
  have hbound (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : r / 2 * a ∈ Ioo 0 r := by
    refine ⟨mul_pos ht.1 ha, ?_⟩
    have hle := mul_le_mul_of_nonneg_left ha1 ht.1.le
    nlinarith
  have hzI : z ∈ polygonInterior p := by
    apply hwedge
    change f z ∈ Ioo 0 r ×ˢ Ioo 0 r
    rw [hfz]
    exact ⟨hbound _ hpos.1 (by linarith [hjT.2.1, hjT.2.2]),
      hbound _ hpos.2 (by linarith [hjT.1, hjT.2.2])⟩
  obtain ⟨hI, hO, _, _, hIO, hcover, _⟩ := hp.polygonRegions_spec hdim
  have hinside : openSegment ℝ (p k) (p j) ⊆ polygonInterior p := by
    apply IsPreconnected.subset_left_of_subset_union hI hO hIO
    · rw [hcover]
      intro w hw
      exact Set.disjoint_left.mp hdis hw
    · exact ⟨z, hzseg, hzI⟩
    · exact (convex_openSegment (𝕜 := ℝ) (p k) (p j)).isPreconnected
  exact ⟨j, hjk, hjp, hjs, hinside,
    segment_subset_closure_openSegment.trans (closure_mono hinside)⟩

end PoincareConjecture.M25.Topology3D
