import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleEntry
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleBaseContact
import Mathlib.Data.Finset.Max










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {p : Polygon E (n + 2)}



theorem IsSimplePolygonalArc.normalized_nonincident_edge_inter_corner_subset
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    (i : Fin (n + 1)) (hik : i.castSucc ≠ k) (his : i.succ ≠ k) :
    segment ℝ (f (p i.castSucc)) (f (p i.succ)) ∩ unitCorner ⊆
      {(1, 0), (0, 1)} := by
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have himage (x y : E) : f '' segment ℝ x y = segment ℝ (f x) (f y) :=
    image_segment ℝ f.toAffineEquiv.toAffineMap x y
  have hback (x y w : E) (hw : f w ∈ segment ℝ (f x) (f y)) :
      w ∈ segment ℝ x y := by
    rw [← himage] at hw
    obtain ⟨v, hv, heq⟩ := hw
    exact f.injective heq ▸ hv
  rintro z ⟨hz, hzC⟩
  rw [← himage] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwi : w ∈ p.edgeSet ℝ i.castSucc := by
    rw [polygon_arcEdge_eq_segment]
    exact hw
  have hwk : w ≠ p k := by
    intro heq
    rw [heq] at hwi
    exact ((hp.vertex_mem_edgeSet_iff k i).mp hwi).elim
      (fun h => hik h.symm) (fun h => his h.symm)
  rcases hzC with hzC | hzC
  · rw [← hfk, ← hfp] at hzC
    have hwa : w ∈ p.edgeSet ℝ a.castSucc := by
      rw [polygon_arcEdge_eq_segment, hap, hak, segment_symm]
      exact hback _ _ _ hzC
    have hia : i ≠ a := fun h => his (h ▸ hak)
    have hh := (hp.edges_inter i a hia ⟨hwi, hwa⟩).2
    rw [hap, hak] at hh
    exact Or.inl (by rw [hh.resolve_right hwk, hfp])
  · rw [← hfk, ← hfs] at hzC
    have hwb : w ∈ p.edgeSet ℝ b.castSucc := by
      rw [polygon_arcEdge_eq_segment, hbk, hbs]
      exact hback _ _ _ hzC
    have hib : i ≠ b := fun h => hik (h ▸ hbk)
    have hh := (hp.edges_inter i b hib ⟨hwi, hwb⟩).2
    rw [hbk, hbs] at hh
    right
    change f w = (0, 1)
    rw [hh.resolve_left hwk, hfs]



theorem IsSimplePolygonalArc.normalized_triangle_vertex_pos
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    (j : Fin (n + 2)) (hjk : j ≠ k) (hjp : j ≠ (finRotate (n + 2)).symm k)
    (hjs : j ≠ finRotate (n + 2) k) (hjT : f (p j) ∈ unitTriangle) :
    0 < (f (p j)).1 ∧ 0 < (f (p j)).2 := by
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hback (x y : E) (h : f (p j) ∈ segment ℝ (f x) (f y)) :
      p j ∈ segment ℝ x y := by
    have him := image_segment ℝ f.toAffineEquiv.toAffineMap x y
    change f '' segment ℝ x y = segment ℝ (f x) (f y) at him
    rw [← him] at h
    obtain ⟨w, hw, heq⟩ := h
    exact f.injective heq ▸ hw
  have hjC : f (p j) ∉ unitCorner := by
    rintro (h | h)
    · rw [← hfk, ← hfp] at h
      have hjedge : p j ∈ p.edgeSet ℝ a.castSucc := by
        rw [polygon_arcEdge_eq_segment, hap, hak, segment_symm]
        exact hback _ _ h
      have hh := (hp.vertex_mem_edgeSet_iff j a).mp hjedge
      rw [hap, hak] at hh
      exact hh.elim hjp hjk
    · rw [← hfk, ← hfs] at h
      have hjedge : p j ∈ p.edgeSet ℝ b.castSucc := by
        rw [polygon_arcEdge_eq_segment, hbk, hbs]
        exact hback _ _ h
      have hh := (hp.vertex_mem_edgeSet_iff j b).mp hjedge
      rw [hbk, hbs] at hh
      exact hh.elim hjk hjs
  constructor
  · by_contra! h
    have heq : (f (p j)).1 = 0 := le_antisymm h hjT.1
    exact hjC ((mem_unitCorner_iff _).mpr
      (Or.inr ⟨heq, hjT.2.1, by linarith [hjT.2.2]⟩))
  · by_contra! h
    have heq : (f (p j)).2 = 0 := le_antisymm h hjT.2.1
    exact hjC ((mem_unitCorner_iff _).mpr
      (Or.inl ⟨hjT.1, by linarith [hjT.2.2], heq⟩))



theorem IsSimplePolygonalArc.normalized_low_triangle_disjoint_arcBoundary
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    {d : ℝ} (_hd : 0 < d) (hd1 : d ≤ 1)
    (hmin : ∀ j, j ≠ k → j ≠ (finRotate (n + 2)).symm k →
      j ≠ finRotate (n + 2) k → f (p j) ∈ unitTriangle →
        d ≤ (f (p j)).1 + (f (p j)).2) :
    Disjoint {w : ℝ × ℝ | 0 < w.1 ∧ 0 < w.2 ∧ w.1 + w.2 < d}
      (f '' polygonArcBoundary p) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨hwx, hwy, hwH⟩ ⟨z, hzB, rfl⟩
  have hwT : f z ∈ interior unitTriangle := by
    rw [interior_unitTriangle]
    exact ⟨hwx, hwy, hwH.trans_le hd1⟩
  have hwC : f z ∉ unitCorner := by
    intro h
    rcases (mem_unitCorner_iff _).mp h with h | h
    · exact hwy.ne' h.2.2
    · exact hwx.ne' h.1
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzB
  have himage : f '' p.edgeSet ℝ i.castSucc =
      segment ℝ (f (p i.castSucc)) (f (p i.succ)) := by
    rw [polygon_arcEdge_eq_segment]
    exact image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  have hzi := himage ▸ mem_image_of_mem f hi
  have hik : i.castSucc ≠ k := by
    intro heq
    have hnext : i.succ = finRotate (n + 2) k := by
      have hrot : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
      rw [← heq, hrot]
    rw [heq, hnext, hfk, hfs] at hzi
    exact hwC (Or.inr hzi)
  have his : i.succ ≠ k := by
    intro heq
    have hprev : i.castSucc = (finRotate (n + 2)).symm k := by
      apply (finRotate (n + 2)).injective
      have hrot : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
      rw [hrot, heq, Equiv.apply_symm_apply]
    rw [hprev, heq, hfp, hfk, segment_symm] at hzi
    exact hwC (Or.inl hzi)
  obtain ⟨c, hc, hcT, hcH⟩ := exists_endpoint_interior_unitTriangle_le_sum hzi hwT
    (hp.normalized_nonincident_edge_inter_corner_subset k hk0 hkl f hfk hfp hfs i hik his)
  obtain ⟨l, hcl⟩ : ∃ l : Fin (n + 2), c = f (p l) := by
    rcases hc with hc | hc
    · exact ⟨i.castSucc, hc⟩
    · exact ⟨i.succ, hc⟩
  rw [hcl] at hcT hcH
  have hcoords := hcT
  rw [interior_unitTriangle] at hcoords
  have hlk : l ≠ k := by
    intro heq
    rw [heq, hfk] at hcoords
    exact (lt_irrefl 0) hcoords.1
  have hlp : l ≠ (finRotate (n + 2)).symm k := by
    intro heq
    rw [heq, hfp] at hcoords
    exact (lt_irrefl 0) hcoords.2.1
  have hls : l ≠ finRotate (n + 2) k := by
    intro heq
    rw [heq, hfs] at hcoords
    exact (lt_irrefl 0) hcoords.1
  exact (not_lt_of_ge (hmin l hlk hlp hls (interior_subset hcT))) (hcH.trans_lt hwH)



theorem IsSimplePolygonalArc.openSegment_disjoint_arcBoundary_of_minimal_triangle_vertex
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    (j : Fin (n + 2)) (hjk : j ≠ k) (hjp : j ≠ (finRotate (n + 2)).symm k)
    (hjs : j ≠ finRotate (n + 2) k) (hjT : f (p j) ∈ unitTriangle)
    (hmin : ∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
      l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
        (f (p j)).1 + (f (p j)).2 ≤ (f (p l)).1 + (f (p l)).2) :
    Disjoint (openSegment ℝ (p k) (p j)) (polygonArcBoundary p) := by
  have hpos := hp.normalized_triangle_vertex_pos k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT
  have hdis := hp.normalized_low_triangle_disjoint_arcBoundary k hk0 hkl f hfk hfp hfs
    (add_pos hpos.1 hpos.2) hjT.2.2 hmin
  apply Set.disjoint_left.mpr
  intro z hz hzB
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hfz : f (AffineMap.lineMap (p k) (p j) t) =
      (t * (f (p j)).1, t * (f (p j)).2) := by
    have h := f.toAffineEquiv.toAffineMap.apply_lineMap (p k) (p j) t
    change f (AffineMap.lineMap (p k) (p j) t) =
      AffineMap.lineMap (f (p k)) (f (p j)) t at h
    rw [h, hfk]
    ext <;> simp [AffineMap.lineMap_apply_module]
  apply Set.disjoint_left.mp hdis _ (mem_image_of_mem f hzB)
  rw [hfz]
  refine ⟨mul_pos ht.1 hpos.1, mul_pos ht.1 hpos.2, ?_⟩
  dsimp only
  nlinarith [mul_pos (sub_pos.mpr ht.2) (add_pos hpos.1 hpos.2)]



theorem IsSimplePolygonalArc.normalized_triangle_inter_arcBoundary_eq_corner
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    (hempty : ∀ j, f (p j) ∈ unitTriangle →
      j = k ∨ j = (finRotate (n + 2)).symm k ∨ j = finRotate (n + 2) k) :
    unitTriangle ∩ (f '' polygonArcBoundary p) = unitCorner := by
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have himage (i : Fin (n + 1)) : f '' p.edgeSet ℝ i.castSucc =
      segment ℝ (f (p i.castSucc)) (f (p i.succ)) := by
    rw [polygon_arcEdge_eq_segment]
    exact image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  have hpred : f '' p.edgeSet ℝ a.castSucc = segment ℝ (0, 0) (1, 0) := by
    rw [himage, hap, hak, hfp, hfk, segment_symm]
  have hsucc : f '' p.edgeSet ℝ b.castSucc = segment ℝ (0, 0) (0, 1) := by
    rw [himage, hbk, hbs, hfk, hfs]
  have hlow := hp.normalized_low_triangle_disjoint_arcBoundary k hk0 hkl f hfk hfp hfs
    zero_lt_one le_rfl (fun j hjk hjp hjs hjT =>
      ((hempty j hjT).elim hjk (fun h => h.elim hjp hjs)).elim)
  have hdis : Disjoint (interior unitTriangle) (f '' polygonArcBoundary p) := by
    simpa only [interior_unitTriangle] using hlow
  apply subset_antisymm
  · intro w hw
    by_contra hwC
    have hx : 0 < w.1 := by
      by_contra! h
      have heq : w.1 = 0 := le_antisymm h hw.1.1
      exact hwC ((mem_unitCorner_iff w).mpr
        (Or.inr ⟨heq, hw.1.2.1, by linarith [hw.1.2.2]⟩))
    have hy : 0 < w.2 := by
      by_contra! h
      have heq : w.2 = 0 := le_antisymm h hw.1.2.1
      exact hwC ((mem_unitCorner_iff w).mpr
        (Or.inl ⟨hw.1.1, by linarith [hw.1.2.2], heq⟩))
    have hH : w.1 + w.2 = 1 := by
      apply le_antisymm hw.1.2.2
      by_contra! h
      exact Set.disjoint_left.mp hdis
        (by rw [interior_unitTriangle]; exact ⟨hx, hy, h⟩) hw.2
    obtain ⟨z, hzB, hzw⟩ := hw.2
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzB
    have hwi : w ∈ segment ℝ (f (p i.castSucc)) (f (p i.succ)) := by
      rw [← himage]
      exact ⟨z, hi, hzw⟩
    have hik : i.castSucc ≠ k := by
      intro heq
      have hnext : i.succ = finRotate (n + 2) k := by
        have hrot : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
        rw [← heq, hrot]
      rw [heq, hnext, hfk, hfs] at hwi
      exact hwC (Or.inr hwi)
    have his : i.succ ≠ k := by
      intro heq
      have hprev : i.castSucc = (finRotate (n + 2)).symm k := by
        apply (finRotate (n + 2)).injective
        have hrot : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
        rw [hrot, heq, Equiv.apply_symm_apply]
      rw [hprev, heq, hfp, hfk, segment_symm] at hwi
      exact hwC (Or.inl hwi)
    have hkedge : p k ∉ p.edgeSet ℝ i.castSucc := by
      intro h
      exact ((hp.vertex_mem_edgeSet_iff k i).mp h).elim
        (fun hh => hik hh.symm) (fun hh => his hh.symm)
    have himB : segment ℝ (f (p i.castSucc)) (f (p i.succ)) ⊆
        f '' polygonArcBoundary p := by
      rw [← himage]
      exact image_mono (polygon_arcEdge_subset_boundary p i)
    have hsegdis := hdis.symm.mono_left himB
    have hend : ∀ c ∈ ({f (p i.castSucc), f (p i.succ)} : Set (ℝ × ℝ)),
        c ∈ unitTriangle → c ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
      intro c hc hcT
      obtain ⟨l, hl, hcl⟩ : ∃ l : Fin (n + 2),
          p l ∈ p.edgeSet ℝ i.castSucc ∧ c = f (p l) := by
        rcases hc with hc | hc
        · refine ⟨i.castSucc, ?_, hc⟩
          rw [polygon_arcEdge_eq_segment]
          exact left_mem_segment ℝ _ _
        · refine ⟨i.succ, ?_, hc⟩
          rw [polygon_arcEdge_eq_segment]
          exact right_mem_segment ℝ _ _
      rw [hcl] at hcT ⊢
      rcases hempty l hcT with rfl | rfl | rfl
      · exact (hkedge hl).elim
      · exact Or.inl hfp
      · exact Or.inr hfs
    have hinc : segment ℝ (f (p i.castSucc)) (f (p i.succ)) ∩ {(1, 0), (0, 1)} ⊆
        {f (p i.castSucc), f (p i.succ)} := by
      intro c hc
      obtain ⟨l, hcl⟩ : ∃ l : Fin (n + 2), c = f (p l) := by
        rcases hc.2 with hc | hc
        · exact ⟨(finRotate (n + 2)).symm k, hc.trans hfp.symm⟩
        · exact ⟨finRotate (n + 2) k, hc.trans hfs.symm⟩
      have hl : p l ∈ p.edgeSet ℝ i.castSucc := by
        have hmem := hc.1
        rw [hcl, ← himage] at hmem
        obtain ⟨v, hv, heq⟩ := hmem
        exact f.injective heq ▸ hv
      rcases (hp.vertex_mem_edgeSet_iff l i).mp hl with heq | heq
      · exact Or.inl (by rw [hcl, heq])
      · right
        change c = f (p i.succ)
        rw [hcl, heq]
    have hgap : ((finRotate (n + 2)).symm k).val + 2 =
        (finRotate (n + 2) k).val := by
      have h1 := congrArg Fin.val hak
      have h2 := congrArg Fin.val hbk
      have h3 := congrArg Fin.val hap
      have h4 := congrArg Fin.val hbs
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2 h3 h4
      omega
    rcases unit_base_endpoints_of_segment_base_hit hwi ⟨hx, hy⟩ hH hsegdis hend hinc with
      ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h1 := congrArg Fin.val (hp.vertices_injective (f.injective (ha.trans hfp.symm)))
      have h2 := congrArg Fin.val (hp.vertices_injective (f.injective (hb.trans hfs.symm)))
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
    · have h1 := congrArg Fin.val (hp.vertices_injective (f.injective (ha.trans hfs.symm)))
      have h2 := congrArg Fin.val (hp.vertices_injective (f.injective (hb.trans hfp.symm)))
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
  · intro w hw
    refine ⟨?_, ?_⟩
    · rcases (mem_unitCorner_iff w).mp hw with h | h
      · exact ⟨h.1, by linarith [h.2.2], by linarith [h.2.1, h.2.2]⟩
      · exact ⟨by linarith [h.1], h.2.1, by linarith [h.1, h.2.2]⟩
    · rcases hw with hw | hw
      · exact image_mono (polygon_arcEdge_subset_boundary p a) (hpred.symm ▸ hw)
      · exact image_mono (polygon_arcEdge_subset_boundary p b) (hsucc.symm ▸ hw)



theorem IsSimplePolygonalArc.exists_minimal_triangle_vertex_of_not_admissible
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (f : E ≃ᴬ[ℝ] (ℝ × ℝ))
    (hfk : f (p k) = (0, 0))
    (hfp : f (p ((finRotate (n + 2)).symm k)) = (1, 0))
    (hfs : f (p (finRotate (n + 2) k)) = (0, 1))
    (hnot : ¬ IsAdmissibleArcVertex p k) :
    ∃ j : Fin (n + 2), j ≠ k ∧ j ≠ (finRotate (n + 2)).symm k ∧
      j ≠ finRotate (n + 2) k ∧ f (p j) ∈ unitTriangle ∧
      0 < (f (p j)).1 ∧ 0 < (f (p j)).2 ∧
      (∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
        l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
          (f (p j)).1 + (f (p j)).2 ≤ (f (p l)).1 + (f (p l)).2) ∧
      Disjoint (openSegment ℝ (p k) (p j)) (polygonArcBoundary p) := by
  classical
  have hnorm : f '' polygonVertexTriangle p k = unitTriangle := by
    have him := f.toAffineEquiv.toAffineMap.image_convexHull
      {p k, p ((finRotate (n + 2)).symm k), p (finRotate (n + 2) k)}
    change f '' polygonVertexTriangle p k =
      convexHull ℝ (f '' {p k, p ((finRotate (n + 2)).symm k),
        p (finRotate (n + 2) k)}) at him
    rw [him, image_insert_eq, image_insert_eq, image_singleton, hfk, hfp, hfs,
      ← unitTriangle_eq_convexHull]
  let S := Finset.univ.filter fun l => l ≠ k ∧ l ≠ (finRotate (n + 2)).symm k ∧
    l ≠ finRotate (n + 2) k ∧ f (p l) ∈ unitTriangle
  have hS (l : Fin (n + 2)) : l ∈ S ↔ l ≠ k ∧ l ≠ (finRotate (n + 2)).symm k ∧
      l ≠ finRotate (n + 2) k ∧ f (p l) ∈ unitTriangle := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hSne : S.Nonempty := by
    by_contra hem
    have hempty (j : Fin (n + 2)) (hj : f (p j) ∈ unitTriangle) :
        j = k ∨ j = (finRotate (n + 2)).symm k ∨ j = finRotate (n + 2) k := by
      by_contra hn
      push Not at hn
      exact hem ⟨j, (hS j).mpr ⟨hn.1, hn.2.1, hn.2.2, hj⟩⟩
    have hinc := hp.normalized_triangle_inter_arcBoundary_eq_corner
      k hk0 hkl f hfk hfp hfs hempty
    apply hnot
    refine ⟨hk0, hkl, subset_antisymm ?_
      (polygonArcIncidentEdges_subset_triangle_inter_boundary p k hk0 hkl)⟩
    rintro z ⟨hzT, hzB⟩
    have hfz : f z ∈ unitCorner := hinc ▸
      (show f z ∈ unitTriangle ∩ (f '' polygonArcBoundary p) from
        ⟨hnorm ▸ mem_image_of_mem f hzT, mem_image_of_mem f hzB⟩)
    have hback (x : E) (hx : f z ∈ segment ℝ (f (p k)) (f x)) :
        z ∈ segment ℝ (p k) x := by
      have him := image_segment ℝ f.toAffineEquiv.toAffineMap (p k) x
      change f '' segment ℝ (p k) x = segment ℝ (f (p k)) (f x) at him
      rw [← him] at hx
      obtain ⟨w, hw, heq⟩ := hx
      exact f.injective heq ▸ hw
    rcases hfz with h | h
    · exact Or.inl (hback _ (by rwa [hfk, hfp]))
    · exact Or.inr (hback _ (by rwa [hfk, hfs]))
  obtain ⟨j, hjS, hjmin⟩ := S.exists_min_image (fun l => (f (p l)).1 + (f (p l)).2) hSne
  obtain ⟨hjk, hjp, hjs, hjT⟩ := (hS j).mp hjS
  have hpos := hp.normalized_triangle_vertex_pos k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT
  have hmin : ∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
      l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
        (f (p j)).1 + (f (p j)).2 ≤ (f (p l)).1 + (f (p l)).2 :=
    fun l hlk hlp hls hlT => hjmin l ((hS l).mpr ⟨hlk, hlp, hls, hlT⟩)
  exact ⟨j, hjk, hjp, hjs, hjT, hpos.1, hpos.2, hmin,
    hp.openSegment_disjoint_arcBoundary_of_minimal_triangle_vertex
      k hk0 hkl f hfk hfp hfs j hjk hjp hjs hjT hmin⟩

end PoincareConjecture.M25.Topology3D
