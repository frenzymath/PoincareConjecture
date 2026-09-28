import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CyclicDistance











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {n : ℕ}


def polygonCut {E : Type*} (p : Polygon E n) (a b : Fin n) :
    Polygon E (cyclicDistance a b + 1) := polygonArc p a (cyclicDistance a b)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem polygonCut_boundary (p : Polygon E n) (a b : Fin n) :
    (polygonCut p a b).boundary ℝ =
      (⋃ (i : Fin n) (_ : cyclicDistance a i < cyclicDistance a b), p.edgeSet ℝ i) ∪
        segment ℝ (p a) (p b) := by
  unfold polygonCut
  rw [polygonArc_boundary, iterate_cyclicDistance, segment_symm]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨cyclicArcIndex a (cyclicDistance a b) j.castSucc,
      mem_iUnion.mpr ⟨?_, hj⟩⟩
    exact (mem_range_cyclicArcEdgeIndex_iff a _ (cyclicDistance_lt a b) _).mp ⟨j, rfl⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨hindex, hxedge⟩ := mem_iUnion.mp hi
    obtain ⟨j, rfl⟩ :=
      (mem_range_cyclicArcEdgeIndex_iff a _ (cyclicDistance_lt a b) i).mpr hindex
    exact mem_iUnion.mpr ⟨j, hxedge⟩


theorem polygonCut_boundary_union (p : Polygon E n) (a b : Fin n) (hab : b ≠ a) :
    (polygonCut p a b).boundary ℝ ∪ (polygonCut p b a).boundary ℝ =
      p.boundary ℝ ∪ segment ℝ (p a) (p b) := by
  have hcover (i : Fin n) :
      cyclicDistance a i < cyclicDistance a b ∨ cyclicDistance b i < cyclicDistance b a := by
    have hi := ((cyclicArc_edgeIndex_partition a b hab).2).symm ▸ mem_univ i
    rcases hi with hi | hi
    · exact Or.inl ((mem_range_cyclicArcEdgeIndex_iff a _ (cyclicDistance_lt a b) i).mp hi)
    · exact Or.inr ((mem_range_cyclicArcEdgeIndex_iff b _ (cyclicDistance_lt b a) i).mp hi)
  rw [polygonCut_boundary, polygonCut_boundary, segment_symm ℝ (p b) (p a)]
  apply subset_antisymm
  · intro x hx
    rcases hx with (hx | hx) | (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨_, hxedge⟩ := mem_iUnion.mp hi
      exact Or.inl (polygon_edgeSet_subset_boundary p i hxedge)
    · exact Or.inr hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨_, hxedge⟩ := mem_iUnion.mp hi
      exact Or.inl (polygon_edgeSet_subset_boundary p i hxedge)
    · exact Or.inr hx
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p x).mp hx
      rcases hcover i with hia | hib
      · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hia, hi⟩⟩))
      · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hib, hi⟩⟩))
    · exact Or.inl (Or.inr hx)


theorem IsSimplePolygon.polygonCut_boundary_inter {p : Polygon E n}
    (hp : IsSimplePolygon p) (a b : Fin n) (hab : b ≠ a) :
    (polygonCut p a b).boundary ℝ ∩ (polygonCut p b a).boundary ℝ =
      segment ℝ (p a) (p b) := by
  have hend (c d i : Fin n) (hi : cyclicDistance c i < cyclicDistance c d)
      {x : E} (hx : x ∈ ({p i, p (finRotate n i)} : Set E)) :
      ∃ l, l ∈ range (cyclicArcIndex c (cyclicDistance c d)) ∧ x = p l := by
    obtain ⟨t, rfl⟩ :=
      (mem_range_cyclicArcEdgeIndex_iff c _ (cyclicDistance_lt c d) i).mpr hi
    rcases hx with hx | hx
    · exact ⟨cyclicArcIndex c (cyclicDistance c d) t.castSucc, ⟨t.castSucc, rfl⟩, hx⟩
    · refine ⟨cyclicArcIndex c (cyclicDistance c d) t.succ, ⟨t.succ, rfl⟩, ?_⟩
      rw [cyclicArcIndex_succ]
      exact hx
  rw [polygonCut_boundary, polygonCut_boundary, segment_symm ℝ (p b) (p a)]
  apply subset_antisymm
  · intro x hx
    rcases hx.1 with ha | ha
    · rcases hx.2 with hb | hb
      · obtain ⟨i, hi⟩ := mem_iUnion.mp ha
        obtain ⟨hia, hxi⟩ := mem_iUnion.mp hi
        obtain ⟨j, hj⟩ := mem_iUnion.mp hb
        obtain ⟨hjb, hxj⟩ := mem_iUnion.mp hj
        have hij : i ≠ j := by
          intro heq
          subst j
          exact Set.disjoint_left.mp (cyclicArc_edgeIndex_partition a b hab).1
            ((mem_range_cyclicArcEdgeIndex_iff a _ (cyclicDistance_lt a b) i).mpr hia)
            ((mem_range_cyclicArcEdgeIndex_iff b _ (cyclicDistance_lt b a) i).mpr hjb)
        have hends := hp.edges_inter i j hij ⟨hxi, hxj⟩
        obtain ⟨l, hl, hxl⟩ := hend a b i hia hends.1
        obtain ⟨r, hr, hxr⟩ := hend b a j hjb hends.2
        have hlr : l = r := hp.vertices_injective (hxl.symm.trans hxr)
        subst r
        have hlab : l ∈ ({a, b} : Set (Fin n)) :=
          (cyclicArc_vertexIndex_inter a b hab) ▸ ⟨hl, hr⟩
        rcases hlab with rfl | rfl
        · rw [hxl]
          exact left_mem_segment ℝ _ _
        · rw [hxl]
          exact right_mem_segment ℝ _ _
      · exact hb
    · exact ha
  · intro x hx
    exact ⟨Or.inr hx, Or.inr hx⟩



theorem IsSimplePolygon.polygonCut_pair {p : Polygon E n} (hp : IsSimplePolygon p)
    (a b : Fin n) (hab : b ≠ a) (hs : b ≠ finRotate n a)
    (hp' : b ≠ (finRotate n).symm a)
    (hdiag : Disjoint (openSegment ℝ (p a) (p b)) (p.boundary ℝ)) :
    cyclicDistance a b + 1 < n ∧ cyclicDistance b a + 1 < n ∧
      IsSimplePolygon (polygonCut p a b) ∧ IsSimplePolygon (polygonCut p b a) := by
  have hbs : a ≠ finRotate n b := by
    intro h
    apply hp'
    simpa only [Equiv.symm_apply_apply] using (congrArg (finRotate n).symm h).symm
  have hbp : a ≠ (finRotate n).symm b := by
    intro h
    apply hs
    simpa only [Equiv.apply_symm_apply] using (congrArg (finRotate n) h).symm
  obtain ⟨hm2, hmn⟩ := cyclicDistance_nonadjacent_bounds a b hab hs hp'
  obtain ⟨hl2, hln⟩ := cyclicDistance_nonadjacent_bounds b a hab.symm hbs hbp
  refine ⟨hmn, hln, ?_, ?_⟩
  · apply hp.isSimple_polygonArc a _ hm2 (cyclicDistance_lt a b)
    simpa only [iterate_cyclicDistance] using hdiag
  · apply hp.isSimple_polygonArc b _ hl2 (cyclicDistance_lt b a)
    simpa only [iterate_cyclicDistance, openSegment_symm] using hdiag

end PoincareConjecture.M25.Topology3D
