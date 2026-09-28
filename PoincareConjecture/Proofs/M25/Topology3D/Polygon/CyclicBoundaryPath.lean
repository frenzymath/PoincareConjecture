import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CyclicDistance










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}


def polygonCyclicPathBoundary (p : Polygon E n) (a b : Fin n) : Set E :=
  ⋃ i : Fin (cyclicDistance a b),
    p.edgeSet ℝ (cyclicArcIndex a (cyclicDistance a b) i.castSucc)



theorem polygonCyclicPathBoundary_subset_boundary (p : Polygon E n) (a b : Fin n) :
    polygonCyclicPathBoundary p a b ⊆ p.boundary ℝ := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact polygon_edgeSet_subset_boundary p _ hi


theorem polygonCyclicPathBoundary_isCompact (p : Polygon E n) (a b : Fin n) :
    IsCompact (polygonCyclicPathBoundary p a b) :=
  isCompact_iUnion (fun _ => polygon_edgeSet_isCompact p _)

private theorem cyclic_path_distance_pos (a b : Fin n) (hab : b ≠ a) :
    0 < cyclicDistance a b := by
  by_contra h
  have hz : cyclicDistance a b = 0 := by omega
  have hreach := iterate_cyclicDistance a b
  rw [hz] at hreach
  exact hab hreach.symm

private theorem cyclic_path_vertex_mem (p : Polygon E n) (a b : Fin n) (hab : b ≠ a)
    (i : Fin (cyclicDistance a b + 1)) :
    p (cyclicArcIndex a (cyclicDistance a b) i) ∈ polygonCyclicPathBoundary p a b := by
  have hd := cyclic_path_distance_pos a b hab
  refine Fin.lastCases ?_ (fun j => ?_) i
  · let j : Fin (cyclicDistance a b) := ⟨cyclicDistance a b - 1, by omega⟩
    have hj : j.succ = Fin.last (cyclicDistance a b) := by
      apply Fin.ext
      dsimp [j]
      omega
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [← hj, cyclicArcIndex_succ]
    exact polygon_right_mem_edgeSet p _
  · exact mem_iUnion.mpr ⟨j, polygon_left_mem_edgeSet p _⟩



theorem polygonCyclicPathBoundary_endpoints (p : Polygon E n) (a b : Fin n)
    (hab : b ≠ a) :
    p a ∈ polygonCyclicPathBoundary p a b ∧ p b ∈ polygonCyclicPathBoundary p a b := by
  have ha := cyclic_path_vertex_mem p a b hab 0
  have hb := cyclic_path_vertex_mem p a b hab (Fin.last (cyclicDistance a b))
  constructor
  · simpa only [cyclicArcIndex_zero] using ha
  · simpa only [cyclicArcIndex_last, iterate_cyclicDistance] using hb



theorem polygonCyclicPathBoundary_union (p : Polygon E n) (a b : Fin n) (hab : b ≠ a) :
    polygonCyclicPathBoundary p a b ∪ polygonCyclicPathBoundary p b a = p.boundary ℝ := by
  apply subset_antisymm
  · exact union_subset (polygonCyclicPathBoundary_subset_boundary p a b)
      (polygonCyclicPathBoundary_subset_boundary p b a)
  · intro x hx
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p x).mp hx
    have hindex : i ∈
        range (fun j : Fin (cyclicDistance a b) =>
          cyclicArcIndex a (cyclicDistance a b) j.castSucc) ∪
        range (fun j : Fin (cyclicDistance b a) =>
          cyclicArcIndex b (cyclicDistance b a) j.castSucc) :=
      (cyclicArc_edgeIndex_partition a b hab).2.symm ▸ mem_univ i
    rcases hindex with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (mem_iUnion.mpr ⟨j, hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨j, hi⟩)



theorem IsSimplePolygon.polygonCyclicPathBoundary_inter {p : Polygon E n}
    (hp : IsSimplePolygon p) (a b : Fin n) (hab : b ≠ a) :
    polygonCyclicPathBoundary p a b ∩ polygonCyclicPathBoundary p b a = {p a, p b} := by
  have hend (c d : Fin n) (i : Fin (cyclicDistance c d)) {x : E}
      (hx : x ∈ ({p (cyclicArcIndex c (cyclicDistance c d) i.castSucc),
        p (finRotate n (cyclicArcIndex c (cyclicDistance c d) i.castSucc))} : Set E)) :
      ∃ l, l ∈ range (cyclicArcIndex c (cyclicDistance c d)) ∧ x = p l := by
    rcases hx with hx | hx
    · exact ⟨_, ⟨i.castSucc, rfl⟩, hx⟩
    · refine ⟨_, ⟨i.succ, rfl⟩, ?_⟩
      rw [cyclicArcIndex_succ]
      exact hx
  apply subset_antisymm
  · rintro x ⟨hxA, hxB⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
    have hij : cyclicArcIndex a (cyclicDistance a b) i.castSucc ≠
        cyclicArcIndex b (cyclicDistance b a) j.castSucc := by
      intro h
      exact Set.disjoint_left.mp (cyclicArc_edgeIndex_partition a b hab).1
        ⟨i, rfl⟩ ⟨j, h.symm⟩
    have hends := hp.edges_inter _ _ hij ⟨hi, hj⟩
    obtain ⟨l, hl, hxl⟩ := hend a b i hends.1
    obtain ⟨r, hr, hxr⟩ := hend b a j hends.2
    have hlr : l = r := hp.vertices_injective (hxl.symm.trans hxr)
    subst r
    have hlab : l ∈ ({a, b} : Set (Fin n)) :=
      (cyclicArc_vertexIndex_inter a b hab) ▸ ⟨hl, hr⟩
    rcases hlab with rfl | rfl
    · exact Or.inl hxl
    · exact Or.inr hxl
  · have hA := polygonCyclicPathBoundary_endpoints p a b hab
    have hB := polygonCyclicPathBoundary_endpoints p b a hab.symm
    rintro x (rfl | rfl)
    · exact ⟨hA.1, hB.2⟩
    · exact ⟨hA.2, hB.1⟩



theorem IsSimplePolygon.vertex_mem_polygonCyclicPathBoundary_iff {p : Polygon E n}
    (hp : IsSimplePolygon p) (a b : Fin n) (hab : b ≠ a) (i : Fin n) :
    p i ∈ polygonCyclicPathBoundary p a b ↔ cyclicDistance a i ≤ cyclicDistance a b := by
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    apply (mem_range_cyclicArcIndex_iff a _ (cyclicDistance_lt a b) i).mp
    rcases (hp.vertex_mem_edgeSet_iff i _).mp hj with hi | hi
    · exact ⟨j.castSucc, hi.symm⟩
    · refine ⟨j.succ, ?_⟩
      rw [cyclicArcIndex_succ]
      exact hi.symm
  · intro hi
    obtain ⟨j, hj⟩ :=
      (mem_range_cyclicArcIndex_iff a _ (cyclicDistance_lt a b) i).mpr hi
    rw [← hj]
    exact cyclic_path_vertex_mem p a b hab j

end PoincareConjecture.M25.Topology3D
