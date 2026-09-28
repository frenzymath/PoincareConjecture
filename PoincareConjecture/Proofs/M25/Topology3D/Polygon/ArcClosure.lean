import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PolygonalArc










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem IsSimplePolygonalArc.isSimplePolygon_of_closing_disjoint {k : ℕ}
    {q : Polygon E (k + 2)} (hq : IsSimplePolygonalArc q)
    (hclose : Disjoint (openSegment ℝ (q (Fin.last (k + 1))) (q 0))
      (polygonArcBoundary q)) :
    3 ≤ k + 2 ∧ IsSimplePolygon q ∧
      q.boundary ℝ = polygonArcBoundary q ∪
        segment ℝ (q (Fin.last (k + 1))) (q 0) := by
  have hlast : q.edgeSet ℝ (Fin.last (k + 1)) =
      segment ℝ (q (Fin.last (k + 1))) (q 0) := by
    rw [polygon_edgeSet_eq_segment, finRotate_last]
  have hnext (i : Fin (k + 1)) : finRotate (k + 2) i.castSucc = i.succ :=
    finRotate_of_lt i.isLt
  have hboundary : q.boundary ℝ = polygonArcBoundary q ∪
      segment ℝ (q (Fin.last (k + 1))) (q 0) := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff q x).mp hx
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        exact Or.inr (hlast ▸ hi)
      · intro hi
        exact Or.inl (polygon_arcEdge_subset_boundary q j hi)
    · rintro x (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact polygon_edgeSet_subset_boundary q i.castSucc hi
      · exact polygon_edgeSet_subset_boundary q (Fin.last (k + 1)) (hlast.symm ▸ hx)
  have hthree : 3 ≤ k + 2 := by
    by_contra h
    have hk : k = 0 := by omega
    subst k
    have hmid := midpoint_mem_openSegment (𝕜 := ℝ) (q (Fin.last 1)) (q 0)
    apply Set.disjoint_left.mp hclose hmid
    apply polygon_arcEdge_subset_boundary q (0 : Fin 1)
    rw [polygon_arcEdge_eq_segment, segment_symm]
    exact openSegment_subset_segment ℝ _ _ hmid
  have hmixed (i : Fin (k + 1)) :
      q.edgeSet ℝ (Fin.last (k + 1)) ∩ q.edgeSet ℝ i.castSucc ⊆
        {q (Fin.last (k + 1)), q 0} ∩ {q i.castSucc, q i.succ} := by
    rintro x ⟨hxlast, hxi⟩
    rw [hlast, ← insert_endpoints_openSegment] at hxlast
    rcases hxlast with rfl | rfl | hopen
    · refine ⟨Or.inl rfl, ?_⟩
      rcases (hq.vertex_mem_edgeSet_iff (Fin.last (k + 1)) i).mp hxi with hi | hi
      · exact Or.inl (congrArg q hi)
      · exact Or.inr (congrArg q hi)
    · refine ⟨Or.inr rfl, ?_⟩
      rcases (hq.vertex_mem_edgeSet_iff 0 i).mp hxi with hi | hi
      · exact Or.inl (congrArg q hi)
      · exact Or.inr (congrArg q hi)
    · exact (Set.disjoint_left.mp hclose hopen (polygon_arcEdge_subset_boundary q i hxi)).elim
  have hsimple : IsSimplePolygon q := by
    refine ⟨hthree, hq.vertices_injective, ?_⟩
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro hne
        exact (hne rfl).elim
      · intro _
        simpa only [finRotate_last, hnext] using hmixed b
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _ x hx
        have hh := hmixed a ⟨hx.2, hx.1⟩
        simpa only [finRotate_last, hnext, mem_inter_iff] using And.intro hh.2 hh.1
      · intro hne
        simpa only [hnext] using hq.edges_inter a b
          (fun hab => hne (congrArg (fun x : Fin (k + 1) => x.castSucc) hab))
  exact ⟨hthree, hsimple, hboundary⟩

end PoincareConjecture.M25.Topology3D
