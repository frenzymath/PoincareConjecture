import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsSimplePolygonalArc.terminal_path_isSimplePolygon {n k : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p) (hk : 2 ≤ k)
    (c : Fin (k + 1) ↪ Fin (n + 2))
    (hint : ∀ i, c i ≠ 0 ∧ c i ≠ Fin.last (n + 1))
    (hadj : c (Fin.last k) = (finRotate (n + 2)).symm (c 0) ∨
      c (Fin.last k) = finRotate (n + 2) (c 0))
    (hwnot : (if c (Fin.last k) = (finRotate (n + 2)).symm (c 0)
      then finRotate (n + 2) (c 0) else (finRotate (n + 2)).symm (c 0)) ∉ range c)
    (hvis : ∀ j : Fin k,
      Disjoint (openSegment ℝ (p (c j.castSucc)) (p (c j.succ))) (polygonArcBoundary p))
    (hinc : ∀ i j : Fin k, i ≠ j →
      segment ℝ (p (c i.castSucc)) (p (c i.succ)) ∩
          segment ℝ (p (c j.castSucc)) (p (c j.succ)) =
        {p (c i.castSucc), p (c i.succ)} ∩ {p (c j.castSucc), p (c j.succ)}) :
    let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
    let σ := segment ℝ (p (c (Fin.last k))) (p (c 0))
    IsSimplePolygon r ∧
      (∀ j : Fin k, r.edgeSet ℝ j.castSucc =
        segment ℝ (p (c j.castSucc)) (p (c j.succ))) ∧
      r.edgeSet ℝ (Fin.last k) = σ ∧
      r.boundary ℝ = (⋃ j : Fin k, segment ℝ (p (c j.castSucc)) (p (c j.succ))) ∪ σ ∧
      r.boundary ℝ ∩ polygonArcBoundary p = range r ∪ σ ∧
      p (if c (Fin.last k) = (finRotate (n + 2)).symm (c 0)
        then finRotate (n + 2) (c 0) else (finRotate (n + 2)).symm (c 0)) ∉
          r.boundary ℝ := by
  classical
  let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
  let u := c 0
  let v := c (Fin.last k)
  let w := if v = (finRotate (n + 2)).symm u
    then finRotate (n + 2) u else (finRotate (n + 2)).symm u
  let σ := segment ℝ (p v) (p u)
  have hr (i : Fin (k + 1)) : r i = p (c i) := rfl
  have hnext (j : Fin k) : finRotate (k + 1) j.castSucc = j.succ :=
    finRotate_of_lt j.isLt
  have hedge (j : Fin k) : r.edgeSet ℝ j.castSucc =
      segment ℝ (p (c j.castSucc)) (p (c j.succ)) := by
    rw [polygon_edgeSet_eq_segment, hnext, hr, hr]
  have hlast : r.edgeSet ℝ (Fin.last k) = σ := by
    rw [polygon_edgeSet_eq_segment, finRotate_last]
  have hσedge : ∃ e : Fin (n + 1), σ = p.edgeSet ℝ e.castSucc ∧
      ((e.castSucc = u ∧ e.succ = v) ∨ (e.castSucc = v ∧ e.succ = u)) := by
    obtain ⟨a, b, hau, hbu, hap, hbs, _⟩ :=
      exists_arc_incident_edge_indices u (hint 0).1 (hint 0).2
    rcases hadj with h | h
    · change v = (finRotate (n + 2)).symm u at h
      refine ⟨a, ?_, Or.inr ⟨hap.trans h.symm, hau⟩⟩
      change segment ℝ (p v) (p u) = _
      rw [polygon_arcEdge_eq_segment, hap, hau, ← h]
    · change v = finRotate (n + 2) u at h
      refine ⟨b, ?_, Or.inl ⟨hbu, hbs.trans h.symm⟩⟩
      change segment ℝ (p v) (p u) = _
      rw [polygon_arcEdge_eq_segment, hbu, hbs, ← h]
      exact segment_symm ℝ _ _
  obtain ⟨e, hσeq, he⟩ := hσedge
  have hσG : σ ⊆ polygonArcBoundary p := by
    rw [hσeq]
    exact polygon_arcEdge_subset_boundary p e
  have hσvertex (i : Fin (n + 2)) (hi : p i ∈ σ) : i = u ∨ i = v := by
    rw [hσeq] at hi
    have hh := (hp.vertex_mem_edgeSet_iff i e).mp hi
    rcases he with ⟨he0, he1⟩ | ⟨he0, he1⟩
    · simpa only [he0, he1] using hh
    · simpa only [he0, he1, or_comm] using hh
  have hauxEnds (j : Fin k) {x : E} (hx : x ∈ r.edgeSet ℝ j.castSucc)
      (hxG : x ∈ polygonArcBoundary p) : x ∈ ({r j.castSucc, r j.succ} : Set E) := by
    rw [hedge, ← insert_endpoints_openSegment] at hx
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
    · exact (Set.disjoint_left.mp (hvis j) hx hxG).elim
  have hσends (j : Fin (k + 1)) (hj : r j ∈ σ) :
      r j ∈ ({r (Fin.last k), r 0} : Set E) := by
    rcases hσvertex (c j) hj with h | h
    · exact Or.inr (congrArg p h)
    · exact Or.inl (congrArg p h)
  have hmixed (j : Fin k) :
      r.edgeSet ℝ (Fin.last k) ∩ r.edgeSet ℝ j.castSucc ⊆
        {r (Fin.last k), r 0} ∩ {r j.castSucc, r j.succ} := by
    rintro x ⟨hxlast, hxj⟩
    have hxσ : x ∈ σ := hlast ▸ hxlast
    have hxends := hauxEnds j hxj (hσG hxσ)
    refine ⟨?_, hxends⟩
    rcases hxends with rfl | rfl
    · exact hσends _ hxσ
    · exact hσends _ hxσ
  have hsimple : IsSimplePolygon r := by
    refine ⟨by omega, hp.vertices_injective.comp c.injective, ?_⟩
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
        rw [hedge, hedge]
        simpa only [hr, hnext] using
          (hinc a b (fun h => hne (congrArg (fun j : Fin k => j.castSucc) h))).le
  have hboundary : r.boundary ℝ =
      (⋃ j : Fin k, segment ℝ (p (c j.castSucc)) (p (c j.succ))) ∪ σ := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff r x).mp hx
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        exact Or.inr (hlast ▸ hi)
      · intro hi
        exact Or.inl (mem_iUnion.mpr ⟨j, hedge j ▸ hi⟩)
    · rintro x (hx | hx)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact polygon_edgeSet_subset_boundary r j.castSucc ((hedge j).symm ▸ hj)
      · exact polygon_edgeSet_subset_boundary r (Fin.last k) (hlast.symm ▸ hx)
  have hcontact : r.boundary ℝ ∩ polygonArcBoundary p = range r ∪ σ := by
    apply subset_antisymm
    · rintro x ⟨hxC, hxG⟩
      rw [hboundary] at hxC
      rcases hxC with hx | hx
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        rcases hauxEnds j ((hedge j).symm ▸ hj) hxG with rfl | rfl
        · exact Or.inl ⟨j.castSucc, rfl⟩
        · exact Or.inl ⟨j.succ, rfl⟩
      · exact Or.inr hx
    · rintro x (⟨j, rfl⟩ | hx)
      · exact ⟨polygon_vertex_mem_boundary r j, polygon_vertex_mem_arcBoundary p (c j)⟩
      · exact ⟨polygon_edgeSet_subset_boundary r (Fin.last k) (hlast.symm ▸ hx), hσG hx⟩
  refine ⟨hsimple, hedge, hlast, hboundary, hcontact, ?_⟩
  change p w ∉ r.boundary ℝ
  intro hwC
  have hwcontact : p w ∈ range r ∪ σ :=
    hcontact ▸ ⟨hwC, polygon_vertex_mem_arcBoundary p w⟩
  rcases hwcontact with ⟨j, hj⟩ | hwσ
  · exact hwnot ⟨j, hp.vertices_injective hj⟩
  · rcases hσvertex w hwσ with hw | hw
    · exact hwnot ⟨0, hw.symm⟩
    · exact hwnot ⟨Fin.last k, hw.symm⟩

end PoincareConjecture.M25.Topology3D
