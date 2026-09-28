import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PolygonalArc
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PushIn

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

theorem exists_arc_incident_edge_indices {n : ℕ} (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) :
    ∃ i j : Fin (n + 1), i.succ = k ∧ j.castSucc = k ∧
      i.castSucc = (finRotate (n + 2)).symm k ∧
      j.succ = finRotate (n + 2) k ∧ i ≠ j := by
  have hpos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk0 (Fin.ext h))
  have hlt : k.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hkl
  let i : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  let j : Fin (n + 1) := ⟨k.val, hlt⟩
  have hik : i.succ = k := Fin.ext (by change k.val - 1 + 1 = k.val; omega)
  have hjk : j.castSucc = k := Fin.ext rfl
  have hi : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
  have hj : finRotate (n + 2) j.castSucc = j.succ := finRotate_of_lt j.isLt
  refine ⟨i, j, hik, hjk, ?_, ?_, ?_⟩
  · exact (finRotate (n + 2)).injective (by rw [hi, hik, Equiv.apply_symm_apply])
  · rw [← hjk, hj]
  · intro hij
    have hv := congrArg Fin.val hij
    change k.val - 1 = k.val at hv
    omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem polygonArcIncidentEdges_subset_triangle_inter_boundary
    (p : Polygon E (n + 2)) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) :
    segment ℝ (p k) (p ((finRotate (n + 2)).symm k)) ∪
        segment ℝ (p k) (p (finRotate (n + 2) k)) ⊆
      polygonVertexTriangle p k ∩ polygonArcBoundary p := by
  obtain ⟨i, j, hik, hjk, hip, hjs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hconv : Convex ℝ (polygonVertexTriangle p k) := convex_convexHull ℝ _
  have hk : p k ∈ polygonVertexTriangle p k := subset_convexHull ℝ _ (by simp)
  have hp : p ((finRotate (n + 2)).symm k) ∈ polygonVertexTriangle p k :=
    subset_convexHull ℝ _ (by simp)
  have hs : p (finRotate (n + 2) k) ∈ polygonVertexTriangle p k :=
    subset_convexHull ℝ _ (by simp)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨hconv.segment_subset hk hp hx, polygon_arcEdge_subset_boundary p i ?_⟩
    rw [polygon_arcEdge_eq_segment, hip, hik, segment_symm]
    exact hx
  · refine ⟨hconv.segment_subset hk hs hx, polygon_arcEdge_subset_boundary p j ?_⟩
    rw [polygon_arcEdge_eq_segment, hjk, hjs]
    exact hx

theorem IsSimplePolygonalArc.vertex_mem_triangle_iff_of_admissible
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (had : IsAdmissibleArcVertex p k) (l : Fin (n + 2)) :
    p l ∈ polygonVertexTriangle p k ↔
      l = k ∨ l = (finRotate (n + 2)).symm k ∨ l = finRotate (n + 2) k := by
  obtain ⟨i, j, hik, hjk, hip, hjs, _⟩ :=
    exists_arc_incident_edge_indices k had.1 had.2.1
  constructor
  · intro hl
    have hb : p l ∈ polygonVertexTriangle p k ∩ polygonArcBoundary p :=
      ⟨hl, polygon_vertex_mem_arcBoundary p l⟩
    rw [had.2.2] at hb
    rcases hb with hb | hb
    · have he : p l ∈ p.edgeSet ℝ i.castSucc := by
        rw [polygon_arcEdge_eq_segment, hip, hik, segment_symm]
        exact hb
      have hh := (hp.vertex_mem_edgeSet_iff l i).mp he
      rw [hip, hik] at hh
      exact hh.elim (Or.inr ∘ Or.inl) Or.inl
    · have he : p l ∈ p.edgeSet ℝ j.castSucc := by
        rw [polygon_arcEdge_eq_segment, hjk, hjs]
        exact hb
      have hh := (hp.vertex_mem_edgeSet_iff l j).mp he
      rw [hjk, hjs] at hh
      exact hh.elim Or.inl (Or.inr ∘ Or.inr)
  · intro hl
    apply subset_convexHull ℝ _
    rcases hl with rfl | rfl | rfl <;> simp

theorem IsSimplePolygonalArc.triangle_inter_edge_subset_of_admissible
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (had : IsAdmissibleArcVertex p k) (l : Fin (n + 1))
    (hlk : l.castSucc ≠ k) (hls : l.succ ≠ k) :
    polygonVertexTriangle p k ∩ p.edgeSet ℝ l.castSucc ⊆
      {p ((finRotate (n + 2)).symm k), p (finRotate (n + 2) k)} ∩
        {p l.castSucc, p l.succ} := by
  obtain ⟨i, j, hik, hjk, hip, hjs, _⟩ :=
    exists_arc_incident_edge_indices k had.1 had.2.1
  have hil : i ≠ l := fun h => hls (h ▸ hik)
  have hjl : j ≠ l := fun h => hlk (h ▸ hjk)
  rintro z ⟨hzT, hzl⟩
  have hzk : z ≠ p k := by
    intro hz
    have hh := (hp.vertex_mem_edgeSet_iff k l).mp (hz ▸ hzl)
    exact hh.elim (fun h => hlk h.symm) (fun h => hls h.symm)
  have hb : z ∈ polygonVertexTriangle p k ∩ polygonArcBoundary p :=
    ⟨hzT, polygon_arcEdge_subset_boundary p l hzl⟩
  rw [had.2.2] at hb
  rcases hb with hb | hb
  · have hz : z ∈ p.edgeSet ℝ i.castSucc := by
      rw [polygon_arcEdge_eq_segment, hip, hik, segment_symm]
      exact hb
    have hh := hp.edges_inter i l hil ⟨hz, hzl⟩
    rw [hip, hik] at hh
    exact ⟨Or.inl (hh.1.resolve_right hzk), hh.2⟩
  · have hz : z ∈ p.edgeSet ℝ j.castSucc := by
      rw [polygon_arcEdge_eq_segment, hjk, hjs]
      exact hb
    have hh := hp.edges_inter j l hjl ⟨hz, hzl⟩
    rw [hjk, hjs] at hh
    exact ⟨Or.inr (hh.1.resolve_left hzk), hh.2⟩

theorem IsSimplePolygonalArc.isSimple_polygonReplaceVertex_of_admissible
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (had : IsAdmissibleArcVertex p k) (x : E) (hxT : x ∈ polygonVertexTriangle p k)
    (hxa : x ≠ p ((finRotate (n + 2)).symm k))
    (hxb : x ≠ p (finRotate (n + 2) k))
    (hinter : segment ℝ x (p ((finRotate (n + 2)).symm k)) ∩
      segment ℝ x (p (finRotate (n + 2) k)) = {x}) :
    IsSimplePolygonalArc (polygonReplaceVertex p k x) := by
  obtain ⟨i, j, hik, hjk, hip, hjs, hij⟩ :=
    exists_arc_incident_edge_indices k had.1 had.2.1
  let q := polygonReplaceVertex p k x
  have hpk : (finRotate (n + 2)).symm k ≠ k := by
    rw [← hip, ← hik]
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hsk : finRotate (n + 2) k ≠ k := by
    rw [← hjs, ← hjk]
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hqk : q k = x := polygonReplaceVertex_apply_same p k x
  have hqother (l : Fin (n + 2)) (hl : l ≠ k) : q l = p l :=
    polygonReplaceVertex_apply_of_ne p k x hl
  have hqpred : q ((finRotate (n + 2)).symm k) = p ((finRotate (n + 2)).symm k) :=
    hqother _ hpk
  have hqsucc : q (finRotate (n + 2) k) = p (finRotate (n + 2) k) := hqother _ hsk
  have hunchanged (l : Fin (n + 1)) (hli : l ≠ i) (hlj : l ≠ j) :
      l.castSucc ≠ k ∧ l.succ ≠ k := by
    constructor
    · intro h
      have hv := congrArg Fin.val (h.trans hjk.symm)
      exact hlj (Fin.ext hv)
    · intro h
      apply hli
      apply Fin.ext
      have hv := congrArg Fin.val (h.trans hik.symm)
      simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using hv
  have hqedge (l : Fin (n + 1)) (hli : l ≠ i) (hlj : l ≠ j) :
      q.edgeSet ℝ l.castSucc = p.edgeSet ℝ l.castSucc := by
    rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment,
      hqother _ (hunchanged l hli hlj).1, hqother _ (hunchanged l hli hlj).2]
  have hqedgei : q.edgeSet ℝ i.castSucc =
      segment ℝ x (p ((finRotate (n + 2)).symm k)) := by
    rw [polygon_arcEdge_eq_segment, hip, hik, hqpred, hqk, segment_symm]
  have hqedgej : q.edgeSet ℝ j.castSucc =
      segment ℝ x (p (finRotate (n + 2) k)) := by
    rw [polygon_arcEdge_eq_segment, hjk, hjs, hqk, hqsucc]
  have haT : p ((finRotate (n + 2)).symm k) ∈ polygonVertexTriangle p k :=
    subset_convexHull ℝ _ (by simp)
  have hbT : p (finRotate (n + 2) k) ∈ polygonVertexTriangle p k :=
    subset_convexHull ℝ _ (by simp)
  have hA : segment ℝ x (p ((finRotate (n + 2)).symm k)) ⊆ polygonVertexTriangle p k :=
    (convex_convexHull ℝ _).segment_subset hxT haT
  have hB : segment ℝ x (p (finRotate (n + 2) k)) ⊆ polygonVertexTriangle p k :=
    (convex_convexHull ℝ _).segment_subset hxT hbT
  have hxne (l : Fin (n + 2)) (hl : l ≠ k) : x ≠ p l := by
    intro h
    have hh := (hp.vertex_mem_triangle_iff_of_admissible k had l).mp (h ▸ hxT)
    rcases hh with hh | hh | hh
    · exact hl hh
    · exact hxa (h.trans (congrArg p hh))
    · exact hxb (h.trans (congrArg p hh))
  have hincident (l m : Fin (n + 1)) (hl : l = i ∨ l = j)
      (hmi : m ≠ i) (hmj : m ≠ j) :
      q.edgeSet ℝ l.castSucc ∩ q.edgeSet ℝ m.castSucc ⊆
        {q l.castSucc, q l.succ} ∩ {q m.castSucc, q m.succ} := by
    rcases hl with rfl | rfl
    · rintro z ⟨hzA, hzm⟩
      rw [hqedgei] at hzA
      rw [hqedge m hmi hmj] at hzm
      have hends := hp.triangle_inter_edge_subset_of_admissible k had m
        (hunchanged m hmi hmj).1 (hunchanged m hmi hmj).2 ⟨hA hzA, hzm⟩
      have hznb : z ≠ p (finRotate (n + 2) k) := by
        intro h
        have hbA : p (finRotate (n + 2) k) ∈
            segment ℝ x (p ((finRotate (n + 2)).symm k)) := h ▸ hzA
        have hbx : p (finRotate (n + 2) k) ∈ ({x} : Set E) :=
          hinter ▸ ⟨hbA, right_mem_segment ℝ _ _⟩
        exact hxb (mem_singleton_iff.mp hbx).symm
      refine ⟨Or.inl ?_, ?_⟩
      · rw [hip, hqpred]
        exact hends.1.resolve_right hznb
      · simpa only [hqother _ (hunchanged m hmi hmj).1,
          hqother _ (hunchanged m hmi hmj).2] using hends.2
    · rintro z ⟨hzB, hzm⟩
      rw [hqedgej] at hzB
      rw [hqedge m hmi hmj] at hzm
      have hends := hp.triangle_inter_edge_subset_of_admissible k had m
        (hunchanged m hmi hmj).1 (hunchanged m hmi hmj).2 ⟨hB hzB, hzm⟩
      have hzna : z ≠ p ((finRotate (n + 2)).symm k) := by
        intro h
        have haB : p ((finRotate (n + 2)).symm k) ∈
            segment ℝ x (p (finRotate (n + 2) k)) := h ▸ hzB
        have hax : p ((finRotate (n + 2)).symm k) ∈ ({x} : Set E) :=
          hinter ▸ ⟨right_mem_segment ℝ _ _, haB⟩
        exact hxa (mem_singleton_iff.mp hax).symm
      refine ⟨Or.inr ?_, ?_⟩
      · rw [hjs, hqsucc]
        exact hends.1.resolve_left hzna
      · simpa only [hqother _ (hunchanged m hmi hmj).1,
          hqother _ (hunchanged m hmi hmj).2] using hends.2
  refine ⟨?_, ?_⟩
  · intro l m hlm
    by_cases hlk : l = k
    · subst l
      by_cases hmk : m = k
      · exact hmk.symm
      · exact (hxne m hmk (hqk.symm.trans (hlm.trans (hqother m hmk)))).elim
    · by_cases hmk : m = k
      · subst m
        exact (hxne l hlk (hqk.symm.trans (hlm.symm.trans (hqother l hlk)))).elim
      · exact hp.vertices_injective ((hqother l hlk).symm.trans (hlm.trans (hqother m hmk)))
  · intro l m hlm z hz
    change z ∈ {q l.castSucc, q l.succ} ∩ {q m.castSucc, q m.succ}
    change z ∈ q.edgeSet ℝ l.castSucc ∩ q.edgeSet ℝ m.castSucc at hz
    by_cases hl : l = i ∨ l = j
    · by_cases hm : m = i ∨ m = j
      · rcases hl with hl | hl <;> rcases hm with hm | hm
        · exact (hlm (hl.trans hm.symm)).elim
        · subst l
          subst m
          have hzx : z ∈ ({x} : Set E) :=
            hinter ▸ (by simpa only [hqedgei, hqedgej] using hz)
          change z = x at hzx
          simp only [hip, hik, hjk, hjs, hqpred, hqk, hqsucc]
          exact ⟨Or.inr hzx, Or.inl hzx⟩
        · subst l
          subst m
          have hswap : z ∈ q.edgeSet ℝ i.castSucc ∩ q.edgeSet ℝ j.castSucc :=
            ⟨hz.2, hz.1⟩
          rw [hqedgei, hqedgej] at hswap
          have hzx : z ∈ ({x} : Set E) := hinter ▸ hswap
          change z = x at hzx
          simp only [hip, hik, hjk, hjs, hqpred, hqk, hqsucc]
          exact ⟨Or.inl hzx, Or.inr hzx⟩
        · exact (hlm (hl.trans hm.symm)).elim
      · exact hincident l m hl (not_or.mp hm).1 (not_or.mp hm).2 hz
    · by_cases hm : m = i ∨ m = j
      · have hh := hincident m l hm (not_or.mp hl).1 (not_or.mp hl).2 ⟨hz.2, hz.1⟩
        exact ⟨hh.2, hh.1⟩
      · have hl' := not_or.mp hl
        have hm' := not_or.mp hm
        rw [hqedge l hl'.1 hl'.2, hqedge m hm'.1 hm'.2] at hz
        simpa only [hqother _ (hunchanged l hl'.1 hl'.2).1,
          hqother _ (hunchanged l hl'.1 hl'.2).2,
          hqother _ (hunchanged m hm'.1 hm'.2).1,
          hqother _ (hunchanged m hm'.1 hm'.2).2] using hp.edges_inter l m hlm hz

theorem IsSimplePolygonalArc.isSimple_polygonPushVertex {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2)) (had : IsAdmissibleArcVertex p k)
    {t : ℝ} (ht : t ∈ Icc 0 1) : IsSimplePolygonalArc (polygonPushVertex p k t) := by
  obtain ⟨i, j, hik, hjk, hip, hjs, hij⟩ :=
    exists_arc_incident_edge_indices k had.1 had.2.1
  have ha : p ((finRotate (n + 2)).symm k) ≠ p k := by
    rw [← hip, ← hik]
    exact hp.edge_endpoints_ne i
  have hb : p (finRotate (n + 2) k) ≠ p k := by
    rw [← hjs, ← hjk]
    exact (hp.edge_endpoints_ne j).symm
  have hneighbors : (finRotate (n + 2)).symm k ≠ finRotate (n + 2) k := by
    intro h
    have hv := congrArg Fin.val (hip.trans (h.trans hjs.symm))
    have hvk := congrArg Fin.val (hik.trans hjk.symm)
    simp only [Fin.val_castSucc, Fin.val_succ] at hv hvk
    omega
  have hinter : segment ℝ (p k) (p ((finRotate (n + 2)).symm k)) ∩
      segment ℝ (p k) (p (finRotate (n + 2) k)) ⊆ {p k} := by
    rintro z ⟨hzp, hzs⟩
    have hzp' : z ∈ p.edgeSet ℝ i.castSucc := by
      rw [polygon_arcEdge_eq_segment, hip, hik, segment_symm]
      exact hzp
    have hzs' : z ∈ p.edgeSet ℝ j.castSucc := by
      rw [polygon_arcEdge_eq_segment, hjk, hjs]
      exact hzs
    have hh := hp.edges_inter i j hij ⟨hzp', hzs'⟩
    rw [hip, hik, hjk, hjs] at hh
    rcases hh.1 with hzp | hzk
    · rcases hh.2 with hzk | hzs
      · exact hzk
      · exact (hneighbors (hp.vertices_injective (hzp.symm.trans hzs))).elim
    · exact hzk
  have hcorner := cornerPushPoint_simple_corner ha hb hinter ht
  exact hp.isSimple_polygonReplaceVertex_of_admissible k had _
    (cornerPushPoint_mem_triangle _ _ _ ht) hcorner.1 hcorner.2.1 hcorner.2.2

theorem polygonPushVertex_arc_endpoints (p : Polygon E (n + 2)) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (t : ℝ) :
    polygonPushVertex p k t 0 = p 0 ∧
      polygonPushVertex p k t (Fin.last (n + 1)) = p (Fin.last (n + 1)) := by
  exact ⟨polygonReplaceVertex_apply_of_ne _ _ _ hk0.symm,
    polygonReplaceVertex_apply_of_ne _ _ _ hkl.symm⟩

theorem polygonPushVertex_arcBoundary_sdiff_triangle (p : Polygon E (n + 2))
    (k : Fin (n + 2)) {t : ℝ} (ht : t ∈ Icc 0 1) :
    polygonArcBoundary (polygonPushVertex p k t) \ polygonVertexTriangle p k =
      polygonArcBoundary p \ polygonVertexTriangle p k := by
  let T := polygonVertexTriangle p k
  let v := cornerPushPoint (p k) (p ((finRotate (n + 2)).symm k))
    (p (finRotate (n + 2) k)) t
  let q := polygonReplaceVertex p k v
  have hconv : Convex ℝ T := convex_convexHull ℝ _
  have hk : p k ∈ T := subset_convexHull ℝ _ (by simp)
  have hp : p ((finRotate (n + 2)).symm k) ∈ T := subset_convexHull ℝ _ (by simp)
  have hs : p (finRotate (n + 2) k) ∈ T := subset_convexHull ℝ _ (by simp)
  have hv : v ∈ T := cornerPushPoint_mem_triangle _ _ _ ht
  have hqother (j : Fin (n + 2)) (hj : j ≠ k) : q j = p j :=
    polygonReplaceVertex_apply_of_ne p k v hj
  have hqmem (j : Fin (n + 2)) (hj : p j ∈ T) : q j ∈ T := by
    by_cases hjk : j = k
    · subst j
      rw [show q k = v from polygonReplaceVertex_apply_same p k v]
      exact hv
    · rw [hqother j hjk]
      exact hj
  have hends (i : Fin (n + 1)) (hi : i.castSucc = k ∨ i.succ = k) :
      p i.castSucc ∈ T ∧ p i.succ ∈ T := by
    have hr : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rcases hi with hi | hi
    · have hi' : i.succ = finRotate (n + 2) k := by rw [← hi, hr]
      rw [hi, hi']
      exact ⟨hk, hs⟩
    · have hi' : i.castSucc = (finRotate (n + 2)).symm k :=
        (finRotate (n + 2)).injective (by rw [hr, hi, Equiv.apply_symm_apply])
      rw [hi, hi']
      exact ⟨hp, hk⟩
  have hpedge (i : Fin (n + 1)) (hi : i.castSucc = k ∨ i.succ = k) :
      p.edgeSet ℝ i.castSucc ⊆ T := by
    rw [polygon_arcEdge_eq_segment]
    exact hconv.segment_subset (hends i hi).1 (hends i hi).2
  have hqedge (i : Fin (n + 1)) (hi : i.castSucc = k ∨ i.succ = k) :
      q.edgeSet ℝ i.castSucc ⊆ T := by
    rw [polygon_arcEdge_eq_segment]
    exact hconv.segment_subset (hqmem _ (hends i hi).1) (hqmem _ (hends i hi).2)
  have heq (i : Fin (n + 1)) (hi : ¬ (i.castSucc = k ∨ i.succ = k)) :
      q.edgeSet ℝ i.castSucc = p.edgeSet ℝ i.castSucc := by
    rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment,
      hqother _ (not_or.mp hi).1, hqother _ (not_or.mp hi).2]
  change polygonArcBoundary q \ T = polygonArcBoundary p \ T
  ext z
  constructor
  · rintro ⟨hz, hzT⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    by_cases hik : i.castSucc = k ∨ i.succ = k
    · exact (hzT (hqedge i hik hi)).elim
    · rw [heq i hik] at hi
      exact ⟨mem_iUnion.mpr ⟨i, hi⟩, hzT⟩
  · rintro ⟨hz, hzT⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    by_cases hik : i.castSucc = k ∨ i.succ = k
    · exact (hzT (hpedge i hik hi)).elim
    · rw [← heq i hik] at hi
      exact ⟨mem_iUnion.mpr ⟨i, hi⟩, hzT⟩

end PoincareConjecture.M25.Topology3D
