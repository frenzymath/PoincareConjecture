import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SegmentSubdivision
import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {n : ℕ}

def polygonArcDeleteVertex {E : Type*} (p : Polygon E (n + 3)) (k : Fin (n + 3)) :
    Polygon E (n + 2) := ⟨fun j => p (k.succAbove j)⟩

theorem polygonArcDeleteVertex_endpoints {E : Type*} (p : Polygon E (n + 3))
    (k : Fin (n + 3)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 2)) :
    polygonArcDeleteVertex p k 0 = p 0 ∧
      polygonArcDeleteVertex p k (Fin.last (n + 1)) = p (Fin.last (n + 2)) := by
  change p (k.succAbove 0) = p 0 ∧
    p (k.succAbove (Fin.last (n + 1))) = p (Fin.last (n + 2))
  rw [Fin.succAbove_ne_zero_zero hk0, Fin.succAbove_ne_last_last hkl]
  exact ⟨rfl, rfl⟩

private theorem arcDeleteIndex_val (k : Fin (n + 3)) (j : Fin (n + 2)) :
    (k.succAbove j).val = if j.val < k.val then j.val else j.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

private theorem arcDelete_center_indices (k : Fin (n + 3))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 2)) :
    ∃ r : Fin (n + 1), r.val + 1 = k.val ∧
      k.succAbove r.castSucc = (finRotate (n + 3)).symm k ∧
      k.succAbove r.succ = finRotate (n + 3) k := by
  have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk0
  have hklt : k.val < n + 2 := Fin.lt_last_iff_ne_last.mpr hkl
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have ha := congrArg Fin.val hak
  have hb := congrArg Fin.val hbk
  simp only [Fin.val_succ, Fin.val_castSucc] at ha hb
  let r : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  have hr : r.val + 1 = k.val := by dsimp [r]; omega
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hap]
    apply Fin.ext
    simp only [arcDeleteIndex_val, Fin.val_castSucc]
    split_ifs <;> omega
  · rw [← hbs]
    apply Fin.ext
    simp only [arcDeleteIndex_val, Fin.val_succ]
    split_ifs <;> omega

private theorem arcDelete_noncentral_indices (k : Fin (n + 3)) (i : Fin (n + 1))
    (hi : i.val + 1 ≠ k.val) :
    ∃ j : Fin (n + 2), k.succAbove i.castSucc = j.castSucc ∧
      k.succAbove i.succ = j.succ := by
  by_cases h : i.val + 1 < k.val
  · let j : Fin (n + 2) := ⟨i.val, by omega⟩
    refine ⟨j, ?_, ?_⟩ <;> apply Fin.ext
    · simp only [arcDeleteIndex_val, Fin.val_castSucc]
      change (if i.val < k.val then i.val else i.val + 1) = i.val
      rw [if_pos (by omega)]
    · simp only [arcDeleteIndex_val, Fin.val_succ]
      change (if i.val + 1 < k.val then i.val + 1 else i.val + 1 + 1) = i.val + 1
      rw [if_pos h]
  · let j : Fin (n + 2) := ⟨i.val + 1, by omega⟩
    refine ⟨j, ?_, ?_⟩ <;> apply Fin.ext
    · simp only [arcDeleteIndex_val, Fin.val_castSucc]
      change (if i.val < k.val then i.val else i.val + 1) = i.val + 1
      rw [if_neg (by omega)]
    · simp only [arcDeleteIndex_val, Fin.val_succ]
      change (if i.val + 1 < k.val then i.val + 1 else i.val + 1 + 1) = i.val + 1 + 1
      rw [if_neg h]

private theorem arcDelete_retained_indices (k : Fin (n + 3))
    (hkl : k ≠ Fin.last (n + 2)) (j : Fin (n + 2))
    (hjk : j.castSucc ≠ k) (hjs : j.succ ≠ k) :
    ∃ i : Fin (n + 1), k.succAbove i.castSucc = j.castSucc ∧
      k.succAbove i.succ = j.succ := by
  have hklt : k.val < n + 2 := Fin.lt_last_iff_ne_last.mpr hkl
  have hj0 : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hj1 : j.val + 1 ≠ k.val := fun h => hjs (Fin.ext h)
  by_cases h : j.val < k.val
  · let i : Fin (n + 1) := ⟨j.val, by omega⟩
    refine ⟨i, ?_, ?_⟩ <;> apply Fin.ext
    · simp only [arcDeleteIndex_val, Fin.val_castSucc]
      change (if j.val < k.val then j.val else j.val + 1) = j.val
      rw [if_pos h]
    · simp only [arcDeleteIndex_val, Fin.val_succ]
      change (if j.val + 1 < k.val then j.val + 1 else j.val + 1 + 1) = j.val + 1
      rw [if_pos (by omega)]
  · have hpos : 0 < j.val := by omega
    let i : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    refine ⟨i, ?_, ?_⟩ <;> apply Fin.ext
    · simp only [arcDeleteIndex_val, Fin.val_castSucc]
      change (if j.val - 1 < k.val then j.val - 1 else j.val - 1 + 1) = j.val
      rw [if_neg (by omega)]
      omega
    · simp only [arcDeleteIndex_val, Fin.val_succ]
      change (if j.val - 1 + 1 < k.val then j.val - 1 + 1 else
        j.val - 1 + 1 + 1) = j.val + 1
      rw [if_neg (by omega)]
      omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isAdmissibleArcVertex_of_mem_segment (p : Polygon E (n + 2))
    (k : Fin (n + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1))
    (hstraight : p k ∈ segment ℝ (p ((finRotate (n + 2)).symm k))
      (p (finRotate (n + 2) k))) : IsAdmissibleArcVertex p k := by
  refine ⟨hk0, hkl, subset_antisymm ?_
    (polygonArcIncidentEdges_subset_triangle_inter_boundary p k hk0 hkl)⟩
  have hT : polygonVertexTriangle p k ⊆
      segment ℝ (p ((finRotate (n + 2)).symm k)) (p (finRotate (n + 2) k)) := by
    apply convexHull_min _ (convex_segment (𝕜 := ℝ) _ _)
    rintro z (hz | hz | hz)
    · exact hz.symm ▸ hstraight
    · exact hz.symm ▸ left_mem_segment ℝ _ _
    · exact hz.symm ▸ right_mem_segment ℝ _ _
  rintro z ⟨hz, _⟩
  exact (segment_split_at_point hstraight).1.symm ▸ hT hz

theorem polygonArcDeleteVertex_boundary (p : Polygon E (n + 3)) (k : Fin (n + 3))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 2))
    (hstraight : p k ∈ segment ℝ (p ((finRotate (n + 3)).symm k))
      (p (finRotate (n + 3) k))) :
    polygonArcBoundary (polygonArcDeleteVertex p k) = polygonArcBoundary p := by
  obtain ⟨r, hr, hrp, hrs⟩ := arcDelete_center_indices k hk0 hkl
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hmerged : (polygonArcDeleteVertex p k).edgeSet ℝ r.castSucc =
      p.edgeSet ℝ a.castSucc ∪ p.edgeSet ℝ b.castSucc := by
    rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment]
    change segment ℝ (p (k.succAbove r.castSucc)) (p (k.succAbove r.succ)) = _
    rw [hrp, hrs, hap, hak, hbk, hbs,
      segment_symm ℝ (p ((finRotate (n + 3)).symm k)) (p k)]
    exact (segment_split_at_point hstraight).1.symm
  have heq (i : Fin (n + 1)) (j : Fin (n + 2))
      (h0 : k.succAbove i.castSucc = j.castSucc) (h1 : k.succAbove i.succ = j.succ) :
      (polygonArcDeleteVertex p k).edgeSet ℝ i.castSucc = p.edgeSet ℝ j.castSucc := by
    rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment]
    change segment ℝ (p (k.succAbove i.castSucc)) (p (k.succAbove i.succ)) = _
    rw [h0, h1]
  apply subset_antisymm
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    by_cases hir : i = r
    · rw [hir, hmerged] at hi
      exact hi.elim (fun h => polygon_arcEdge_subset_boundary p a h)
        (fun h => polygon_arcEdge_subset_boundary p b h)
    · have hi' : i.val + 1 ≠ k.val := fun h => hir (Fin.ext (by omega))
      obtain ⟨j, hj0, hj1⟩ := arcDelete_noncentral_indices k i hi'
      exact polygon_arcEdge_subset_boundary p j (heq i j hj0 hj1 ▸ hi)
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    by_cases hja : j = a
    · apply polygon_arcEdge_subset_boundary (polygonArcDeleteVertex p k) r
      rw [hmerged]
      exact Or.inl (hja ▸ hj)
    · by_cases hjb : j = b
      · apply polygon_arcEdge_subset_boundary (polygonArcDeleteVertex p k) r
        rw [hmerged]
        exact Or.inr (hjb ▸ hj)
      · have hjk : j.castSucc ≠ k := by
          intro h
          exact hjb (Fin.castSucc_injective _ (h.trans hbk.symm))
        have hjs : j.succ ≠ k := by
          intro h
          exact hja (Fin.succ_injective _ (h.trans hak.symm))
        obtain ⟨i, hi0, hi1⟩ := arcDelete_retained_indices k hkl j hjk hjs
        exact polygon_arcEdge_subset_boundary (polygonArcDeleteVertex p k) i
          ((heq i j hi0 hi1).symm ▸ hj)

theorem IsSimplePolygonalArc.isSimple_polygonArcDeleteVertex {p : Polygon E (n + 3)}
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 3))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 2))
    (hstraight : p k ∈ segment ℝ (p ((finRotate (n + 3)).symm k))
      (p (finRotate (n + 3) k))) :
    IsSimplePolygonalArc (polygonArcDeleteVertex p k) := by
  obtain ⟨r, hr, hrp, hrs⟩ := arcDelete_center_indices k hk0 hkl
  have had := isAdmissibleArcVertex_of_mem_segment p k hk0 hkl hstraight
  have hDT : segment ℝ (p ((finRotate (n + 3)).symm k)) (p (finRotate (n + 3) k)) ⊆
      polygonVertexTriangle p k := segment_subset_convexHull (by simp) (by simp)
  have hparts (i : Fin (n + 1)) (hir : i ≠ r) :
      ∃ j : Fin (n + 2), k.succAbove i.castSucc = j.castSucc ∧
        k.succAbove i.succ = j.succ :=
    arcDelete_noncentral_indices k i (fun h => hir (Fin.ext (by omega)))
  have hclose (i : Fin (n + 1)) (hir : i ≠ r) :
      (polygonArcDeleteVertex p k).edgeSet ℝ r.castSucc ∩
        (polygonArcDeleteVertex p k).edgeSet ℝ i.castSucc ⊆
      {(polygonArcDeleteVertex p k) r.castSucc, (polygonArcDeleteVertex p k) r.succ} ∩
        {(polygonArcDeleteVertex p k) i.castSucc, (polygonArcDeleteVertex p k) i.succ} := by
    obtain ⟨j, hj0, hj1⟩ := hparts i hir
    rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment]
    change segment ℝ (p (k.succAbove r.castSucc)) (p (k.succAbove r.succ)) ∩
        segment ℝ (p (k.succAbove i.castSucc)) (p (k.succAbove i.succ)) ⊆
      {p (k.succAbove r.castSucc), p (k.succAbove r.succ)} ∩
        {p (k.succAbove i.castSucc), p (k.succAbove i.succ)}
    rw [hrp, hrs, hj0, hj1, ← polygon_arcEdge_eq_segment p j]
    have hjk : j.castSucc ≠ k := hj0 ▸ Fin.succAbove_ne k i.castSucc
    have hjs : j.succ ≠ k := hj1 ▸ Fin.succAbove_ne k i.succ
    intro z hz
    exact hp.triangle_inter_edge_subset_of_admissible k had j hjk hjs ⟨hDT hz.1, hz.2⟩
  refine ⟨hp.vertices_injective.comp Fin.succAbove_right_injective, ?_⟩
  intro i j hij
  by_cases hir : i = r
  · subst i
    exact hclose j hij.symm
  · by_cases hjr : j = r
    · subst j
      intro z hz
      have hh := hclose i hir ⟨hz.2, hz.1⟩
      exact ⟨hh.2, hh.1⟩
    · obtain ⟨a, ha0, ha1⟩ := hparts i hir
      obtain ⟨b, hb0, hb1⟩ := hparts j hjr
      have hab : a ≠ b := by
        intro heq
        apply hij
        apply Fin.castSucc_injective (n + 1)
        apply Fin.succAbove_right_injective (p := k)
        rw [ha0, hb0, heq]
      rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment]
      change segment ℝ (p (k.succAbove i.castSucc)) (p (k.succAbove i.succ)) ∩
          segment ℝ (p (k.succAbove j.castSucc)) (p (k.succAbove j.succ)) ⊆
        {p (k.succAbove i.castSucc), p (k.succAbove i.succ)} ∩
          {p (k.succAbove j.castSucc), p (k.succAbove j.succ)}
      rw [ha0, ha1, hb0, hb1, ← polygon_arcEdge_eq_segment p a,
        ← polygon_arcEdge_eq_segment p b]
      exact hp.edges_inter a b hab

end PoincareConjecture.M25.Topology3D
