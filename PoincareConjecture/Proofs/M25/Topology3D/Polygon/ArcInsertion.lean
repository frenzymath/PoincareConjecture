import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcDeletion
import Mathlib.Data.Fin.Tuple.Basic









set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}



noncomputable def polygonArcInsertVertex (q : Polygon E (n + 2)) (i : Fin (n + 1))
    (t : ℝ) : Polygon E (n + 3) :=
  ⟨Fin.insertNth i.castSucc.succ (AffineMap.lineMap (q i.castSucc) (q i.succ) t) q.vertices⟩

private theorem arcInsert_internal (i : Fin (n + 1)) :
    i.castSucc.succ ≠ (0 : Fin (n + 3)) ∧
      i.castSucc.succ ≠ Fin.last (n + 2) := by
  constructor <;> intro h
  · have hh := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hh
    omega
  · have hh := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
    omega



theorem polygonArcInsertVertex_spec (q : Polygon E (n + 2)) (i : Fin (n + 1)) (t : ℝ) :
    let k := i.castSucc.succ
    let p := polygonArcInsertVertex q i t
    p k = AffineMap.lineMap (q i.castSucc) (q i.succ) t ∧
      (∀ j : Fin (n + 2), p (k.succAbove j) = q j) ∧ p 0 = q 0 ∧
      p (Fin.last (n + 2)) = q (Fin.last (n + 1)) ∧ polygonArcDeleteVertex p k = q := by
  dsimp only
  have hsame : polygonArcInsertVertex q i t i.castSucc.succ =
      AffineMap.lineMap (q i.castSucc) (q i.succ) t := by
    exact Fin.insertNth_apply_same (α := fun _ => E) i.castSucc.succ _ q.vertices
  have hret (j : Fin (n + 2)) :
      polygonArcInsertVertex q i t (i.castSucc.succ.succAbove j) = q j :=
    Fin.insertNth_apply_succAbove (α := fun _ => E) i.castSucc.succ _ q.vertices j
  refine ⟨hsame, hret, ?_, ?_, ?_⟩
  · simpa only [Fin.succAbove_ne_zero_zero (arcInsert_internal i).1] using hret 0
  · simpa only [Fin.succAbove_ne_last_last (arcInsert_internal i).2] using
      hret (Fin.last (n + 1))
  · exact congrArg Polygon.mk (funext hret)



theorem polygonArcInsertVertex_delete_eq (p : Polygon E (n + 3))
    (i : Fin (n + 1)) (t : ℝ)
    (ht : p i.castSucc.succ =
      AffineMap.lineMap (p (i.castSucc.succ.succAbove i.castSucc))
        (p (i.castSucc.succ.succAbove i.succ)) t) :
    polygonArcInsertVertex (polygonArcDeleteVertex p i.castSucc.succ) i t = p := by
  exact congrArg Polygon.mk (Fin.insertNth_eq_iff.mpr ⟨ht.symm, rfl⟩)

private theorem arcInsert_succAbove_val (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (i.castSucc.succ.succAbove j).val =
      if j.val < i.val + 1 then j.val else j.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> rfl

private theorem arcInsert_center_indices (i : Fin (n + 1)) :
    i.castSucc.succ.succAbove i.castSucc = i.castSucc.castSucc ∧
      i.castSucc.succ.succAbove i.succ = i.succ.succ ∧
      i.succ.castSucc = i.castSucc.succ ∧
      i.castSucc.succ.succAbove i.castSucc = (finRotate (n + 3)).symm i.castSucc.succ ∧
      i.castSucc.succ.succAbove i.succ = finRotate (n + 3) i.castSucc.succ := by
  have hleft : i.castSucc.succ.succAbove i.castSucc = i.castSucc.castSucc := by
    apply Fin.ext
    simp only [arcInsert_succAbove_val, Fin.val_castSucc, Nat.lt_add_one, if_pos]
  have hright : i.castSucc.succ.succAbove i.succ = i.succ.succ := by
    apply Fin.ext
    simp only [arcInsert_succAbove_val, Fin.val_succ, lt_self_iff_false, if_false]
  have hmid : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  refine ⟨hleft, hright, hmid, ?_, ?_⟩
  · rw [hleft]
    apply (finRotate (n + 3)).injective
    rw [Equiv.apply_symm_apply]
    exact finRotate_of_lt i.castSucc.isLt
  · rw [hright, ← hmid]
    exact (finRotate_of_lt i.succ.isLt).symm



theorem polygonArcInsertVertex_boundary (q : Polygon E (n + 2)) (i : Fin (n + 1))
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    polygonArcBoundary (polygonArcInsertVertex q i t) = polygonArcBoundary q := by
  obtain ⟨hsame, hret, _, _, hdel⟩ := polygonArcInsertVertex_spec q i t
  obtain ⟨_, _, _, hpred, hsucc⟩ := arcInsert_center_indices i
  have hstraight : polygonArcInsertVertex q i t i.castSucc.succ ∈
      segment ℝ (polygonArcInsertVertex q i t ((finRotate (n + 3)).symm i.castSucc.succ))
        (polygonArcInsertVertex q i t (finRotate (n + 3) i.castSucc.succ)) := by
    rw [hsame, ← hpred, ← hsucc, hret, hret]
    exact lineMap_mem_segment ℝ _ _ ht
  have hh := polygonArcDeleteVertex_boundary (polygonArcInsertVertex q i t)
    i.castSucc.succ (arcInsert_internal i).1 (arcInsert_internal i).2 hstraight
  rw [hdel] at hh
  exact hh.symm

private theorem arcInsert_other_edge (i : Fin (n + 1)) (a : Fin (n + 2))
    (ha0 : a ≠ i.castSucc) (ha1 : a ≠ i.succ) :
    ∃ j : Fin (n + 1), j ≠ i ∧
      i.castSucc.succ.succAbove j.castSucc = a.castSucc ∧
      i.castSucc.succ.succAbove j.succ = a.succ := by
  have hne0 : a.val ≠ i.val := fun h => ha0 (Fin.ext h)
  have hne1 : a.val ≠ i.val + 1 := fun h => ha1 (Fin.ext h)
  by_cases ha : a.val < i.val
  · let j : Fin (n + 1) := ⟨a.val, by omega⟩
    refine ⟨j, fun h => hne0 (congrArg Fin.val h), ?_, ?_⟩
    · apply Fin.ext
      simp only [arcInsert_succAbove_val, Fin.val_castSucc]
      change (if a.val < i.val + 1 then a.val else a.val + 1) = a.val
      rw [if_pos (by omega)]
    · apply Fin.ext
      simp only [arcInsert_succAbove_val, Fin.val_succ]
      change (if a.val + 1 < i.val + 1 then a.val + 1 else a.val + 1 + 1) = a.val + 1
      rw [if_pos (by omega)]
  · let j : Fin (n + 1) := ⟨a.val - 1, by omega⟩
    refine ⟨j, ?_, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      change a.val - 1 = i.val at hv
      omega
    · apply Fin.ext
      simp only [arcInsert_succAbove_val, Fin.val_castSucc]
      change (if a.val - 1 < i.val + 1 then a.val - 1 else a.val - 1 + 1) = a.val
      rw [if_neg (by omega)]
      omega
    · apply Fin.ext
      simp only [arcInsert_succAbove_val, Fin.val_succ]
      change (if a.val - 1 + 1 < i.val + 1 then a.val - 1 + 1 else
        a.val - 1 + 1 + 1) = a.val + 1
      rw [if_neg (by omega)]
      omega



theorem IsSimplePolygonalArc.isSimple_polygonArcInsertVertex {q : Polygon E (n + 2)}
    (hq : IsSimplePolygonalArc q) (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    IsSimplePolygonalArc (polygonArcInsertVertex q i t) := by
  let p := polygonArcInsertVertex q i t
  let a := q i.castSucc
  let b := q i.succ
  let x := AffineMap.lineMap a b t
  obtain ⟨hsame, hret, _, _, _⟩ := polygonArcInsertVertex_spec q i t
  obtain ⟨hidx0, hidx1, hidxmid, _, _⟩ := arcInsert_center_indices i
  have hab : a ≠ b := hq.edge_endpoints_ne i
  have hx : x ∈ openSegment ℝ a b := lineMap_mem_openSegment ℝ _ _ ht
  have hxseg : x ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hx
  have hxa : x ≠ a := fun h => hab (left_mem_openSegment_iff.mp (h ▸ hx))
  have hxb : x ≠ b := fun h => hab (right_mem_openSegment_iff.mp (h ▸ hx))
  have hxq (j : Fin (n + 2)) : x ≠ q j := by
    intro hh
    have he : q j ∈ q.edgeSet ℝ i.castSucc := by
      rw [polygon_arcEdge_eq_segment, ← hh]
      exact hxseg
    rcases (hq.vertex_mem_edgeSet_iff j i).mp he with hj | hj
    · exact hxa (hh.trans (congrArg q.vertices hj))
    · exact hxb (hh.trans (congrArg q.vertices hj))
  have hpinj : Function.Injective p := by
    intro j l hh
    rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ j with rfl | ⟨j, rfl⟩
    · rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ l with rfl | ⟨l, rfl⟩
      · rfl
      · exact (hxq l (by simpa only [p, hsame, hret] using hh)).elim
    · rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ l with rfl | ⟨l, rfl⟩
      · exact (hxq j (by simpa only [p, hsame, hret] using hh.symm)).elim
      · apply congrArg i.castSucc.succ.succAbove
        apply hq.vertices_injective
        simpa only [p, hret] using hh
  have hpa : p i.castSucc.castSucc = a := by rw [← hidx0]; exact hret i.castSucc
  have hpb : p i.succ.succ = b := by rw [← hidx1]; exact hret i.succ
  have hpk : p i.castSucc.succ = x := hsame
  have hpl : p.edgeSet ℝ i.castSucc.castSucc = segment ℝ a x := by
    rw [polygon_arcEdge_eq_segment, hpa, hpk]
  have hpr : p.edgeSet ℝ i.succ.castSucc = segment ℝ x b := by
    rw [polygon_arcEdge_eq_segment, hidxmid, hpk, hpb]
  have hparts (j : Fin (n + 2)) (hj0 : j ≠ i.castSucc) (hj1 : j ≠ i.succ) :
      ∃ l : Fin (n + 1), l ≠ i ∧ p j.castSucc = q l.castSucc ∧ p j.succ = q l.succ := by
    obtain ⟨l, hli, hl0, hl1⟩ := arcInsert_other_edge i j hj0 hj1
    refine ⟨l, hli, ?_, ?_⟩
    · rw [← hl0]; exact hret l.castSucc
    · rw [← hl1]; exact hret l.succ
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b
  have hL0 : L 0 = a := AffineMap.lineMap_apply_zero _ _
  have hL1 : L 1 = b := AffineMap.lineMap_apply_one _ _
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ hab
  have hleft : segment ℝ a x = L '' Icc 0 t := by
    rw [← segment_eq_Icc ht.1.le, image_segment, hL0]
  have hright : segment ℝ x b = L '' Icc t 1 := by
    rw [← segment_eq_Icc ht.2.le, image_segment, hL1]
  have hbn : b ∉ segment ℝ a x := by
    rw [hleft]
    rintro ⟨s, hs, heq⟩
    have hs1 := hLinj (heq.trans hL1.symm)
    exact (not_le_of_gt ht.2) (hs1 ▸ hs.2)
  have han : a ∉ segment ℝ x b := by
    rw [hright]
    rintro ⟨s, hs, heq⟩
    have hs0 := hLinj (heq.trans hL0.symm)
    exact (not_le_of_gt ht.1) (hs0 ▸ hs.1)
  have hleftsub : segment ℝ a x ⊆ segment ℝ a b :=
    (convex_segment (𝕜 := ℝ) a b).segment_subset (left_mem_segment ℝ a b) hxseg
  have hrightsub : segment ℝ x b ⊆ segment ℝ a b :=
    (convex_segment (𝕜 := ℝ) a b).segment_subset hxseg (right_mem_segment ℝ a b)
  have hleftother (j : Fin (n + 2)) (hj0 : j ≠ i.castSucc) (hj1 : j ≠ i.succ) :
      p.edgeSet ℝ i.castSucc.castSucc ∩ p.edgeSet ℝ j.castSucc ⊆
        {p i.castSucc.castSucc, p i.castSucc.succ} ∩ {p j.castSucc, p j.succ} := by
    obtain ⟨l, hli, hl0, hl1⟩ := hparts j hj0 hj1
    rw [hpl, polygon_arcEdge_eq_segment, hpa, hpk, hl0, hl1]
    rintro z ⟨hz, hzl⟩
    have hh := hq.edges_inter i l hli.symm
      ⟨(polygon_arcEdge_eq_segment q i).symm ▸ hleftsub hz,
        (polygon_arcEdge_eq_segment q l).symm ▸ hzl⟩
    have he : z = a ∨ z = b := hh.1
    have hza : z = a := he.resolve_right (fun heq => hbn (heq ▸ hz))
    exact ⟨Or.inl hza, hh.2⟩
  have hrightother (j : Fin (n + 2)) (hj0 : j ≠ i.castSucc) (hj1 : j ≠ i.succ) :
      p.edgeSet ℝ i.succ.castSucc ∩ p.edgeSet ℝ j.castSucc ⊆
        {p i.succ.castSucc, p i.succ.succ} ∩ {p j.castSucc, p j.succ} := by
    obtain ⟨l, hli, hl0, hl1⟩ := hparts j hj0 hj1
    rw [hpr, polygon_arcEdge_eq_segment, hidxmid, hpk, hpb, hl0, hl1]
    rintro z ⟨hz, hzl⟩
    have hh := hq.edges_inter i l hli.symm
      ⟨(polygon_arcEdge_eq_segment q i).symm ▸ hrightsub hz,
        (polygon_arcEdge_eq_segment q l).symm ▸ hzl⟩
    have he : z = a ∨ z = b := hh.1
    have hzb : z = b := he.resolve_left (fun heq => han (heq ▸ hz))
    exact ⟨Or.inr hzb, hh.2⟩
  have hsplit : p.edgeSet ℝ i.castSucc.castSucc ∩ p.edgeSet ℝ i.succ.castSucc ⊆
      {p i.castSucc.castSucc, p i.castSucc.succ} ∩ {p i.succ.castSucc, p i.succ.succ} := by
    rw [hpl, hpr, hpa, hpk, hidxmid, hpk, hpb, segment_symm ℝ a x]
    rw [(segment_split_at_point hxseg).2]
    intro z hz
    exact ⟨Or.inr hz, Or.inl hz⟩
  refine ⟨hpinj, ?_⟩
  intro j l hjl
  by_cases hj0 : j = i.castSucc
  · subst j
    by_cases hl1 : l = i.succ
    · subst l; exact hsplit
    · exact hleftother l hjl.symm hl1
  · by_cases hj1 : j = i.succ
    · subst j
      by_cases hl0 : l = i.castSucc
      · subst l
        intro z hz
        have hh := hsplit ⟨hz.2, hz.1⟩
        exact ⟨hh.2, hh.1⟩
      · exact hrightother l hl0 hjl.symm
    · by_cases hl0 : l = i.castSucc
      · subst l
        intro z hz
        have hh := hleftother j hj0 hj1 ⟨hz.2, hz.1⟩
        exact ⟨hh.2, hh.1⟩
      · by_cases hl1 : l = i.succ
        · subst l
          intro z hz
          have hh := hrightother j hj0 hj1 ⟨hz.2, hz.1⟩
          exact ⟨hh.2, hh.1⟩
        · obtain ⟨a', _, ha0, ha1⟩ := hparts j hj0 hj1
          obtain ⟨b', _, hb0, hb1⟩ := hparts l hl0 hl1
          have hab' : a' ≠ b' := by
            intro heq
            apply hjl
            apply Fin.castSucc_injective (n + 2)
            apply hpinj
            rw [ha0, hb0, heq]
          rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment, ha0, ha1, hb0, hb1,
            ← polygon_arcEdge_eq_segment q a', ← polygon_arcEdge_eq_segment q b']
          exact hq.edges_inter a' b' hab'



theorem contDiff_polygonArcInsertVertex_apply {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {s : ℕ∞ω}
    {q : W → Polygon E (n + 2)} {t : W → ℝ} (i : Fin (n + 1)) (j : Fin (n + 3))
    (hq : ∀ a, ContDiff ℝ s (fun z => q z a)) (ht : ContDiff ℝ s t) :
    ContDiff ℝ s (fun z => polygonArcInsertVertex (q z) i (t z) j) := by
  rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ j with rfl | ⟨a, rfl⟩
  · have heq (z : W) := (polygonArcInsertVertex_spec (q z) i (t z)).1
    simp_rw [heq, AffineMap.lineMap_apply_module]
    exact ((contDiff_const.sub ht).smul (hq i.castSucc)).add (ht.smul (hq i.succ))
  · have heq (z : W) := (polygonArcInsertVertex_spec (q z) i (t z)).2.1 a
    simp_rw [heq]
    exact hq a



theorem polygonArcInsertVertex_strict_bounds (q : Polygon E (n + 2))
    (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Ioo 0 1) (X : E →ₗ[ℝ] ℝ)
    (hLR : X (q 0) < X (q (Fin.last (n + 1))))
    (hX : ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
      X (q 0) < X (q j) ∧ X (q j) < X (q (Fin.last (n + 1)))) :
    ∀ h, h ≠ 0 → h ≠ Fin.last (n + 2) →
      X (polygonArcInsertVertex q i t 0) < X (polygonArcInsertVertex q i t h) ∧
      X (polygonArcInsertVertex q i t h) < X (polygonArcInsertVertex q i t (Fin.last (n + 2))) := by
  obtain ⟨hsame, hret, hzero, hlast, _⟩ := polygonArcInsertVertex_spec q i t
  have hial : i.castSucc ≠ Fin.last (n + 1) := Fin.castSucc_ne_last i
  have hib0 : i.succ ≠ 0 := Fin.succ_ne_zero i
  have ha : X (q 0) ≤ X (q i.castSucc) ∧ X (q i.castSucc) < X (q (Fin.last (n + 1))) := by
    by_cases h : i.castSucc = 0
    · rw [h]
      exact ⟨le_rfl, hLR⟩
    · exact ⟨(hX _ h hial).1.le, (hX _ h hial).2⟩
  have hb : X (q 0) < X (q i.succ) ∧ X (q i.succ) ≤ X (q (Fin.last (n + 1))) := by
    by_cases h : i.succ = Fin.last (n + 1)
    · rw [h]
      exact ⟨hLR, le_rfl⟩
    · exact ⟨(hX _ hib0 h).1, (hX _ hib0 h).2.le⟩
  intro h hh0 hhl
  rw [hzero, hlast]
  rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ h with rfl | ⟨a, rfl⟩
  · rw [hsame, AffineMap.lineMap_apply_module, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
    have ht' : 0 < 1 - t := sub_pos.mpr ht.2
    constructor
    · nlinarith [mul_nonneg ht'.le (sub_nonneg.mpr ha.1),
        mul_pos ht.1 (sub_pos.mpr hb.1)]
    · nlinarith [mul_pos ht' (sub_pos.mpr ha.2),
        mul_nonneg ht.1.le (sub_nonneg.mpr hb.2)]
  · rw [hret]
    apply hX
    · intro h
      apply hh0
      rw [h, Fin.succAbove_ne_zero_zero (arcInsert_internal i).1]
    · intro h
      apply hhl
      rw [h, Fin.succAbove_ne_last_last (arcInsert_internal i).2]

end PoincareConjecture.M25.Topology3D
