import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcInsertion
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SupportedRadialSlide
import PoincareConjecture.Proofs.M25.Topology3D.Plane.FamilyPersistence

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

private theorem arcLocal_center_indices {n : ℕ} (i : Fin (n + 1)) :
    i.castSucc.succ ≠ (0 : Fin (n + 3)) ∧
      i.castSucc.succ ≠ Fin.last (n + 2) ∧
      i.castSucc.succ.succAbove i.castSucc = i.castSucc.castSucc ∧
      i.castSucc.succ.succAbove i.succ = i.succ.succ ∧
      (finRotate (n + 3)).symm i.castSucc.succ = i.castSucc.castSucc ∧
      finRotate (n + 3) i.castSucc.succ = i.succ.succ := by
  have hk0 : i.castSucc.succ ≠ (0 : Fin (n + 3)) := Fin.succ_ne_zero _
  have hkl : i.castSucc.succ ≠ Fin.last (n + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  refine ⟨hk0, hkl, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    rw [if_pos (by omega)]
    rfl
  · apply Fin.ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    rw [if_neg (by omega)]
    rfl
  · apply (finRotate (n + 3)).injective
    rw [Equiv.apply_symm_apply]
    exact (show finRotate (n + 3) i.castSucc.castSucc = i.castSucc.succ from
      finRotate_of_lt i.castSucc.isLt).symm
  · have hmid : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    rw [hmid]
    exact finRotate_of_lt i.succ.isLt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem arcLocal_same_admissible {n : ℕ} {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (had : IsAdmissibleArcVertex p k) {t : ℝ} (ht : t ∈ Icc 0 1) :
    IsAdmissibleArcVertex (polygonPushVertex p k t) k := by
  obtain ⟨a, b, hak, hbk, hap, hbs, _⟩ :=
    exists_arc_incident_edge_indices k had.1 had.2.1
  have hpk : (finRotate (n + 2)).symm k ≠ k := by
    rw [← hap, ← hak]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hsk : finRotate (n + 2) k ≠ k := by
    rw [← hbs, ← hbk]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  let q := polygonPushVertex p k t
  have hqother (j : Fin (n + 2)) (hj : j ≠ k) : q j = p j :=
    polygonReplaceVertex_apply_of_ne _ _ _ hj
  have hqp := hqother _ hpk
  have hqs := hqother _ hsk
  have hT : polygonVertexTriangle q k ⊆ polygonVertexTriangle p k := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro x (hx | hx | hx)
    · rw [hx]
      change polygonPushVertex p k t k ∈ polygonVertexTriangle p k
      rw [polygonPushVertex, polygonReplaceVertex_apply_same]
      exact cornerPushPoint_mem_triangle (p k) (p ((finRotate (n + 2)).symm k))
        (p (finRotate (n + 2) k)) ht
    · rw [hx, hqp]
      exact subset_convexHull ℝ _ (by simp)
    · rw [hx, hqs]
      exact subset_convexHull ℝ _ (by simp)
  refine ⟨had.1, had.2.1, subset_antisymm ?_
    (polygonArcIncidentEdges_subset_triangle_inter_boundary q k had.1 had.2.1)⟩
  change polygonVertexTriangle q k ∩ polygonArcBoundary q ⊆
    segment ℝ (q k) (q ((finRotate (n + 2)).symm k)) ∪
      segment ℝ (q k) (q (finRotate (n + 2) k))
  rintro x ⟨hxT, hxB⟩
  obtain ⟨e, he⟩ := mem_iUnion.mp hxB
  have hrot : finRotate (n + 2) e.castSucc = e.succ := finRotate_of_lt e.isLt
  rw [polygon_arcEdge_eq_segment] at he
  by_cases he0 : e.castSucc = k
  · have he1 : e.succ = finRotate (n + 2) k := by
      rw [← he0, hrot]
    rw [he0, he1] at he
    exact Or.inr he
  · by_cases he1 : e.succ = k
    · have hepred : e.castSucc = (finRotate (n + 2)).symm k := by
        apply (finRotate (n + 2)).injective
        rw [hrot, Equiv.apply_symm_apply, he1]
      rw [hepred, he1, segment_symm] at he
      exact Or.inl he
    · have heold : x ∈ p.edgeSet ℝ e.castSucc := by
        rw [polygon_arcEdge_eq_segment]
        rwa [hqother _ he0, hqother _ he1] at he
      have hx := (hp.triangle_inter_edge_subset_of_admissible k had e he0 he1
        ⟨hT hxT, heold⟩).1
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx, hqp]; exact right_mem_segment ℝ _ _)
      · exact Or.inr (by rw [hx, hqs]; exact right_mem_segment ℝ _ _)

theorem exists_supported_polygonalArc_push {n : ℕ}
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (p : ℝ → Polygon E (n + 3)) (i : Fin (n + 1))
    (hp_smooth : ∀ j, ContDiff ℝ ∞ (fun t => p t j))
    (hp_good : ∀ t, IsSimplePolygonalArc (p t) ∧ p t 0 = A ∧
      p t (Fin.last (n + 2)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
        X A < X (p t j) ∧ X (p t j) < X B)
    {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d)
    (hp_ad : ∀ t ∈ Ioo (a - 2 * d) (b + 2 * d),
      IsAdmissibleArcVertex (p t) i.castSucc.succ) :
    ∃ χ θ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
      (∀ t ∈ Icc (a - d) (b + d), χ t = 1) ∧
      (∀ t, t ≤ a - 2 * d ∨ b + 2 * d ≤ t → χ t = 0) ∧
      ContDiff ℝ ∞ θ ∧ (∀ t, θ t ∈ Icc (a - d) (b + d)) ∧
      (∀ t ∈ Icc a b, θ t = t) ∧
      let k := i.castSucc.succ
      let P : ℝ × ℝ → Polygon E (n + 3) := fun z =>
        polygonPushVertex (p z.2) k (Real.smoothTransition z.1 * χ z.2)
      let H := fun t => P (1, t)
      let q := fun t => polygonArcDeleteVertex (H (θ t)) k
      (∀ j, ContDiff ℝ ∞ (fun z : ℝ × ℝ => P z j)) ∧
      (∀ s t, IsSimplePolygonalArc (P (s, t)) ∧ P (s, t) 0 = A ∧
        P (s, t) (Fin.last (n + 2)) = B ∧
        ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
          X A < X (P (s, t) j) ∧ X (P (s, t) j) < X B) ∧
      (∀ s t, s ≤ 0 ∨ t ≤ a - 2 * d ∨ b + 2 * d ≤ t → P (s, t) = p t) ∧
      (∀ s t, 1 ≤ s → P (s, t) = H t) ∧
      (∀ s t j, j ≠ k → P (s, t) j = p t j) ∧
      (∀ s t, IsAdmissibleArcVertex (p t) k → IsAdmissibleArcVertex (P (s, t)) k) ∧
      (∀ t ∈ Icc (a - d) (b + d),
        H t k = midpoint ℝ (H t ((finRotate (n + 3)).symm k))
          (H t (finRotate (n + 3) k))) ∧
      (∀ j, ContDiff ℝ ∞ (fun t => q t j)) ∧
      (∀ t, IsSimplePolygonalArc (q t) ∧ q t 0 = A ∧
        q t (Fin.last (n + 1)) = B ∧
        ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) → X A < X (q t j) ∧ X (q t j) < X B) ∧
      ∀ t, polygonArcBoundary (q t) = polygonArcBoundary (H (θ t)) ∧
        polygonArcInsertVertex (q t) i (1 / 2) = H (θ t) := by
  obtain ⟨χ, hχ, hχbound, hχone, hχzero⟩ :=
    exists_smooth_interval_cutoff (a - d) (b + d) hd
  obtain ⟨θ, hθ, hθrange, hθid⟩ := exists_smooth_interval_clamp hab hd
  have hzero (t : ℝ) (ht : t ≤ a - 2 * d ∨ b + 2 * d ≤ t) : χ t = 0 := by
    apply hχzero t
    rcases ht with ht | ht
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  refine ⟨χ, θ, hχ, hχbound, hχone, hzero, hθ, hθrange, hθid, ?_⟩
  let k := i.castSucc.succ
  let P : ℝ × ℝ → Polygon E (n + 3) := fun z =>
    polygonPushVertex (p z.2) k (Real.smoothTransition z.1 * χ z.2)
  let H := fun t => P (1, t)
  let q := fun t => polygonArcDeleteVertex (H (θ t)) k
  change (∀ j, ContDiff ℝ ∞ (fun z : ℝ × ℝ => P z j)) ∧ _
  obtain ⟨hk0, hkl, hleft, hright, hpred, hsucc⟩ := arcLocal_center_indices i
  have hpk : (finRotate (n + 3)).symm k ≠ k := by
    rw [hpred]
    intro h
    have hv := congrArg Fin.val h
    change i.val = i.val + 1 at hv
    omega
  have hsk : finRotate (n + 3) k ≠ k := by
    rw [hsucc]
    intro h
    have hv := congrArg Fin.val h
    change i.val + 1 + 1 = i.val + 1 at hv
    omega
  have hcoef (s t : ℝ) : Real.smoothTransition s * χ t ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (Real.smoothTransition.nonneg s) (hχbound t).1, ?_⟩
    nlinarith [Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s,
      (hχbound t).1, (hχbound t).2]
  have hsmooth (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun z : ℝ × ℝ => P z j) :=
    contDiff_polygonPushVertex_apply k j (fun l => (hp_smooth l).comp contDiff_snd)
      ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (hχ.comp contDiff_snd))
  have hother (s t : ℝ) (j : Fin (n + 3)) (hj : j ≠ k) : P (s, t) j = p t j :=
    polygonReplaceVertex_apply_of_ne _ _ _ hj
  have hgood (s t : ℝ) : IsSimplePolygonalArc (P (s, t)) ∧ P (s, t) 0 = A ∧
      P (s, t) (Fin.last (n + 2)) = B ∧
      ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
        X A < X (P (s, t) j) ∧ X (P (s, t) j) < X B := by
    obtain ⟨hp, hp0, hplast, hpX⟩ := hp_good t
    refine ⟨?_, (hother s t 0 hk0.symm).trans hp0,
      (hother s t _ hkl.symm).trans hplast, ?_⟩
    · by_cases ht : χ t = 0
      · simpa only [P, ht, mul_zero, polygonPushVertex_zero] using hp
      · have hmem : t ∈ Ioo (a - 2 * d) (b + 2 * d) := by
          constructor
          · exact lt_of_not_ge (fun h => ht (hzero t (Or.inl h)))
          · exact lt_of_not_ge (fun h => ht (hzero t (Or.inr h)))
        exact hp.isSimple_polygonPushVertex k (hp_ad t hmem) (hcoef s t)
    · intro j hj0 hjl
      by_cases hjk : j = k
      · subst j
        have ha : X A ≤ X (p t ((finRotate (n + 3)).symm k)) ∧
            X (p t ((finRotate (n + 3)).symm k)) < X B := by
          have hl : (finRotate (n + 3)).symm k ≠ Fin.last (n + 2) := by
            rw [hpred]
            exact Fin.castSucc_ne_last _
          by_cases hz : (finRotate (n + 3)).symm k = 0
          · rw [hz, hp0]
            exact ⟨le_rfl, hAB⟩
          · exact ⟨(hpX _ hz hl).1.le, (hpX _ hz hl).2⟩
        have hb : X A < X (p t (finRotate (n + 3) k)) ∧
            X (p t (finRotate (n + 3) k)) ≤ X B := by
          have hz : finRotate (n + 3) k ≠ 0 := by rw [hsucc]; exact Fin.succ_ne_zero _
          by_cases hl : finRotate (n + 3) k = Fin.last (n + 2)
          · rw [hl, hplast]
            exact ⟨hAB, le_rfl⟩
          · exact ⟨(hpX _ hz hl).1, (hpX _ hz hl).2.le⟩
        have hm : X (midpoint ℝ (p t ((finRotate (n + 3)).symm k))
            (p t (finRotate (n + 3) k))) ∈ Ioo (X A) (X B) := by
          simp only [midpoint_eq_smul_add, map_smul, map_add, smul_eq_mul, invOf_eq_inv]
          constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
        have hx := (convex_Ioo (X A) (X B)).lineMap_mem (hpX k hk0 hkl) hm (hcoef s t)
        change X (polygonPushVertex (p t) k (Real.smoothTransition s * χ t) k) ∈
          Ioo (X A) (X B)
        rw [polygonPushVertex, polygonReplaceVertex_apply_same]
        change X.toAffineMap (AffineMap.lineMap (p t k)
          (midpoint ℝ (p t ((finRotate (n + 3)).symm k))
            (p t (finRotate (n + 3) k))) (Real.smoothTransition s * χ t)) ∈
          Ioo (X A) (X B)
        rw [X.toAffineMap.apply_lineMap]
        exact hx
      · rw [hother s t j hjk]
        exact hpX j hj0 hjl
  have hmid (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) :
      H t k = midpoint ℝ (H t ((finRotate (n + 3)).symm k))
        (H t (finRotate (n + 3) k)) := by
    rw [show H t ((finRotate (n + 3)).symm k) = p t ((finRotate (n + 3)).symm k)
        from hother 1 t _ hpk,
      show H t (finRotate (n + 3) k) = p t (finRotate (n + 3) k) from hother 1 t _ hsk]
    simp only [H, P, Real.smoothTransition.one, hχone t ht, mul_one,
      polygonPushVertex_one_vertex]
  have hstraight (t : ℝ) : H (θ t) k ∈
      segment ℝ (H (θ t) ((finRotate (n + 3)).symm k))
        (H (θ t) (finRotate (n + 3) k)) := by
    rw [hmid _ (hθrange t)]
    exact midpoint_mem_segment _ _
  have hqsmooth (j : Fin (n + 2)) : ContDiff ℝ ∞ (fun t => q t j) :=
    ((hsmooth (k.succAbove j)).comp (contDiff_const.prodMk contDiff_id)).comp hθ
  have hqgood (t : ℝ) : IsSimplePolygonalArc (q t) ∧ q t 0 = A ∧
      q t (Fin.last (n + 1)) = B ∧
      ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) → X A < X (q t j) ∧ X (q t j) < X B := by
    obtain ⟨hp, hp0, hplast, hpX⟩ := hgood 1 (θ t)
    have hends := polygonArcDeleteVertex_endpoints (H (θ t)) k hk0 hkl
    exact ⟨hp.isSimple_polygonArcDeleteVertex k hk0 hkl (hstraight t),
      hends.1.trans hp0, hends.2.trans hplast, fun j hj0 hjl =>
        hpX _ (Fin.succAbove_ne_zero hk0 hj0) (Fin.succAbove_ne_last hkl hjl)⟩
  refine ⟨hsmooth, hgood, ?_, ?_, hother, ?_, hmid, hqsmooth, hqgood, ?_⟩
  · intro s t ht
    rcases ht with hs | ht
    · simp only [Real.smoothTransition.zero_of_nonpos hs, zero_mul, polygonPushVertex_zero]
    · simp only [hzero t ht, mul_zero, polygonPushVertex_zero]
  · intro s t hs
    simp only [Real.smoothTransition.one_of_one_le hs, Real.smoothTransition.one]
  · intro s t had
    exact arcLocal_same_admissible (hp_good t).1 k had (hcoef s t)
  · intro t
    refine ⟨polygonArcDeleteVertex_boundary (H (θ t)) k hk0 hkl (hstraight t), ?_⟩
    apply polygonArcInsertVertex_delete_eq
    rw [hleft, hright, ← hpred, ← hsucc]
    simpa only [midpoint, invOf_eq_inv, one_div] using hmid (θ t) (hθrange t)

end PoincareConjecture.M25.Topology3D
