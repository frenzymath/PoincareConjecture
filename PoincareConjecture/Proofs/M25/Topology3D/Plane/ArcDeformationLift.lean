import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcInsertion










set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private theorem arcLift_center_indices {n : ℕ} (i : Fin (n + 1)) :
    i.castSucc.succ ≠ (0 : Fin (n + 3)) ∧
      i.castSucc.succ ≠ Fin.last (n + 2) ∧
      i.castSucc.succ.succAbove i.castSucc = (finRotate (n + 3)).symm i.castSucc.succ ∧
      i.castSucc.succ.succAbove i.succ = finRotate (n + 3) i.castSucc.succ := by
  have hleft : i.castSucc.succ.succAbove i.castSucc = i.castSucc.castSucc := by
    apply Fin.ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    rw [if_pos (by omega)]
    rfl
  have hright : i.castSucc.succ.succAbove i.succ = i.succ.succ := by
    apply Fin.ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    rw [if_neg (by omega)]
    rfl
  refine ⟨Fin.succ_ne_zero _, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  · rw [hleft]
    apply (finRotate (n + 3)).injective
    rw [Equiv.apply_symm_apply]
    exact finRotate_of_lt i.castSucc.isLt
  · have hmid : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    rw [hright, hmid]
    exact (finRotate_of_lt i.succ.isLt).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_relative_polygonalArc_lift {n : ℕ}
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (i : Fin (n + 1)) (H : ℝ → Polygon E (n + 3))
    (Q : ℝ × ℝ → Polygon E (n + 2)) (w : ℝ → ℝ)
    {K U : Set ℝ} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hH_smooth : ∀ j, ContDiff ℝ ∞ (fun t => H t j))
    (hH_good : ∀ t, IsSimplePolygonalArc (H t) ∧ H t 0 = A ∧
      H t (Fin.last (n + 2)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
        X A < X (H t j) ∧ X (H t j) < X B)
    (hQ_smooth : ∀ j, ContDiff ℝ ∞ (fun z : ℝ × ℝ => Q z j))
    (hQ_good : ∀ s t, IsSimplePolygonalArc (Q (s, t)) ∧ Q (s, t) 0 = A ∧
      Q (s, t) (Fin.last (n + 1)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
        X A < X (Q (s, t) j) ∧ X (Q (s, t) j) < X B)
    (hw_smooth : ContDiff ℝ ∞ w) (hw : ∀ t, w t ∈ Ioo (0 : ℝ) 1)
    (hQ_zero : ∀ s t, s ≤ 0 → Q (s, t) = Q (0, t))
    (hQ_one : ∀ s t, 1 ≤ s → Q (s, t) = Q (1, t))
    (hQ_fix : ∀ s t, t ∉ K → Q (s, t) = Q (0, t))
    (hQ_delete : ∀ t ∈ U, Q (0, t) = polygonArcDeleteVertex (H t) i.castSucc.succ)
    (hH_weight : ∀ t ∈ U, H t i.castSucc.succ =
      AffineMap.lineMap (H t (i.castSucc.succ.succAbove i.castSucc))
        (H t (i.castSucc.succ.succAbove i.succ)) (w t)) :
    ∃ R : ℝ × ℝ → Polygon E (n + 3),
      (∀ s t, t ∈ U → R (s, t) = polygonArcInsertVertex (Q (s, t)) i (w t)) ∧
      (∀ s t, t ∉ U → R (s, t) = H t) ∧
      (∀ j, ContDiff ℝ ∞ (fun z : ℝ × ℝ => R z j)) ∧
      (∀ s t, IsSimplePolygonalArc (R (s, t)) ∧ R (s, t) 0 = A ∧
        R (s, t) (Fin.last (n + 2)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
          X A < X (R (s, t) j) ∧ X (R (s, t) j) < X B) ∧
      (∀ s t, s ≤ 0 → R (s, t) = H t) ∧
      (∀ s t, 1 ≤ s → R (s, t) = R (1, t)) ∧
      (∀ s t, t ∉ K → R (s, t) = H t) ∧
      (∀ t, t ∉ K → ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
        ∀ s u, u ∈ V → R (s, u) = H u) ∧
      ∀ s t, t ∈ U →
        let k := i.castSucc.succ
        polygonArcDeleteVertex (R (s, t)) k = Q (s, t) ∧
          polygonArcBoundary (R (s, t)) = polygonArcBoundary (Q (s, t)) ∧
          (∀ j : Fin (n + 2), R (s, t) (k.succAbove j) = Q (s, t) j) ∧
          R (s, t) k ∈ segment ℝ (R (s, t) ((finRotate (n + 3)).symm k))
            (R (s, t) (finRotate (n + 3) k)) ∧ IsAdmissibleArcVertex (R (s, t)) k := by
  classical
  let R : ℝ × ℝ → Polygon E (n + 3) := fun z =>
    if z.2 ∈ U then polygonArcInsertVertex (Q z) i (w z.2) else H z.2
  have hin (s t : ℝ) (ht : t ∈ U) :
      R (s, t) = polygonArcInsertVertex (Q (s, t)) i (w t) := if_pos ht
  have hout (s t : ℝ) (ht : t ∉ U) : R (s, t) = H t := if_neg ht
  have hbase (t : ℝ) (ht : t ∈ U) :
      polygonArcInsertVertex (Q (0, t)) i (w t) = H t := by
    rw [hQ_delete t ht]
    exact polygonArcInsertVertex_delete_eq (H t) i (w t) (hH_weight t ht)
  have hfix (s t : ℝ) (ht : t ∉ K) : R (s, t) = H t := by
    by_cases hu : t ∈ U
    · rw [hin s t hu, hQ_fix s t ht, hbase t hu]
    · exact hout s t hu
  have hsmooth (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun z : ℝ × ℝ => R z j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases ht : z.2 ∈ U
    · apply (contDiff_polygonArcInsertVertex_apply i j hQ_smooth
        (hw_smooth.comp contDiff_snd)).contDiffAt.congr_of_eventuallyEq
      have hn : (Prod.snd ⁻¹' U : Set (ℝ × ℝ)) ∈ 𝓝 z :=
        (hU.preimage continuous_snd).mem_nhds ht
      filter_upwards [hn] with y hy
      exact congrArg (fun p : Polygon E (n + 3) => p j) (hin y.1 y.2 hy)
    · apply ((hH_smooth j).comp contDiff_snd).contDiffAt.congr_of_eventuallyEq
      have htn : z.2 ∉ K := fun h => ht (hKU h)
      have hn : (Prod.snd ⁻¹' Kᶜ : Set (ℝ × ℝ)) ∈ 𝓝 z :=
        (hK.isOpen_compl.preimage continuous_snd).mem_nhds htn
      filter_upwards [hn] with y hy
      exact congrArg (fun p : Polygon E (n + 3) => p j) (hfix y.1 y.2 hy)
  have hgood (s t : ℝ) : IsSimplePolygonalArc (R (s, t)) ∧ R (s, t) 0 = A ∧
      R (s, t) (Fin.last (n + 2)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
        X A < X (R (s, t) j) ∧ X (R (s, t) j) < X B := by
    by_cases ht : t ∈ U
    · rw [hin s t ht]
      obtain ⟨hq, hq0, hql, hqX⟩ := hQ_good s t
      obtain ⟨_, _, h0, hl, _⟩ := polygonArcInsertVertex_spec (Q (s, t)) i (w t)
      refine ⟨hq.isSimple_polygonArcInsertVertex i (w t) (hw t),
        h0.trans hq0, hl.trans hql, ?_⟩
      intro j hj0 hjl
      have hab : X (Q (s, t) 0) < X (Q (s, t) (Fin.last (n + 1))) := by
        rwa [hq0, hql]
      have hbounds : ∀ l, l ≠ 0 → l ≠ Fin.last (n + 1) →
          X (Q (s, t) 0) < X (Q (s, t) l) ∧
            X (Q (s, t) l) < X (Q (s, t) (Fin.last (n + 1))) := by
        simpa only [hq0, hql] using hqX
      have hx := polygonArcInsertVertex_strict_bounds (Q (s, t)) i (w t) (hw t)
        X hab hbounds j hj0 hjl
      simpa only [h0, hl, hq0, hql] using hx
    · rw [hout s t ht]
      exact hH_good t
  refine ⟨R, hin, hout, hsmooth, hgood, ?_, ?_, hfix, ?_, ?_⟩
  · intro s t hs
    by_cases ht : t ∈ U
    · rw [hin s t ht, hQ_zero s t hs, hbase t ht]
    · exact hout s t ht
  · intro s t hs
    by_cases ht : t ∈ U
    · rw [hin s t ht, hin 1 t ht, hQ_one s t hs]
    · rw [hout s t ht, hout 1 t ht]
  · intro t ht
    exact ⟨Kᶜ, hK.isOpen_compl, ht, fun s u hu => hfix s u hu⟩
  · intro s t ht
    dsimp only
    rw [hin s t ht]
    obtain ⟨hk0, hkl, hpred, hsucc⟩ := arcLift_center_indices i
    obtain ⟨hsame, hret, _, _, hdel⟩ := polygonArcInsertVertex_spec (Q (s, t)) i (w t)
    have hwcc : w t ∈ Icc (0 : ℝ) 1 := ⟨(hw t).1.le, (hw t).2.le⟩
    have hstraight : polygonArcInsertVertex (Q (s, t)) i (w t) i.castSucc.succ ∈
        segment ℝ
          (polygonArcInsertVertex (Q (s, t)) i (w t)
            ((finRotate (n + 3)).symm i.castSucc.succ))
          (polygonArcInsertVertex (Q (s, t)) i (w t)
            (finRotate (n + 3) i.castSucc.succ)) := by
      rw [← hpred, ← hsucc, hret, hret, hsame]
      exact lineMap_mem_segment ℝ _ _ hwcc
    exact ⟨hdel, polygonArcInsertVertex_boundary (Q (s, t)) i (w t) hwcc,
      hret, hstraight, isAdmissibleArcVertex_of_mem_segment _ _ hk0 hkl hstraight⟩

end PoincareConjecture.M25.Topology3D
