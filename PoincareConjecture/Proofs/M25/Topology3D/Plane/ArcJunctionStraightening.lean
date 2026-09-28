import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcStraightWeight
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcLocalStraightening

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem single_corner_junction {n : ℕ}
    (hdim : Module.finrank ℝ E = 2)
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (H : ℝ → Polygon E (n + 3))
    (hH_smooth : ∀ j, ContDiff ℝ ∞ (fun t => H t j))
    (hH_good : ∀ t, IsSimplePolygonalArc (H t) ∧ H t 0 = A ∧
      H t (Fin.last (n + 2)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
        X A < X (H t j) ∧ X (H t j) < X B)
    (i : Fin (n + 1))
    (t0 r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hstraight : ∀ t, |t - t0| ≤ r →
      H t i.castSucc.succ ∈ segment ℝ
        (H t ((finRotate (n + 3)).symm i.castSucc.succ))
        (H t (finRotate (n + 3) i.castSucc.succ))) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ F : ℝ × ℝ → Polygon E (n + 3),
      (∀ v, ContDiff ℝ ∞ (fun z => F z v)) ∧
      (∀ s t, IsSimplePolygonalArc (F (s, t)) ∧ F (s, t) 0 = A ∧
        F (s, t) (Fin.last (n + 2)) = B ∧
        ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
          X A < X (F (s, t) v) ∧ X (F (s, t) v) < X B) ∧
      (∀ s t, s ≤ 0 → F (s, t) = H t) ∧
      (∀ s t, 1 ≤ s → F (s, t) = F (1, t)) ∧
      (∀ s t, δ ≤ |t - t0| → F (s, t) = H t) ∧
      (∀ t, |t - t0| < ε → ∀ v, F (1, t) v ∈ segment ℝ A B) ∧
      ∀ s t,
        (H t i.castSucc.succ ∈ segment ℝ
            (H t ((finRotate (n + 3)).symm i.castSucc.succ))
            (H t (finRotate (n + 3) i.castSucc.succ)) →
          F (s, t) i.castSucc.succ ∈ segment ℝ
            (F (s, t) ((finRotate (n + 3)).symm i.castSucc.succ))
            (F (s, t) (finRotate (n + 3) i.castSucc.succ))) := by
  classical
  let k : Fin (n + 3) := i.castSucc.succ
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact Fin.succ_ne_zero _
  have hkl : k ≠ Fin.last (n + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [k, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
    omega
  let d : ℝ := min δ r / 8
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdδ : 4 * d < δ := by
    have hle : 8 * d ≤ δ := by
      dsimp [d]
      linarith [min_le_left δ r]
    linarith
  have hdr : 4 * d < r := by
    have hle : 8 * d ≤ r := by
      dsimp [d]
      linarith [min_le_right δ r]
    linarith
  let a : ℝ := t0 - 2 * d
  let b : ℝ := t0 + 2 * d
  have hab : a ≤ b := by dsimp [a, b]; linarith
  obtain ⟨θ, hθsmooth, hθrange, hθid⟩ :=
    exists_smooth_interval_clamp (a := a) (b := b) (d := d) hab hd
  let K : Set ℝ := Icc (t0 - d) (t0 + d)
  let U : Set ℝ := Ioo (t0 - 2 * d) (t0 + 2 * d)
  have hKU : K ⊆ U := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hθU (t : ℝ) (ht : t ∈ U) : θ t = t := by
    apply hθid t
    dsimp [a, b]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hθstraight (t : ℝ) :
      H (θ t) k ∈ segment ℝ (H (θ t) ((finRotate (n + 3)).symm k))
        (H (θ t) (finRotate (n + 3) k)) := by
    apply hstraight
    have hrange := hθrange t
    dsimp [a, b] at hrange
    have hbound : |θ t - t0| ≤ 3 * d := by
      rw [abs_le]
      constructor <;> linarith [hrange.1, hrange.2]
    linarith [hbound, hdr]
  have hkleft : k.succAbove i.castSucc =
      (finRotate (n + 3)).symm k := by
    have hleft : k.succAbove i.castSucc = i.castSucc.castSucc := by
      dsimp [k]
      apply Fin.ext
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      rw [if_pos (by omega)]
      rfl
    rw [hleft]
    apply (finRotate (n + 3)).injective
    rw [Equiv.apply_symm_apply]
    exact finRotate_of_lt i.castSucc.isLt
  have hkright : k.succAbove i.succ = finRotate (n + 3) k := by
    have hright : k.succAbove i.succ = i.succ.succ := by
      dsimp [k]
      apply Fin.ext
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
      rw [if_neg (by omega)]
      rfl
    rw [hright]
    exact (finRotate_of_lt i.succ.isLt).symm
  let q : ℝ → Polygon E (n + 2) := fun t =>
    polygonArcDeleteVertex (H (θ t)) k
  have hq_smooth (j : Fin (n + 2)) :
      ContDiff ℝ ∞ (fun t => q t j) := by
    exact (hH_smooth (k.succAbove j)).comp hθsmooth
  have hq_good (t : ℝ) : IsSimplePolygonalArc (q t) ∧ q t 0 = A ∧
      q t (Fin.last (n + 1)) = B ∧
      ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
        X A < X (q t j) ∧ X (q t j) < X B := by
    obtain ⟨hp, hp0, hplast, hpX⟩ := hH_good (θ t)
    have hend := polygonArcDeleteVertex_endpoints (H (θ t)) k hk0 hkl
    refine ⟨hp.isSimple_polygonArcDeleteVertex k hk0 hkl (hθstraight t),
      hend.1.trans hp0, hend.2.trans hplast, ?_⟩
    intro j hj0 hjl
    exact hpX _ (Fin.succAbove_ne_zero hk0 hj0) (Fin.succAbove_ne_last hkl hjl)
  obtain ⟨ε, hε, hεδ, Q, hQsmooth, hQgood, hQzero, hQone, hQfix, hQflat⟩ :=
    exists_local_polygonalArc_straightening hdim A B X hAB q hq_smooth hq_good t0 hd
  obtain ⟨w, hw_smooth, hwval, hwrecover⟩ :=
    exists_polygonalArc_straight_weight H i hH_smooth (a := a) (b := b) (d := d)
      hab hd (fun t _ => (hH_good t).1) (fun t ht => by
        rw [hkleft, hkright]
        apply hstraight
        have hbound : |t - t0| ≤ 3 * d := by
          dsimp [a, b] at ht
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        linarith [hbound, hdr])
  have hqdelete (t : ℝ) (ht : t ∈ U) :
      q t = polygonArcDeleteVertex (H t) k := by
    dsimp [q]
    rw [hθU t ht]
  have hweight (t : ℝ) (ht : t ∈ U) :
      H t k = AffineMap.lineMap (H t (k.succAbove i.castSucc))
        (H t (k.succAbove i.succ)) (w t) := by
    simpa [k] using hwrecover t ⟨by dsimp [a]; linarith [ht.1], by dsimp [b]; linarith [ht.2]⟩
  obtain ⟨R, hRin, hRout, hRsmooth, hRgood, hRzero, hRone, hRfix, _,
      hRlocal⟩ :=
    exists_relative_polygonalArc_lift A B X hAB i H Q w
      (K := K) (U := U) isClosed_Icc isOpen_Ioo hKU hH_smooth hH_good
      hQsmooth hQgood hw_smooth hwval
      (fun s t hs => (hQzero s t hs).trans (hQzero 0 t le_rfl).symm)
      hQone
      (fun s t ht => by
        have hfar : d ≤ |t - t0| := by
          by_contra hn
          have hh := abs_lt.mp (lt_of_not_ge hn)
          exact ht ⟨by linarith [hh.1], by linarith [hh.2]⟩
        rw [hQfix s t hfar, hQzero 0 t le_rfl])
      (fun t ht => (hQzero 0 t le_rfl).trans (hqdelete t ht)) hweight
  have hflat (t : ℝ) (ht : |t - t0| < ε) :
      ∀ v, R (1, t) v ∈ segment ℝ A B := by
    have hU : t ∈ U := by
      have hh := abs_lt.mp ht
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    rw [hRin 1 t hU]
    obtain ⟨hc, hret, _, _, _⟩ := polygonArcInsertVertex_spec (Q (1, t)) i (w t)
    intro v
    rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ v with rfl | ⟨v, rfl⟩
    · rw [hc]
      exact (convex_segment (𝕜 := ℝ) A B).lineMap_mem
        (hQflat t ht i.castSucc) (hQflat t ht i.succ) ⟨(hwval t).1.le, (hwval t).2.le⟩
    · rw [hret]
      exact hQflat t ht v
  refine ⟨ε, hε, lt_trans hεδ (by linarith), R, hRsmooth, hRgood,
    hRzero, hRone, ?_, hflat, ?_⟩
  · intro s t ht
    apply hRfix
    intro hm
    have hh : |t - t0| ≤ d := abs_le.mpr
      ⟨by linarith [hm.1], by linarith [hm.2]⟩
    linarith
  · intro s t hst
    by_cases ht : t ∈ U
    · exact (hRlocal s t ht).2.2.2.1
    · rw [hRout s t ht]
      exact hst

private theorem junction_delete_index_bridge {n : ℕ}
    (k l : Fin (n + 3))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 2))
    (hl0 : l ≠ 0) (hll : l ≠ Fin.last (n + 2))
    (hne : l ≠ k)
    (hprev : l ≠ (finRotate (n + 3)).symm k)
    (hnext : l ≠ finRotate (n + 3) k) :
    2 ≤ n ∧ ∃ j' : Fin n,
      k.succAbove j'.castSucc.succ = l ∧
      k.succAbove ((finRotate (n + 2)).symm j'.castSucc.succ) =
        (finRotate (n + 3)).symm l ∧
      k.succAbove (finRotate (n + 2) j'.castSucc.succ) =
        finRotate (n + 3) l := by
  have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk0
  have hklt : k.val < n + 2 := Fin.lt_last_iff_ne_last.mpr hkl
  have hlpos : 0 < l.val := Fin.pos_iff_ne_zero.mpr hl0
  have hllt : l.val < n + 2 := Fin.lt_last_iff_ne_last.mpr hll
  have hkp := coe_finRotate_symm_of_ne_zero hk0
  have hks := coe_finRotate_of_ne_last hkl
  have hnev : l.val ≠ k.val := fun h => hne (Fin.ext h)
  have hpv : l.val ≠ k.val - 1 := by
    intro h
    exact hprev (Fin.ext (h.trans hkp.symm))
  have hsv : l.val ≠ k.val + 1 := by
    intro h
    exact hnext (Fin.ext (h.trans hks.symm))
  have hn : 2 ≤ n := by omega
  obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hne
  have hq0 : q ≠ 0 := by
    intro h
    apply hl0
    rw [← hq, h, Fin.succAbove_ne_zero_zero hk0]
  have hql : q ≠ Fin.last (n + 1) := by
    intro h
    apply hll
    rw [← hq, h, Fin.succAbove_ne_last_last hkl]
  have hqpos : 0 < q.val := Fin.pos_iff_ne_zero.mpr hq0
  have hqlt : q.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hql
  let j' : Fin n := ⟨q.val - 1, by omega⟩
  have hjq : j'.castSucc.succ = q := by
    apply Fin.ext
    change q.val - 1 + 1 = q.val
    omega
  have hval (a : Fin (n + 2)) :
      (k.succAbove a).val = if a.val < k.val then a.val else a.val + 1 := by
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> rfl
  have hqv : (if q.val < k.val then q.val else q.val + 1) = l.val := by
    simpa only [hval] using congrArg Fin.val hq
  refine ⟨hn, j', ?_, ?_, ?_⟩
  · rw [hjq]
    exact hq
  · rw [hjq]
    apply Fin.ext
    rw [hval, coe_finRotate_symm_of_ne_zero hq0, coe_finRotate_symm_of_ne_zero hl0]
    split_ifs at hqv ⊢ <;> omega
  · rw [hjq]
    apply Fin.ext
    rw [hval, coe_finRotate_of_ne_last hql, coe_finRotate_of_ne_last hll]
    split_ifs at hqv ⊢ <;> omega

theorem exists_local_polygonalArc_junction_straightening {n : ℕ}
    (hdim : Module.finrank ℝ E = 2)
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (H : ℝ → Polygon E (n + 3))
    (hH_smooth : ∀ v, ContDiff ℝ ∞ (fun t => H t v))
    (hH_good : ∀ t, IsSimplePolygonalArc (H t) ∧ H t 0 = A ∧
      H t (Fin.last (n + 2)) = B ∧ ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
        X A < X (H t v) ∧ X (H t v) < X B)
    (i j : Fin (n + 1))
    (hcompat : i.castSucc.succ = j.castSucc.succ ∨
      (j.castSucc.succ ≠ i.castSucc.succ ∧
        j.castSucc.succ ≠ (finRotate (n + 3)).symm i.castSucc.succ ∧
        j.castSucc.succ ≠ finRotate (n + 3) i.castSucc.succ))
    (t0 : ℝ) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hstraight : ∀ t, |t - t0| ≤ r →
      (H t i.castSucc.succ ∈ segment ℝ
        (H t ((finRotate (n + 3)).symm i.castSucc.succ))
        (H t (finRotate (n + 3) i.castSucc.succ))) ∧
      (H t j.castSucc.succ ∈ segment ℝ
        (H t ((finRotate (n + 3)).symm j.castSucc.succ))
        (H t (finRotate (n + 3) j.castSucc.succ)))) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ F : ℝ × ℝ → Polygon E (n + 3),
      (∀ v, ContDiff ℝ ∞ (fun z => F z v)) ∧
      (∀ s t, IsSimplePolygonalArc (F (s, t)) ∧ F (s, t) 0 = A ∧
        F (s, t) (Fin.last (n + 2)) = B ∧
        ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
          X A < X (F (s, t) v) ∧ X (F (s, t) v) < X B) ∧
      (∀ s t, s ≤ 0 → F (s, t) = H t) ∧
      (∀ s t, 1 ≤ s → F (s, t) = F (1, t)) ∧
      (∀ s t, δ ≤ |t - t0| → F (s, t) = H t) ∧
      (∀ t, |t - t0| < ε → ∀ v, F (1, t) v ∈ segment ℝ A B) ∧
      ∀ s t,
        (H t i.castSucc.succ ∈ segment ℝ
            (H t ((finRotate (n + 3)).symm i.castSucc.succ))
            (H t (finRotate (n + 3) i.castSucc.succ)) →
          F (s, t) i.castSucc.succ ∈ segment ℝ
            (F (s, t) ((finRotate (n + 3)).symm i.castSucc.succ))
            (F (s, t) (finRotate (n + 3) i.castSucc.succ))) ∧
        (H t j.castSucc.succ ∈ segment ℝ
            (H t ((finRotate (n + 3)).symm j.castSucc.succ))
            (H t (finRotate (n + 3) j.castSucc.succ)) →
          F (s, t) j.castSucc.succ ∈ segment ℝ
            (F (s, t) ((finRotate (n + 3)).symm j.castSucc.succ))
            (F (s, t) (finRotate (n + 3) j.castSucc.succ))) := by
  classical
  rcases hcompat with heq | ⟨hne, hprev, hnext⟩
  · have hij : i = j := by
      apply Fin.ext
      have hh := congrArg Fin.val heq
      simp only [Fin.val_succ, Fin.val_castSucc] at hh
      omega
    subst j
    obtain ⟨ε, hε, hεδ, F, hFs, hFg, hF0, hF1, hFfix, hFflat, hFkeep⟩ :=
      single_corner_junction hdim A B X hAB H hH_smooth hH_good i t0 r δ hr hδ
        (fun t ht => (hstraight t ht).1)
    exact ⟨ε, hε, hεδ, F, hFs, hFg, hF0, hF1, hFfix, hFflat,
      fun s t => ⟨hFkeep s t, hFkeep s t⟩⟩
  · have hk0 : i.castSucc.succ ≠ (0 : Fin (n + 3)) := Fin.succ_ne_zero _
    have hl0 : j.castSucc.succ ≠ (0 : Fin (n + 3)) := Fin.succ_ne_zero _
    have hkl : i.castSucc.succ ≠ Fin.last (n + 2) := by
      apply Fin.lt_last_iff_ne_last.mp
      change i.val + 1 < n + 2
      omega
    have hll : j.castSucc.succ ≠ Fin.last (n + 2) := by
      apply Fin.lt_last_iff_ne_last.mp
      change j.val + 1 < n + 2
      omega
    obtain ⟨hn, j', hcenter, hpre, hsuc⟩ := junction_delete_index_bridge
      i.castSucc.succ j.castSucc.succ hk0 hkl hl0 hll hne hprev hnext
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
    subst n
    let k : Fin (m + 5) := i.castSucc.succ
    let d : ℝ := min δ r / 8
    have hd : 0 < d := div_pos (lt_min hδ hr) (by norm_num)
    have hdδ : 4 * d < δ := by
      have hh : 8 * d ≤ δ := by dsimp [d]; linarith [min_le_left δ r]
      linarith
    have hdr : 4 * d < r := by
      have hh : 8 * d ≤ r := by dsimp [d]; linarith [min_le_right δ r]
      linarith
    let a : ℝ := t0 - 2 * d
    let b : ℝ := t0 + 2 * d
    have hab : a ≤ b := by dsimp [a, b]; linarith
    obtain ⟨θ, hθs, hθrange, hθid⟩ :=
      exists_smooth_interval_clamp (a := a) (b := b) hab hd
    have hwindow (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) : |t - t0| ≤ r := by
      dsimp [a, b] at ht
      have hh : |t - t0| ≤ 3 * d :=
        abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    let q : ℝ → Polygon E (m + 4) := fun t => polygonArcDeleteVertex (H (θ t)) k
    have hqs (v : Fin (m + 4)) : ContDiff ℝ ∞ (fun t => q t v) :=
      (hH_smooth (k.succAbove v)).comp hθs
    have hqg (t : ℝ) : IsSimplePolygonalArc (q t) ∧ q t 0 = A ∧
        q t (Fin.last (m + 3)) = B ∧ ∀ v, v ≠ 0 → v ≠ Fin.last (m + 3) →
          X A < X (q t v) ∧ X (q t v) < X B := by
      obtain ⟨hp, hp0, hpl, hpX⟩ := hH_good (θ t)
      have he := polygonArcDeleteVertex_endpoints (H (θ t)) k hk0 hkl
      exact ⟨hp.isSimple_polygonArcDeleteVertex k hk0 hkl
          (hstraight _ (hwindow _ (hθrange t))).1,
        he.1.trans hp0, he.2.trans hpl, fun v hv0 hvl =>
          hpX _ (Fin.succAbove_ne_zero hk0 hv0) (Fin.succAbove_ne_last hkl hvl)⟩
    have hqstraight (t : ℝ) : q t j'.castSucc.succ ∈ segment ℝ
        (q t ((finRotate (m + 4)).symm j'.castSucc.succ))
        (q t (finRotate (m + 4) j'.castSucc.succ)) := by
      change H (θ t) (i.castSucc.succ.succAbove j'.castSucc.succ) ∈ segment ℝ
        (H (θ t) (i.castSucc.succ.succAbove ((finRotate (m + 4)).symm j'.castSucc.succ)))
        (H (θ t) (i.castSucc.succ.succAbove (finRotate (m + 4) j'.castSucc.succ)))
      rw [hcenter, hpre, hsuc]
      exact (hstraight _ (hwindow _ (hθrange t))).2
    obtain ⟨ε, hε, hεd, Q, hQs, hQg, hQ0, hQ1, hQfix, hQflat, hQkeep⟩ :=
      single_corner_junction hdim A B X hAB q hqs hqg j' t0 d d hd hd
        (fun t _ => hqstraight t)
    have hleft : k.succAbove i.castSucc = (finRotate (m + 5)).symm k := by
      apply Fin.ext
      rw [coe_finRotate_symm_of_ne_zero hk0]
      simp only [k, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> omega
    have hright : k.succAbove i.succ = finRotate (m + 5) k := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hkl]
      simp only [k, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ]
      omega
    obtain ⟨w, hws, hw, hrecover⟩ := exists_polygonalArc_straight_weight H i hH_smooth
      hab hd (fun t _ => (hH_good t).1) (fun t ht => by
        rw [hleft, hright]
        exact (hstraight t (hwindow t ht)).1)
    let K : Set ℝ := Icc (t0 - d) (t0 + d)
    let U : Set ℝ := Ioo a b
    have hKU : K ⊆ U := by
      intro t ht
      dsimp [U, a, b]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hQoutside (s t : ℝ) (ht : t ∉ K) : Q (s, t) = Q (0, t) := by
      have hfar : d ≤ |t - t0| := by
        by_contra hn
        have hh := abs_lt.mp (lt_of_not_ge hn)
        exact ht ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [hQfix s t hfar, hQ0 0 t le_rfl]
    have hqdelete (t : ℝ) (ht : t ∈ U) :
        q t = polygonArcDeleteVertex (H t) i.castSucc.succ := by
      dsimp only [q]
      rw [hθid t ⟨ht.1.le, ht.2.le⟩]
    obtain ⟨F, hFin, hFout, hFs, hFg, hF0, hF1, hFfix, _, hFlocal⟩ :=
      exists_relative_polygonalArc_lift A B X hAB i H Q w
        (K := K) (U := U) isClosed_Icc isOpen_Ioo hKU hH_smooth hH_good hQs hQg hws hw
        (fun s t hs => (hQ0 s t hs).trans (hQ0 0 t le_rfl).symm) hQ1 hQoutside
        (fun t ht => (hQ0 0 t le_rfl).trans (hqdelete t ht))
        (fun t ht => hrecover t ⟨ht.1.le, ht.2.le⟩)
    refine ⟨ε, hε, by linarith, F, hFs, hFg, hF0, hF1, ?_, ?_, ?_⟩
    · intro s t ht
      apply hFfix
      intro hm
      have hh : |t - t0| ≤ d := abs_le.mpr
        ⟨by linarith [hm.1], by linarith [hm.2]⟩
      linarith
    · intro t ht
      have hU : t ∈ U := by
        have hh := abs_lt.mp ht
        dsimp [U, a, b]
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [hFin 1 t hU]
      obtain ⟨hc, hret, _, _, _⟩ := polygonArcInsertVertex_spec (Q (1, t)) i (w t)
      intro v
      rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ v with rfl | ⟨v, rfl⟩
      · rw [hc]
        exact (convex_segment (𝕜 := ℝ) A B).lineMap_mem
          (hQflat t ht i.castSucc) (hQflat t ht i.succ) ⟨(hw t).1.le, (hw t).2.le⟩
      · rw [hret]
        exact hQflat t ht v
    · intro s t
      by_cases ht : t ∈ U
      · obtain ⟨_, _, hret, hkstraight, _⟩ := hFlocal s t ht
        refine ⟨fun _ => hkstraight, fun _ => ?_⟩
        rw [← hpre, ← hsuc, ← hcenter, hret, hret, hret]
        exact hQkeep s t (hqstraight t)
      · rw [hFout s t ht]
        exact ⟨fun h => h, fun h => h⟩

end PoincareConjecture.M25.Topology3D
