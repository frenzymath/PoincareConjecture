import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcJunctionStraightening
import Mathlib.Data.Finset.Max










set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M25.Topology3D



theorem exists_relative_polygonalArc_finite_junctions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {n : ℕ}
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    {ε : ℝ} (hε : 0 < ε) (_hε' : ε < 1 / 4)
    {N : ℕ} (hN : 0 < N) (c : Fin N → Fin (n + 1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < min (1 / (32 * (N : ℝ))) (ε / 8))
    (hcompat : ∀ i j : Fin N, i.val + 1 = j.val →
      (c i).castSucc.succ = (c j).castSucc.succ ∨
      ((c j).castSucc.succ ≠ (c i).castSucc.succ ∧
        (c j).castSucc.succ ≠ (finRotate (n + 3)).symm (c i).castSucc.succ ∧
        (c j).castSucc.succ ≠ finRotate (n + 3) (c i).castSucc.succ))
    (H : ℝ → Polygon E (n + 3))
    (hH_smooth : ∀ v, ContDiff ℝ ∞ (fun t => H t v))
    (hH_good : ∀ t, IsSimplePolygonalArc (H t) ∧ H t 0 = A ∧
      H t (Fin.last (n + 2)) = B ∧ ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
        X A < X (H t v) ∧ X (H t v) < X B)
    (hflat : ∀ t, t ∈ Ioo (-ε) ε ∪ Ioo (1 - ε) (1 + ε) →
      ∀ v, H t v ∈ segment ℝ A B)
    (hstraight : ∀ i : Fin N,
      ∀ t ∈ Ioo ((i.val : ℝ) / N - ρ) (((i.val : ℝ) + 1) / N + ρ),
        H t (c i).castSucc.succ ∈ segment ℝ
          (H t ((finRotate (n + 3)).symm (c i).castSucc.succ))
          (H t (finRotate (n + 3) (c i).castSucc.succ))) :
    ∃ η : ℝ, 0 < η ∧ η < ρ / 8 ∧ ∃ J : ℝ × ℝ → Polygon E (n + 3),
      (∀ v, ContDiff ℝ ∞ (fun z => J z v)) ∧
      (∀ s t, IsSimplePolygonalArc (J (s, t)) ∧ J (s, t) 0 = A ∧
        J (s, t) (Fin.last (n + 2)) = B ∧
        ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
          X A < X (J (s, t) v) ∧ X (J (s, t) v) < X B) ∧
      (∀ s t, s ≤ 0 → J (s, t) = H t) ∧
      (∀ s t, 1 ≤ s → J (s, t) = J (1, t)) ∧
      (∀ s t, t ≤ ε / 4 ∨ 1 - ε / 4 ≤ t → J (s, t) = H t) ∧
      (∀ s t, ∀ i : Fin N,
        t ∈ Ioo ((i.val : ℝ) / N - ρ) (((i.val : ℝ) + 1) / N + ρ) →
          J (s, t) (c i).castSucc.succ ∈ segment ℝ
            (J (s, t) ((finRotate (n + 3)).symm (c i).castSucc.succ))
            (J (s, t) (finRotate (n + 3) (c i).castSucc.succ))) ∧
      ∀ j : Fin (N + 1), ∀ t, |t - (j.val : ℝ) / N| < η →
        ∀ v, J (1, t) v ∈ segment ℝ A B := by
  classical
  let Good (q : Polygon E (n + 3)) : Prop := IsSimplePolygonalArc q ∧ q 0 = A ∧
    q (Fin.last (n + 2)) = B ∧ ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
      X A < X (q v) ∧ X (q v) < X B
  let Flat (q : Polygon E (n + 3)) : Prop := ∀ v, q v ∈ segment ℝ A B
  let Straight (q : Polygon E (n + 3)) (i : Fin N) : Prop :=
    q (c i).castSucc.succ ∈ segment ℝ (q ((finRotate (n + 3)).symm (c i).castSucc.succ))
      (q (finRotate (n + 3) (c i).castSucc.succ))
  let W (i : Fin N) := Ioo ((i.val : ℝ) / N - ρ) (((i.val : ℝ) + 1) / N + ρ)
  let τ (j : Fin (N + 1)) : ℝ := j.val / N
  let δ : ℝ := ρ / 8
  let h : ℝ := 1 / N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < h := one_div_pos.mpr hNR
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρε : ρ < ε / 8 := hρ'.trans_le (min_le_right _ _)
  have hρh : ρ < h / 32 := by
    have heq : (1 : ℝ) / (32 * N) = h / 32 := by dsimp [h]; ring
    rw [← heq]
    exact hρ'.trans_le (min_le_left _ _)
  have hstep (a b : ℕ) (hab : a + 1 ≤ b) : (a : ℝ) / N + h ≤ b / N := by
    have hv : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    have hd := div_le_div_of_nonneg_right hv hNR.le
    simpa only [add_div] using hd
  have hτ (j : Fin (N + 1)) : 0 ≤ τ j ∧ τ j ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hNR.le, (div_le_one hNR).mpr ?_⟩
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hseparate (i j : Fin (N + 1)) (hij : i ≠ j) :
      τ i + h ≤ τ j ∨ τ j + h ≤ τ i := by
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hij (Fin.ext he)) with he | he
    · exact Or.inl (hstep i.val j.val he)
    · exact Or.inr (hstep j.val i.val he)
  have hfar (i j : Fin (N + 1)) (hij : i ≠ j) (t : ℝ)
      (ht : |t - τ j| < δ) : δ ≤ |t - τ i| := by
    have ht' := abs_lt.mp ht
    rcases hseparate i j hij with hs | hs
    · have ha := le_abs_self (t - τ i)
      dsimp [δ] at *
      linarith [ht'.1]
    · have ha := neg_le_abs (t - τ i)
      dsimp [δ] at *
      linarith [ht'.2]
  have hstage (j : Fin (N + 1)) : ∃ e : ℝ, 0 < e ∧ e ≤ δ ∧
      ∃ D : ℝ × ℝ → Polygon E (n + 3),
        (∀ v, ContDiff ℝ ∞ (fun z => D z v)) ∧ (∀ s t, Good (D (s, t))) ∧
        (∀ s t, s ≤ 0 → D (s, t) = H t) ∧
        (∀ s t, 1 ≤ s → D (s, t) = D (1, t)) ∧
        (∀ s t, δ ≤ |t - τ j| → D (s, t) = H t) ∧
        (∀ s t, t ≤ ε / 4 ∨ 1 - ε / 4 ≤ t → D (s, t) = H t) ∧
        (∀ s t i, t ∈ W i → Straight (D (s, t)) i) ∧
        ∀ t, |t - τ j| < e → Flat (D (1, t)) := by
    by_cases hj : ε / 2 ≤ τ j ∧ τ j ≤ 1 - ε / 2
    · have hj0 : 0 < j.val := by
        by_contra he
        have heq : j.val = 0 := by omega
        have hz : τ j = 0 := by simp [τ, heq]
        linarith [hj.1]
      have hjN : j.val < N := by
        by_contra he
        have heq : j.val = N := by omega
        have hz : τ j = 1 := by simp [τ, heq, ne_of_gt hNR]
        linarith [hj.2]
      let l : Fin N := ⟨j.val - 1, by omega⟩
      let r : Fin N := ⟨j.val, hjN⟩
      have hl : (l.val : ℝ) + 1 = j.val := by
        exact_mod_cast (show l.val + 1 = j.val by dsimp [l]; omega)
      have hr : (r.val : ℝ) = j.val := rfl
      obtain ⟨e, he, heδ, D, hDs, hDg, hD0, hD1, hDfix, hDflat, hDkeep⟩ :=
        exists_local_polygonalArc_junction_straightening hdim A B X hAB H
          hH_smooth hH_good (c l) (c r) (hcompat l r (by dsimp [l, r]; omega))
          (τ j) (show 0 < ρ / 2 by positivity) hδ (by
            intro t ht
            have ht' := abs_le.mp ht
            constructor
            · apply hstraight l
              have hb : ((l.val : ℝ) + 1) / N = τ j := by rw [hl]
              have ha : (l.val : ℝ) / N = τ j - h := by
                dsimp [τ, h]
                rw [← hl]
                ring
              exact ⟨by rw [ha]; linarith [ht'.1], by rw [hb]; linarith [ht'.2]⟩
            · apply hstraight r
              have ha : (r.val : ℝ) / N = τ j := rfl
              have hb : ((r.val : ℝ) + 1) / N = τ j + h := by dsimp [τ, h, r]; ring
              exact ⟨by rw [ha]; linarith [ht'.1], by rw [hb]; linarith [ht'.2]⟩)
      refine ⟨e, he, heδ.le, D, hDs, hDg, hD0, hD1, hDfix, ?_, ?_, hDflat⟩
      · intro s t ht
        apply hDfix s t
        rcases ht with ht | ht
        · have ha := neg_le_abs (t - τ j)
          dsimp [δ]
          linarith [hj.1]
        · have ha := le_abs_self (t - τ j)
          dsimp [δ]
          linarith [hj.2]
      · intro s t i ht
        by_cases hil : i = l
        · subst i; exact (hDkeep s t).1 (hstraight l t ht)
        · by_cases hir : i = r
          · subst i; exact (hDkeep s t).2 (hstraight r t ht)
          · rw [hDfix s t (by
              have hi : i.val + 1 < j.val ∨ j.val < i.val := by
                have hil' : i.val ≠ j.val - 1 := fun hh => hil (Fin.ext hh)
                have hir' : i.val ≠ j.val := fun hh => hir (Fin.ext hh)
                omega
              rcases hi with hi | hi
              · have hs := hstep (i.val + 1) j.val hi
                have ha := neg_le_abs (t - τ j)
                simp only [Nat.cast_add, Nat.cast_one] at hs
                dsimp [W] at ht
                dsimp [δ, τ] at *
                linarith [ht.2]
              · have hs := hstep j.val i.val hi
                have ha := le_abs_self (t - τ j)
                dsimp [W] at ht
                dsimp [δ, τ] at *
                linarith [ht.1])]
            exact hstraight i t ht
    · refine ⟨min δ (ε / 8), lt_min hδ (by positivity), min_le_left _ _,
        fun z => H z.2, fun v => (hH_smooth v).comp contDiff_snd,
        fun _ t => hH_good t, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ t i ht => hstraight i t ht, ?_⟩
      intro t ht
      apply hflat t
      have ht' := abs_lt.mp (ht.trans_le (min_le_right _ _))
      have hτj := hτ j
      by_cases hj0 : τ j < ε / 2
      · exact Or.inl ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
      · have hj1 : 1 - ε / 2 < τ j := by
          by_contra he
          exact hj ⟨le_of_not_gt hj0, le_of_not_gt he⟩
        exact Or.inr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  choose e he heδ D hDs hDg hD0 hD1 hDfix hDtail hDstraight hDflat using hstage
  let S : Finset ℝ := insert δ (Finset.univ.image e)
  have hS : S.Nonempty := ⟨δ, Finset.mem_insert_self _ _⟩
  have hSpos (x : ℝ) (hx : x ∈ S) : 0 < x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hδ
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact he j
  let η : ℝ := S.min' hS / 2
  have hmin : 0 < S.min' hS := hSpos _ (Finset.min'_mem _ _)
  have hη : 0 < η := half_pos hmin
  have hηδ : η < δ := (half_lt_self hmin).trans_le
    (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
  have hηe (j : Fin (N + 1)) : η < e j := (half_lt_self hmin).trans_le
    (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, rfl⟩)))
  let J : ℝ × ℝ → Polygon E (n + 3) := fun z =>
    ⟨fun v => H z.2 v + ∑ j : Fin (N + 1), (D j z v - H z.2 v)⟩
  have hJat (s t : ℝ) (j : Fin (N + 1)) (ht : |t - τ j| < δ) :
      J (s, t) = D j (s, t) := by
    apply congrArg Polygon.mk
    funext v
    change H t v + ∑ k : Fin (N + 1), (D k (s, t) v - H t v) = _
    rw [Finset.sum_eq_single j]
    · abel
    · intro k _ hkj
      rw [hDfix k s t (hfar k j hkj t ht), sub_self]
    · simp
  have hJnone (s t : ℝ) (ht : ∀ j, δ ≤ |t - τ j|) : J (s, t) = H t := by
    apply congrArg Polygon.mk
    funext v
    change H t v + ∑ j : Fin (N + 1), (D j (s, t) v - H t v) = _
    have hz : ∑ j : Fin (N + 1), (D j (s, t) v - H t v) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hDfix j s t (ht j), sub_self])
    rw [hz, add_zero]
  have hJcases (s t : ℝ) : J (s, t) = H t ∨ ∃ j, J (s, t) = D j (s, t) := by
    by_cases ht : ∃ j, |t - τ j| < δ
    · obtain ⟨j, hj⟩ := ht
      exact Or.inr ⟨j, hJat s t j hj⟩
    · exact Or.inl (hJnone s t (fun j => le_of_not_gt (fun hj => ht ⟨j, hj⟩)))
  refine ⟨η, hη, hηδ, J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ((hH_smooth v).comp contDiff_snd).add (ContDiff.sum (fun j _ =>
      (hDs j v).sub ((hH_smooth v).comp contDiff_snd)))
  · intro s t
    rcases hJcases s t with hh | ⟨j, hh⟩
    · rw [hh]; exact hH_good t
    · rw [hh]; exact hDg j s t
  · intro s t hs
    rcases hJcases s t with hh | ⟨j, hh⟩
    · exact hh
    · exact hh.trans (hD0 j s t hs)
  · intro s t hs
    apply congrArg Polygon.mk
    funext v
    change H t v + ∑ j : Fin (N + 1), (D j (s, t) v - H t v) =
      H t v + ∑ j : Fin (N + 1), (D j (1, t) v - H t v)
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hD1 j s t hs]
  · intro s t ht
    rcases hJcases s t with hh | ⟨j, hh⟩
    · exact hh
    · exact hh.trans (hDtail j s t ht)
  · intro s t i ht
    rcases hJcases s t with hh | ⟨j, hh⟩
    · rw [hh]; exact hstraight i t ht
    · rw [hh]; exact hDstraight j s t i ht
  · intro j t ht
    have hecore := ht.trans (hηe j)
    rw [hJat 1 t j (hecore.trans_le (heδ j))]
    exact hDflat j t hecore

end PoincareConjecture.M25.Topology3D
