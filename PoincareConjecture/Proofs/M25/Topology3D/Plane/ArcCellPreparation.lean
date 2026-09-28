import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcAdmissible
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPersistence
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCompatibleWindows
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPushNonadjacent
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcLocalPush

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem preparation_neighbors {n : ℕ} (i : Fin (n + 1)) :
    (finRotate (n + 3)).symm i.castSucc.succ = i.castSucc.castSucc ∧
      finRotate (n + 3) i.castSucc.succ = i.succ.succ := by
  constructor
  · apply (finRotate (n + 3)).injective
    rw [Equiv.apply_symm_apply]
    exact (finRotate_of_lt i.castSucc.isLt).symm
  · have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    rw [hi]
    exact finRotate_of_lt i.succ.isLt

private theorem preparation_flat_straight {n : ℕ} {p : Polygon E (n + 3)}
    (hp : IsSimplePolygonalArc p) (A B : E)
    (hf : ∀ v, p v ∈ segment ℝ A B) (i : Fin (n + 1)) :
    p i.castSucc.succ ∈ segment ℝ
      (p ((finRotate (n + 3)).symm i.castSucc.succ))
      (p (finRotate (n + 3) i.castSucc.succ)) := by
  obtain ⟨hpred, hsucc⟩ := preparation_neighbors i
  rw [hpred, hsucc]
  simp only [segment_eq_image_lineMap ℝ] at hf
  obtain ⟨a, _, ha⟩ := hf i.castSucc.castSucc
  obtain ⟨b, _, hb⟩ := hf i.castSucc.succ
  obtain ⟨c, _, hc⟩ := hf i.succ.succ
  have hcases : b ∈ segment ℝ a c ∨ a ∈ segment ℝ b c ∨ c ∈ segment ℝ a b := by
    simp only [segment_eq_Icc', mem_Icc]
    rcases le_total a b with hab | hba <;>
      rcases le_total b c with hbc | hcb <;>
      rcases le_total a c with hac | hca <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, *]
    all_goals first | tauto | exact Or.inl ⟨by linarith, by linarith⟩
  have himage (x y z : ℝ) (hz : z ∈ segment ℝ x y) :
      AffineMap.lineMap A B z ∈ segment ℝ
        (AffineMap.lineMap A B x) (AffineMap.lineMap A B y) := by
    rw [← image_segment]
    exact mem_image_of_mem _ hz
  rcases hcases with h | h | h
  · simpa only [ha, hb, hc] using himage a c b h
  · have he : p i.castSucc.castSucc ∈ p.edgeSet ℝ i.succ.castSucc := by
      rw [polygon_arcEdge_eq_segment]
      have hmid : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hmid]
      simpa only [ha, hb, hc] using himage b c a h
    rcases (hp.vertex_mem_edgeSet_iff _ _).mp he with h | h <;>
      have hv := congrArg Fin.val h <;>
      simp only [Fin.val_castSucc, Fin.val_succ] at hv <;> omega
  · have he : p i.succ.succ ∈ p.edgeSet ℝ i.castSucc.castSucc := by
      rw [polygon_arcEdge_eq_segment]
      simpa only [ha, hb, hc] using himage a b c h
    rcases (hp.vertex_mem_edgeSet_iff _ _).mp he with h | h <;>
      have hv := congrArg Fin.val h <;>
      simp only [Fin.val_castSucc, Fin.val_succ] at hv <;> omega

private theorem preparation_push_flat {n : ℕ} (p : Polygon E (n + 3))
    (A B : E) (hf : ∀ v, p v ∈ segment ℝ A B) (k : Fin (n + 3))
    {u : ℝ} (hu : u ∈ Icc 0 1) :
    ∀ v, polygonPushVertex p k u v ∈ segment ℝ A B := by
  intro v
  by_cases hv : v = k
  · subst v
    rw [polygonPushVertex, polygonReplaceVertex_apply_same]
    exact (convex_segment A B).lineMap_mem (hf k)
      ((convex_segment A B).midpoint_mem (hf _) (hf _)) hu
  · simpa only [polygonPushVertex, polygonReplaceVertex_apply_of_ne _ _ _ hv] using hf v

private theorem preparation_push_straight {n : ℕ} (p : Polygon E (n + 3))
    (i j : Fin (n + 1))
    (hc : i.castSucc.succ = j.castSucc.succ ∨
      (j.castSucc.succ ≠ i.castSucc.succ ∧
        j.castSucc.succ ≠ (finRotate (n + 3)).symm i.castSucc.succ ∧
        j.castSucc.succ ≠ finRotate (n + 3) i.castSucc.succ))
    (hs : p i.castSucc.succ ∈ segment ℝ
      (p ((finRotate (n + 3)).symm i.castSucc.succ))
      (p (finRotate (n + 3) i.castSucc.succ)))
    {u : ℝ} (hu : u ∈ Icc 0 1) :
    polygonPushVertex p j.castSucc.succ u i.castSucc.succ ∈ segment ℝ
      (polygonPushVertex p j.castSucc.succ u
        ((finRotate (n + 3)).symm i.castSucc.succ))
      (polygonPushVertex p j.castSucc.succ u
        (finRotate (n + 3) i.castSucc.succ)) := by
  rcases hc with heq | ⟨hne, hp, hn⟩
  · rw [← heq]
    obtain ⟨hpred, hsucc⟩ := preparation_neighbors i
    have hp : (finRotate (n + 3)).symm i.castSucc.succ ≠ i.castSucc.succ := by
      rw [hpred]
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    have hn : finRotate (n + 3) i.castSucc.succ ≠ i.castSucc.succ := by
      rw [hsucc]
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    simp only [polygonPushVertex, polygonReplaceVertex_apply_of_ne _ _ _ hp,
      polygonReplaceVertex_apply_of_ne _ _ _ hn, polygonReplaceVertex_apply_same]
    exact (convex_segment _ _).lineMap_mem hs (midpoint_mem_segment _ _) hu
  · simpa only [polygonPushVertex, polygonReplaceVertex_apply_of_ne _ _ _ hne.symm,
      polygonReplaceVertex_apply_of_ne _ _ _ hp.symm,
      polygonReplaceVertex_apply_of_ne _ _ _ hn.symm] using hs

theorem exists_relative_polygonalArc_cell_preparation
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2) {n : ℕ}
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (p : ℝ → Polygon E (n + 3))
    (hp_smooth : ∀ v, ContDiff ℝ ∞ (fun t => p t v))
    (hp_good : ∀ t, IsSimplePolygonalArc (p t) ∧ p t 0 = A ∧
      p t (Fin.last (n + 2)) = B ∧ ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
        X A < X (p t v) ∧ X (p t v) < X B)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hflat : ∀ t, t ∈ Ioo (-ε) ε ∪ Ioo (1 - ε) (1 + ε) →
      ∀ v, p t v ∈ segment ℝ A B) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : Fin N → Fin (n + 1), ∃ ρ ν : ℝ,
      0 < ρ ∧ ρ < min (1 / (32 * (N : ℝ))) (ε / 8) ∧ 0 < ν ∧ ν < ε / 8 ∧
      (∀ i j : Fin N, i.val + 1 = j.val →
        (c i).castSucc.succ = (c j).castSucc.succ ∨
        ((c j).castSucc.succ ≠ (c i).castSucc.succ ∧
          (c j).castSucc.succ ≠ (finRotate (n + 3)).symm (c i).castSucc.succ ∧
          (c j).castSucc.succ ≠ finRotate (n + 3) (c i).castSucc.succ)) ∧
      ∃ F : ℝ × ℝ → Polygon E (n + 3),
        (∀ v, ContDiff ℝ ∞ (fun z => F z v)) ∧
        (∀ s t, IsSimplePolygonalArc (F (s, t)) ∧ F (s, t) 0 = A ∧
          F (s, t) (Fin.last (n + 2)) = B ∧
          ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
            X A < X (F (s, t) v) ∧ X (F (s, t) v) < X B) ∧
        (∀ s t, s ≤ 0 → F (s, t) = p t) ∧
        (∀ s t, 1 ≤ s → F (s, t) = F (1, t)) ∧
        (∀ s t, t ≤ ν ∨ 1 - ν ≤ t → F (s, t) = p t) ∧
        (∀ s t, t ∈ Ioo (-ε) ε ∪ Ioo (1 - ε) (1 + ε) →
          ∀ v, F (s, t) v ∈ segment ℝ A B) ∧
        ∀ i : Fin N, ∀ t ∈ Ioo ((i.val : ℝ) / N - ρ) (((i.val : ℝ) + 1) / N + ρ),
          F (1, t) (c i).castSucc.succ ∈ segment ℝ
            (F (1, t) ((finRotate (n + 3)).symm (c i).castSucc.succ))
            (F (1, t) (finRotate (n + 3) (c i).castSucc.succ)) := by
  classical
  let Good (q : Polygon E (n + 3)) : Prop := IsSimplePolygonalArc q ∧ q 0 = A ∧
    q (Fin.last (n + 2)) = B ∧ ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
      X A < X (q v) ∧ X (q v) < X B
  let Flat (q : Polygon E (n + 3)) : Prop := ∀ v, q v ∈ segment ℝ A B
  let Straight (q : Polygon E (n + 3)) (i : Fin (n + 1)) : Prop :=
    q i.castSucc.succ ∈ segment ℝ (q ((finRotate (n + 3)).symm i.castSucc.succ))
      (q (finRotate (n + 3) i.castSucc.succ))
  let R (i j : Fin (n + 1)) : Prop := i.castSucc.succ = j.castSucc.succ ∨
    (j.castSucc.succ ≠ i.castSucc.succ ∧
      j.castSucc.succ ≠ (finRotate (n + 3)).symm i.castSucc.succ ∧
      j.castSucc.succ ≠ finRotate (n + 3) i.castSucc.succ)
  let U (i : Fin (n + 1)) : Set ℝ := {t | IsAdmissibleArcVertex (p t) i.castSucc.succ}
  have hU (i : Fin (n + 1)) : IsOpen (U i) := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact (hp_good t).1.eventually_isAdmissibleArcVertex i.castSucc.succ ht
      (fun v => (hp_smooth v).continuous.continuousAt)
  have hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, ∃ j, R i j ∧ t ∈ U j := by
    intro t _ i
    by_cases hi : IsAdmissibleArcVertex (p t) i.castSucc.succ
    · exact ⟨i, Or.inl rfl, hi⟩
    · have hil : i.castSucc.succ ≠ Fin.last (n + 2) := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
        omega
      obtain ⟨k, hk, hkp, hkn⟩ := (hp_good t).1.exists_admissible_away_neighbors
        hdim X (by simpa only [(hp_good t).2.1, (hp_good t).2.2.1] using hAB)
        (by simpa only [(hp_good t).2.1, (hp_good t).2.2.1] using (hp_good t).2.2.2)
        i.castSucc.succ (Fin.succ_ne_zero _) hil hi
      have hk0 : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk.1
      have hkl : k.val < n + 2 := Fin.lt_last_iff_ne_last.mpr hk.2.1
      let j : Fin (n + 1) := ⟨k.val - 1, by omega⟩
      have hj : j.castSucc.succ = k := Fin.ext (by dsimp [j]; omega)
      refine ⟨j, Or.inr ?_, ?_⟩
      · rw [hj]
        exact ⟨fun hh => hi (hh ▸ hk), hkp, hkn⟩
      · change IsAdmissibleArcVertex (p t) j.castSucc.succ
        rwa [hj]
  obtain ⟨N, hN, c, hpad, hcompat⟩ := exists_compatible_padded_windows U R hU hcover
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let h : ℝ := 1 / N
  have hh : 0 < h := one_div_pos.mpr hNR
  let ρ : ℝ := min (h / 32) (ε / 8) / 2
  have hm : 0 < min (h / 32) (ε / 8) := lt_min (by positivity) (by positivity)
  have hρ : 0 < ρ := half_pos hm
  have hρh : ρ < h / 32 := (half_lt_self hm).trans_le (min_le_left _ _)
  have hρε : ρ < ε / 8 := (half_lt_self hm).trans_le (min_le_right _ _)
  let ν : ℝ := ε / 32
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνε : ν < ε / 8 := by dsimp [ν]; linarith
  have hνsmall : 2 * ν < ε := by dsimp [ν]; linarith
  obtain ⟨β, hβs, hβb, hβone, hβzero⟩ :=
    exists_smooth_interval_cutoff (2 * ν) (1 - 2 * ν) hν
  have hβtail (t : ℝ) (ht : t ≤ ν ∨ 1 - ν ≤ t) : β t = 0 := by
    apply hβzero t
    rcases ht with ht | ht
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  let a (i : Fin N) : ℝ := i.val / N
  let b (i : Fin N) : ℝ := (i.val + 1) / N
  let O (i : Fin N) := Ioo (a i - 4 * ρ) (b i + 4 * ρ)
  let W (i : Fin N) := Ioo (a i - ρ) (b i + ρ)
  let C := Ioo (-ε) ε ∪ Ioo (1 - ε) (1 + ε)
  have hab (i : Fin N) : a i < b i := by
    dsimp [a, b]
    exact (div_lt_div_iff_of_pos_right hNR).mpr (by linarith)
  have ha0 (i : Fin N) : 0 ≤ a i := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hb1 (i : Fin N) : b i ≤ 1 := by
    apply (div_le_one hNR).mpr
    exact_mod_cast i.isLt
  have hba (i : Fin N) : b i = a i + h := by dsimp [a, b, h]; ring
  have hsep (i j : Fin N) (hij : i.val + 2 ≤ j.val) : b i + 8 * ρ < a j := by
    have hv : (i.val : ℝ) + 2 ≤ j.val := by exact_mod_cast hij
    have hd := div_le_div_of_nonneg_right hv hNR.le
    have heq : ((i.val : ℝ) + 2) / N = b i + h := by dsimp [b, h]; ring
    rw [heq] at hd
    linarith
  have hOad (i : Fin N) (t : ℝ) (ht : t ∈ O i) :
      IsAdmissibleArcVertex (p t) (c i).castSucc.succ := by
    apply hpad i
    have hquarter : (1 : ℝ) / (4 * N) = h / 4 := by dsimp [h]; ring
    rw [hquarter]
    exact ⟨by dsimp [O, a] at ht; linarith [ht.1],
      by dsimp [O, b] at ht; linarith [ht.2]⟩
  have hWO (i : Fin N) : W i ⊆ O i :=
    fun _ ht => ⟨by dsimp [W, O] at *; linarith [ht.1],
      by dsimp [W, O] at *; linarith [ht.2]⟩
  have hWbounds (i : Fin N) (t : ℝ) (ht : t ∈ W i) : -ρ < t ∧ t < 1 + ρ :=
    ⟨by dsimp [W] at ht; linarith [ht.1, ha0 i],
      by dsimp [W] at ht; linarith [ht.2, hb1 i]⟩
  have hmaskflat (i : Fin N) (t : ℝ) (ht : t ∈ W i) (hβ : β t ≠ 1) : t ∈ C := by
    have hbnd := hWbounds i t ht
    by_cases ht0 : t < 2 * ν
    · exact Or.inl ⟨by linarith [hbnd.1], by linarith⟩
    · have ht1 : 1 - 2 * ν < t := by
        by_contra hh
        exact hβ (hβone t ⟨le_of_not_gt ht0, le_of_not_gt hh⟩)
      exact Or.inr ⟨by linarith, by linarith [hbnd.2]⟩
  have hind : ∀ m : ℕ, m ≤ N → ∃ F : ℝ × ℝ → Polygon E (n + 3),
      (∀ v, ContDiff ℝ ∞ (fun z => F z v)) ∧ (∀ s t, Good (F (s, t))) ∧
      (∀ s t, s ≤ 0 → F (s, t) = p t) ∧
      (∀ s t, 1 ≤ s → F (s, t) = F (1, t)) ∧
      (∀ s t, t ≤ ν ∨ 1 - ν ≤ t → F (s, t) = p t) ∧
      (∀ s t, t ∈ C → Flat (F (s, t))) ∧
      (∀ j : Fin N, j.val < m → ∀ t ∈ W j, Straight (F (1, t)) (c j)) ∧
      (∀ j : Fin N, m ≤ j.val → ∀ t ∈ O j,
        IsAdmissibleArcVertex (F (1, t)) (c j).castSucc.succ) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun z => p z.2, fun v => (hp_smooth v).comp contDiff_snd,
        fun _ t => hp_good t, fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun _ _ _ => rfl, fun _ t ht => hflat t ht,
        fun j hj => by omega, fun j _ t ht => hOad j t ht⟩
    | succ m ih =>
      intro hm
      obtain ⟨F, hFs, hFg, hF0, hF1, hFfix, hFflat, hFold, hFnext⟩ := ih (by omega)
      let i : Fin N := ⟨m, by omega⟩
      let H : ℝ → Polygon E (n + 3) := fun t => F (1, t)
      have hHs (v : Fin (n + 3)) : ContDiff ℝ ∞ (fun t => H t v) :=
        (hFs v).comp (contDiff_const.prodMk contDiff_id)
      obtain ⟨χ, θ, hχs, hχb, hχone, hχzero, _, _, _, hPs, hPg, hPfix,
        hP1, _, hPad, hPmid, _, _, _⟩ := exists_supported_polygonalArc_push
        A B X hAB H (c i) hHs (fun t => hFg 1 t) (hab i).le (show 0 < 2 * ρ by positivity)
        (fun t ht => hFnext i (by rfl) t
          ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      let P : ℝ × ℝ → Polygon E (n + 3) := fun z =>
        polygonPushVertex (H z.2) (c i).castSucc.succ (Real.smoothTransition z.1 * χ z.2)
      let D : ℝ × ℝ → Polygon E (n + 3) := fun z =>
        P (Real.smoothTransition z.1 * β z.2, z.2)
      have hDs (v : Fin (n + 3)) : ContDiff ℝ ∞ (fun z => D z v) :=
        (hPs v).comp (((Real.smoothTransition.contDiff.comp contDiff_fst).mul
          (hβs.comp contDiff_snd)).prodMk contDiff_snd)
      have hDg (s t : ℝ) : Good (D (s, t)) := hPg _ _
      have hD0 (s t : ℝ) (hs : s ≤ 0) : D (s, t) = H t := by
        apply hPfix
        left
        simp only [Real.smoothTransition.zero_of_nonpos hs, zero_mul, le_refl]
      have hD1 (s t : ℝ) (hs : 1 ≤ s) : D (s, t) = D (1, t) := by
        dsimp [D]
        rw [Real.smoothTransition.one_of_one_le hs, Real.smoothTransition.one]
      have hDout (s t : ℝ) (ht : t ∉ O i) : D (s, t) = H t := by
        apply hPfix
        right
        by_cases ht0 : t ≤ a i - 4 * ρ
        · exact Or.inl (by linarith)
        · right
          have ht1 : b i + 4 * ρ ≤ t := le_of_not_gt (fun hh => ht ⟨lt_of_not_ge ht0, hh⟩)
          linarith
      have hDtail (s t : ℝ) (ht : t ≤ ν ∨ 1 - ν ≤ t) : D (s, t) = H t := by
        apply hPfix
        left
        rw [hβtail t ht, mul_zero]
      have hcoef (s t : ℝ) : Real.smoothTransition (Real.smoothTransition s * β t) * χ t ∈
          Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (hχb t).1, ?_⟩
        nlinarith [Real.smoothTransition.le_one (Real.smoothTransition s * β t),
          Real.smoothTransition.nonneg (Real.smoothTransition s * β t),
          (hχb t).1, (hχb t).2]
      have hDflat (s t : ℝ) (ht : t ∈ C) : Flat (D (s, t)) :=
        preparation_push_flat (H t) A B (hFflat 1 t ht) _ (hcoef s t)
      have hDselected (t : ℝ) (ht : t ∈ W i) : Straight (D (1, t)) (c i) := by
        by_cases hb : β t = 1
        · have heq : D (1, t) = P (1, t) := by
            dsimp [D]
            rw [Real.smoothTransition.one, hb, one_mul]
          rw [heq]
          change P (1, t) (c i).castSucc.succ ∈ _
          rw [hPmid t ⟨by dsimp [W] at ht; linarith [ht.1],
            by dsimp [W] at ht; linarith [ht.2]⟩]
          exact midpoint_mem_segment _ _
        · exact preparation_flat_straight (hDg 1 t).1 A B
            (hDflat 1 t (hmaskflat i t ht hb)) (c i)
      have hDold (j : Fin N) (hj : j.val < m) (t : ℝ) (ht : t ∈ W j) :
          Straight (D (1, t)) (c j) := by
        by_cases hji : j.val + 1 = i.val
        · exact preparation_push_straight (H t) (c j) (c i) (hcompat j i hji)
            (hFold j hj t ht) (hcoef 1 t)
        · rw [hDout 1 t (by
            have hs := hsep j i (by dsimp [i] at hji ⊢; omega)
            intro hti
            dsimp [O, W] at ht hti
            linarith [ht.2, hti.1])]
          exact hFold j hj t ht
      have hDnext (j : Fin N) (hj : m + 1 ≤ j.val) (t : ℝ) (ht : t ∈ O j) :
          IsAdmissibleArcVertex (D (1, t)) (c j).castSucc.succ := by
        have hjad := hFnext j (by omega) t ht
        by_cases hti : t ∈ O i
        · have hji : i.val + 1 = j.val := by
            by_contra hh
            have hs := hsep i j (by dsimp [i] at *; omega)
            dsimp [O] at ht hti
            linarith [ht.1, hti.2]
          rcases hcompat i j hji with heq | ⟨hne, hp, hn⟩
          · rw [← heq] at hjad ⊢
            exact hPad _ t hjad
          · exact (hFg 1 t).1.isAdmissible_polygonPushVertex_of_nonadjacent hdim
              (c i).castSucc.succ (c j).castSucc.succ
              (hFnext i (by rfl) t hti) hjad hne hp hn (hcoef 1 t)
        · rw [hDout 1 t hti]
          exact hjad
      let G : ℝ × ℝ → Polygon E (n + 3) := fun z =>
        ⟨fun v => F (2 * z.1, z.2) v + D (2 * z.1 - 1, z.2) v - H z.2 v⟩
      have hGeq (s t : ℝ) : G (s, t) = F (2 * s, t) ∨ G (s, t) = D (2 * s - 1, t) := by
        by_cases hs : s ≤ 1 / 2
        · left
          apply congrArg Polygon.mk
          funext v
          change F (2 * s, t) v + D (2 * s - 1, t) v - H t v = _
          rw [hD0 _ t (by linarith)]
          exact add_sub_cancel_right _ _
        · right
          apply congrArg Polygon.mk
          funext v
          change F (2 * s, t) v + D (2 * s - 1, t) v - H t v = _
          rw [hF1 _ t (by linarith)]
          exact add_sub_cancel_left _ _
      have hG1 (t : ℝ) : G (1, t) = D (1, t) := by
        apply congrArg Polygon.mk
        funext v
        change F (2 * 1, t) v + D (2 * 1 - 1, t) v - H t v = _
        rw [hF1 _ t (by norm_num)]
        simp only [mul_one, show (2 : ℝ) - 1 = 1 by norm_num]
        exact add_sub_cancel_left _ _
      refine ⟨G, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v
        exact (((hFs v).comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)).add
          ((hDs v).comp (((contDiff_const.mul contDiff_fst).sub contDiff_const).prodMk
            contDiff_snd))).sub ((hHs v).comp contDiff_snd)
      · intro s t
        rcases hGeq s t with hh | hh
        · rw [hh]; exact hFg _ _
        · rw [hh]; exact hDg _ _
      · intro s t hs
        apply congrArg Polygon.mk
        funext v
        change F (2 * s, t) v + D (2 * s - 1, t) v - H t v = _
        rw [hF0 _ t (by linarith), hD0 _ t (by linarith)]
        exact add_sub_cancel_right _ _
      · intro s t hs
        rw [hG1]
        apply congrArg Polygon.mk
        funext v
        change F (2 * s, t) v + D (2 * s - 1, t) v - H t v = _
        rw [hF1 _ t (by linarith), hD1 _ t (by linarith)]
        exact add_sub_cancel_left _ _
      · intro s t ht
        rcases hGeq s t with hh | hh
        · rw [hh]; exact hFfix _ _ ht
        · rw [hh, hDtail _ _ ht]; exact hFfix _ _ ht
      · intro s t ht
        rcases hGeq s t with hh | hh
        · rw [hh]; exact hFflat _ _ ht
        · rw [hh]; exact hDflat _ _ ht
      · intro j hj t ht
        rw [hG1]
        by_cases hji : j = i
        · subst j; exact hDselected t ht
        · exact hDold j (by have hh : j.val ≠ m := fun hh => hji (Fin.ext hh); omega) t ht
      · intro j hj t ht
        rw [hG1]
        exact hDnext j hj t ht
  obtain ⟨F, hFs, hFg, hF0, hF1, hFfix, hFflat, hFstraight, _⟩ := hind N le_rfl
  refine ⟨N, hN, c, ρ, ν, hρ, ?_, hν, hνε, hcompat, F,
    hFs, hFg, hF0, hF1, hFfix, hFflat, ?_⟩
  · have heq : h / 32 = 1 / (32 * (N : ℝ)) := by dsimp [h]; ring
    exact lt_min (heq ▸ hρh) hρε
  · intro i t ht
    exact hFstraight i i.isLt t ht

end PoincareConjecture.M25.Topology3D
