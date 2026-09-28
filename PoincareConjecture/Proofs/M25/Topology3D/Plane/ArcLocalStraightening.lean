import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcLocalPush
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcDeformationLift
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcAdmissible
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPersistence










set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_local_polygonalArc_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {n : ℕ}
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (p : ℝ → Polygon E (n + 2))
    (hp_smooth : ∀ j, ContDiff ℝ ∞ (fun t => p t j))
    (hp_good : ∀ t, IsSimplePolygonalArc (p t) ∧ p t 0 = A ∧
      p t (Fin.last (n + 1)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
        X A < X (p t j) ∧ X (p t j) < X B)
    (t0 : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ F : ℝ × ℝ → Polygon E (n + 2),
      (∀ j, ContDiff ℝ ∞ (fun z : ℝ × ℝ => F z j)) ∧
      (∀ s t, IsSimplePolygonalArc (F (s, t)) ∧ F (s, t) 0 = A ∧
        F (s, t) (Fin.last (n + 1)) = B ∧
        ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
          X A < X (F (s, t) j) ∧ X (F (s, t) j) < X B) ∧
      (∀ s t, s ≤ 0 → F (s, t) = p t) ∧
      (∀ s t, 1 ≤ s → F (s, t) = F (1, t)) ∧
      (∀ s t, δ ≤ |t - t0| → F (s, t) = p t) ∧
      ∀ t, |t - t0| < ε → ∀ j, F (1, t) j ∈ segment ℝ A B := by
  classical
  induction n generalizing t0 δ with
  | zero =>
    refine ⟨δ / 2, half_pos hδ, half_lt_self hδ, fun z => p z.2,
      (fun j => (hp_smooth j).comp contDiff_snd), (fun _ t => hp_good t),
      (fun _ _ _ => rfl), (fun _ _ _ => rfl), (fun _ _ _ => rfl), ?_⟩
    intro t _ j
    fin_cases j
    · change p t 0 ∈ segment ℝ A B
      rw [(hp_good t).2.1]
      exact left_mem_segment ℝ A B
    · change p t (Fin.last 1) ∈ segment ℝ A B
      rw [(hp_good t).2.2.1]
      exact right_mem_segment ℝ A B
  | succ n ih =>
    have hp0 := hp_good t0
    let u : Fin (n + 3) := ⟨1, by omega⟩
    have hu0 : u ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      change 1 = 0 at hv
      omega
    have hul : u ≠ Fin.last (n + 2) := by
      intro h
      have hv := congrArg Fin.val h
      change 1 = n + 2 at hv
      omega
    have hex : ∃ k, IsAdmissibleArcVertex (p t0) k := by
      by_cases had : IsAdmissibleArcVertex (p t0) u
      · exact ⟨u, had⟩
      · obtain ⟨k, hk, _, _⟩ := hp0.1.exists_admissible_away_neighbors hdim X
          (by rw [hp0.2.1, hp0.2.2.1]; exact hAB)
          (by rw [hp0.2.1, hp0.2.2.1]; exact hp0.2.2.2) u hu0 hul had
        exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    have hkpos : 0 < k.val := by
      apply Nat.pos_of_ne_zero
      intro hn
      exact hk.1 (Fin.ext (by simpa only [Fin.val_zero] using hn))
    have hklt : k.val < n + 2 := Fin.lt_last_iff_ne_last.mpr hk.2.1
    let i : Fin (n + 1) := ⟨k.val - 1, by omega⟩
    have hik : i.castSucc.succ = k := by
      apply Fin.ext
      change k.val - 1 + 1 = k.val
      omega
    have hpersist := hp0.1.eventually_isAdmissibleArcVertex k hk
      (fun j => (hp_smooth j).continuous.continuousAt)
    obtain ⟨μ, hμ, hμad⟩ := Metric.eventually_nhds_iff.mp hpersist
    let d : ℝ := min δ μ / 8
    have hd : 0 < d := div_pos (lt_min hδ hμ) (by norm_num)
    have hdδ : 4 * d < δ := by
      have hh : 8 * d ≤ δ := by dsimp [d]; linarith [min_le_left δ μ]
      linarith
    have hdμ : 4 * d < μ := by
      have hh : 8 * d ≤ μ := by dsimp [d]; linarith [min_le_right δ μ]
      linarith
    have had (t : ℝ) (ht : t ∈ Ioo (t0 - 2 * d - 2 * d) (t0 + 2 * d + 2 * d)) :
        IsAdmissibleArcVertex (p t) i.castSucc.succ := by
      rw [hik]
      apply hμad
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨χ, θ, _, _, _, _, _hθ, _, hθid, hPs, hPg, hPzero, hPone,
      _, _, _, hqs, hqg, hrecover⟩ :=
      exists_supported_polygonalArc_push A B X hAB p i hp_smooth hp_good
        (a := t0 - 2 * d) (b := t0 + 2 * d) (by linarith) hd had
    let P : ℝ × ℝ → Polygon E (n + 3) := fun z => polygonPushVertex (p z.2)
      i.castSucc.succ (Real.smoothTransition z.1 * χ z.2)
    let H : ℝ → Polygon E (n + 3) := fun t => P (1, t)
    let q : ℝ → Polygon E (n + 2) := fun t =>
      polygonArcDeleteVertex (H (θ t)) i.castSucc.succ
    change ∀ j, ContDiff ℝ ∞ (fun z : ℝ × ℝ => P z j) at hPs
    change ∀ s t, 1 ≤ s → P (s, t) = H t at hPone
    change ∀ t, polygonArcBoundary (q t) = polygonArcBoundary (H (θ t)) ∧
      polygonArcInsertVertex (q t) i (1 / 2) = H (θ t) at hrecover
    have hHs (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun t => H t j) :=
      (hPs j).comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨ε, hε, hεd, Q, hQs, hQg, hQzero, hQone, hQfix, hQflat⟩ :=
      ih q hqs hqg t0 hd
    let K : Set ℝ := Icc (t0 - d) (t0 + d)
    let U : Set ℝ := Ioo (t0 - 2 * d) (t0 + 2 * d)
    have hKU : K ⊆ U := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hθU (t : ℝ) (ht : t ∈ U) : θ t = t := hθid t ⟨ht.1.le, ht.2.le⟩
    have hqdelete (t : ℝ) (ht : t ∈ U) :
        q t = polygonArcDeleteVertex (H t) i.castSucc.succ := by
      dsimp only [q]
      rw [hθU t ht]
    have hweight (t : ℝ) (ht : t ∈ U) : H t i.castSucc.succ =
        AffineMap.lineMap (H t (i.castSucc.succ.succAbove i.castSucc))
          (H t (i.castSucc.succ.succAbove i.succ)) (1 / 2 : ℝ) := by
      have heq : polygonArcInsertVertex (q t) i (1 / 2) = H t := by
        simpa only [hθU t ht] using (hrecover t).2
      obtain ⟨hc, hr, _, _, _⟩ := polygonArcInsertVertex_spec (q t) i (1 / 2)
      rw [heq] at hc hr
      rw [hr, hr]
      exact hc
    have hQoutside (s t : ℝ) (ht : t ∉ K) : Q (s, t) = Q (0, t) := by
      have hfar : d ≤ |t - t0| := by
        by_contra hn
        have hh := abs_lt.mp (lt_of_not_ge hn)
        exact ht ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [hQfix s t hfar, hQzero 0 t le_rfl]
    obtain ⟨R, hRin, _, hRs, hRg, hRzero, hRone, hRfix, _, _⟩ :=
      exists_relative_polygonalArc_lift A B X hAB i H Q (fun _ => (1 / 2 : ℝ))
        (K := K) (U := U) isClosed_Icc isOpen_Ioo hKU hHs (fun t => hPg 1 t)
        hQs hQg contDiff_const (fun _ => by norm_num)
        (fun s t hs => (hQzero s t hs).trans (hQzero 0 t le_rfl).symm)
        hQone hQoutside
        (fun t ht => (hQzero 0 t le_rfl).trans (hqdelete t ht)) hweight
    have hRflat (t : ℝ) (ht : |t - t0| < ε) :
        ∀ j, R (1, t) j ∈ segment ℝ A B := by
      have hU : t ∈ U := by
        have hh := abs_lt.mp ht
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [hRin 1 t hU]
      obtain ⟨hc, hr, _, _, _⟩ := polygonArcInsertVertex_spec (Q (1, t)) i (1 / 2)
      intro j
      rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ j with rfl | ⟨j, rfl⟩
      · rw [hc]
        exact (convex_segment (𝕜 := ℝ) A B).lineMap_mem
          (hQflat t ht i.castSucc) (hQflat t ht i.succ) (by norm_num)
      · rw [hr]
        exact hQflat t ht j
    let F : ℝ × ℝ → Polygon E (n + 3) := fun z =>
      ⟨fun j => P (3 * z.1, z.2) j + R (3 * z.1 - 2, z.2) j - H z.2 j⟩
    have hleft (s t : ℝ) (hs : s ≤ 2 / 3) : F (s, t) = P (3 * s, t) := by
      apply congrArg Polygon.mk
      funext j
      change P (3 * s, t) j + R (3 * s - 2, t) j - H t j = P (3 * s, t) j
      rw [hRzero (3 * s - 2) t (by linarith), add_sub_cancel_right]
    have hright (s t : ℝ) (hs : 1 / 3 ≤ s) : F (s, t) = R (3 * s - 2, t) := by
      apply congrArg Polygon.mk
      funext j
      change P (3 * s, t) j + R (3 * s - 2, t) j - H t j = R (3 * s - 2, t) j
      rw [hPone (3 * s) t (by linarith)]
      abel
    have hFone (t : ℝ) : F (1, t) = R (1, t) := by
      simpa only [mul_one, show (3 : ℝ) - 2 = 1 by norm_num] using
        hright 1 t (by norm_num)
    have hPfar (s t : ℝ) (ht : δ ≤ |t - t0|) : P (s, t) = p t := by
      apply hPzero
      right
      by_cases ht0 : t ≤ t0
      · left
        rw [abs_of_nonpos (sub_nonpos.mpr ht0)] at ht
        linarith
      · right
        rw [abs_of_nonneg (sub_nonneg.mpr (lt_of_not_ge ht0).le)] at ht
        linarith
    refine ⟨ε, hε, by linarith, F, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      exact ((hPs j).comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)).add
        ((hRs j).comp (((contDiff_const.mul contDiff_fst).sub contDiff_const).prodMk
          contDiff_snd)) |>.sub ((hHs j).comp contDiff_snd)
    · intro s t
      by_cases hs : s ≤ 2 / 3
      · rw [hleft s t hs]
        exact hPg (3 * s) t
      · rw [hright s t (by linarith)]
        exact hRg (3 * s - 2) t
    · intro s t hs
      rw [hleft s t (by linarith)]
      exact hPzero (3 * s) t (Or.inl (by linarith))
    · intro s t hs
      rw [hright s t (by linarith), hRone (3 * s - 2) t (by linarith), hFone]
    · intro s t ht
      have htK : t ∉ K := by
        intro hm
        have hh : |t - t0| ≤ d := abs_le.mpr
          ⟨by linarith [hm.1], by linarith [hm.2]⟩
        linarith
      by_cases hs : s ≤ 2 / 3
      · rw [hleft s t hs, hPfar (3 * s) t ht]
      · rw [hright s t (by linarith), hRfix (3 * s - 2) t htK]
        exact hPfar 1 t ht
    · intro t ht
      rw [hFone]
      exact hRflat t ht

end PoincareConjecture.M25.Topology3D
