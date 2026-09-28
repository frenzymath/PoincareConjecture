import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcStraightWeight
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcDeformationLift

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

private theorem arcCell_center_indices {n : ℕ} (i : Fin (n + 1)) :
    i.castSucc.succ ≠ (0 : Fin (n + 3)) ∧
      i.castSucc.succ ≠ Fin.last (n + 2) ∧
      i.castSucc.succ.succAbove i.castSucc =
        (finRotate (n + 3)).symm i.castSucc.succ ∧
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

theorem exists_relative_polygonalArc_cell_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (ih : ∀ (q : ℝ → Polygon E (n + 2)),
      (∀ j, ContDiff ℝ ∞ (fun t => q t j)) →
      (∀ t, IsSimplePolygonalArc (q t) ∧ q t 0 = A ∧
        q t (Fin.last (n + 1)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
          X A < X (q t j) ∧ X (q t j) < X B) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      (∀ t, |t| < ε → ∀ j, q t j ∈ segment ℝ A B) →
      (∀ t, |t - 1| < ε → ∀ j, q t j ∈ segment ℝ A B) →
      ∃ ν : ℝ, 0 < ν ∧ ν < ε ∧ ∃ Q : ℝ × ℝ → Polygon E (n + 2),
        (∀ j, ContDiff ℝ ∞ (fun z => Q z j)) ∧
        (∀ s t, IsSimplePolygonalArc (Q (s, t)) ∧ Q (s, t) 0 = A ∧
          Q (s, t) (Fin.last (n + 1)) = B ∧
          ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
            X A < X (Q (s, t) j) ∧ X (Q (s, t) j) < X B) ∧
        (∀ s t, s ≤ 0 → Q (s, t) = q t) ∧
        (∀ s t, 1 ≤ s → Q (s, t) = Q (1, t)) ∧
        (∀ s t, t ≤ ν ∨ 1 - ν ≤ t → Q (s, t) = q t) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Q (1, t) j ∈ segment ℝ A B)
    (H : ℝ → Polygon E (n + 3)) (i : Fin (n + 1))
    (hH_smooth : ∀ j, ContDiff ℝ ∞ (fun t => H t j))
    (hH_good : ∀ t, IsSimplePolygonalArc (H t) ∧ H t 0 = A ∧
      H t (Fin.last (n + 2)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
        X A < X (H t j) ∧ X (H t j) < X B)
    {a b ρ κ : ℝ} (hab : a < b) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hstraight : ∀ t ∈ Ioo (a - ρ) (b + ρ),
      H t i.castSucc.succ ∈ segment ℝ
        (H t ((finRotate (n + 3)).symm i.castSucc.succ))
        (H t (finRotate (n + 3) i.castSucc.succ)))
    (hflat_a : ∀ t, |t - a| < κ → ∀ j, H t j ∈ segment ℝ A B)
    (hflat_b : ∀ t, |t - b| < κ → ∀ j, H t j ∈ segment ℝ A B) :
    ∃ σ : ℝ, 0 < σ ∧ σ < (b - a) / 4 ∧ ∃ R : ℝ × ℝ → Polygon E (n + 3),
      (∀ j, ContDiff ℝ ∞ (fun z => R z j)) ∧
      (∀ s t, IsSimplePolygonalArc (R (s, t)) ∧ R (s, t) 0 = A ∧
        R (s, t) (Fin.last (n + 2)) = B ∧
        ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
          X A < X (R (s, t) j) ∧ X (R (s, t) j) < X B) ∧
      (∀ s t, s ≤ 0 → R (s, t) = H t) ∧
      (∀ s t, 1 ≤ s → R (s, t) = R (1, t)) ∧
      (∀ s t, t ≤ a + σ ∨ b - σ ≤ t → R (s, t) = H t) ∧
      ∀ t ∈ Icc a b, ∀ j, R (1, t) j ∈ segment ℝ A B := by
  classical
  let h : ℝ := b - a
  have hh : 0 < h := sub_pos.mpr hab
  have hh0 : h ≠ 0 := ne_of_gt hh
  let k : Fin (n + 3) := i.castSucc.succ
  obtain ⟨hk0, hkl, hkleft, hkright⟩ := arcCell_center_indices i
  obtain ⟨θ, hθ, hθrange, hθid⟩ := exists_smooth_interval_clamp
    (a := a - ρ / 4) (b := b + ρ / 4) (d := ρ / 4)
    (by linarith) (by positivity)
  have hθstraight (t : ℝ) : H (θ t) k ∈
      segment ℝ (H (θ t) ((finRotate (n + 3)).symm k))
        (H (θ t) (finRotate (n + 3) k)) := by
    apply hstraight
    have ht := hθrange t
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let q : ℝ → Polygon E (n + 2) := fun u =>
    polygonArcDeleteVertex (H (θ (a + h * u))) k
  have hqs (j : Fin (n + 2)) : ContDiff ℝ ∞ (fun u => q u j) :=
    ((hH_smooth (k.succAbove j)).comp hθ).comp
      (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hqg (u : ℝ) : IsSimplePolygonalArc (q u) ∧ q u 0 = A ∧
      q u (Fin.last (n + 1)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
        X A < X (q u j) ∧ X (q u j) < X B := by
    obtain ⟨hp, hp0, hplast, hpX⟩ := hH_good (θ (a + h * u))
    have hend := polygonArcDeleteVertex_endpoints (H (θ (a + h * u))) k hk0 hkl
    refine ⟨hp.isSimple_polygonArcDeleteVertex k hk0 hkl (hθstraight _),
      hend.1.trans hp0, hend.2.trans hplast, ?_⟩
    intro j hj0 hjl
    exact hpX _ (Fin.succAbove_ne_zero hk0 hj0) (Fin.succAbove_ne_last hkl hjl)
  let ξ : ℝ := min (min ρ κ) h / 16
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξρ : ξ ≤ ρ / 16 := by
    dsimp [ξ]
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _))
      (by norm_num)
  have hξκ : ξ ≤ κ / 16 := by
    dsimp [ξ]
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _))
      (by norm_num)
  have hξh : ξ ≤ h / 16 := by
    dsimp [ξ]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let ε : ℝ := ξ / h
  have hε : 0 < ε := div_pos hξ hh
  have hεsmall : ε < 1 / 4 := by
    apply (div_lt_iff₀ hh).mpr
    linarith
  have hscale (u : ℝ) (hu : |u| < ε) : |h * u| < ξ := by
    rw [abs_mul, abs_of_pos hh]
    have hu' : |u| < ξ / h := hu
    have hb := (lt_div_iff₀ hh).mp hu'
    nlinarith
  have hqflat_a (u : ℝ) (hu : |u| < ε) : ∀ j, q u j ∈ segment ℝ A B := by
    have huξ := abs_lt.mp (hscale u hu)
    have hfix : θ (a + h * u) = a + h * u :=
      hθid _ ⟨by linarith [huξ.1], by linarith [huξ.2]⟩
    intro j
    change H (θ (a + h * u)) (k.succAbove j) ∈ segment ℝ A B
    rw [hfix]
    apply hflat_a
    rw [add_sub_cancel_left]
    exact lt_of_lt_of_le (hscale u hu) (by linarith)
  have hqflat_b (u : ℝ) (hu : |u - 1| < ε) : ∀ j, q u j ∈ segment ℝ A B := by
    have huξ := abs_lt.mp (hscale (u - 1) hu)
    have heq : a + h * u = b + h * (u - 1) := by dsimp [h]; ring
    have hfix : θ (a + h * u) = a + h * u := by
      apply hθid
      rw [heq]
      exact ⟨by linarith [huξ.1], by linarith [huξ.2]⟩
    intro j
    change H (θ (a + h * u)) (k.succAbove j) ∈ segment ℝ A B
    rw [hfix]
    apply hflat_b
    rw [heq, add_sub_cancel_left]
    exact lt_of_lt_of_le (hscale (u - 1) hu) (by linarith)
  obtain ⟨ν, hν, hνε, Q0, hQ0s, hQ0g, hQ0zero, hQ0one, hQ0fix, hQ0flat⟩ :=
    ih q hqs hqg ε hε hεsmall hqflat_a hqflat_b
  have hνone : ν < 1 := by linarith
  have hνprod : 0 < h * ν := mul_pos hh hν
  let Q : ℝ × ℝ → Polygon E (n + 2) := fun z => Q0 (z.1, (z.2 - a) / h)
  have hQs (j : Fin (n + 2)) : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Q z j) :=
    (hQ0s j).comp
      (contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const h))
  have hQg (s t : ℝ) : IsSimplePolygonalArc (Q (s, t)) ∧ Q (s, t) 0 = A ∧
      Q (s, t) (Fin.last (n + 1)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
        X A < X (Q (s, t) j) ∧ X (Q (s, t) j) < X B := hQ0g _ _
  have hunscale (t : ℝ) : a + h * ((t - a) / h) = t := by
    field_simp
    ring
  let K : Set ℝ := Icc (a + h * ν / 2) (b - h * ν / 2)
  let U : Set ℝ := Ioo (a - ρ / 4) (b + ρ / 4)
  have hKU : K ⊆ U := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hQzero (s t : ℝ) (hs : s ≤ 0) : Q (s, t) = Q (0, t) := by
    exact (hQ0zero s _ hs).trans (hQ0zero 0 _ le_rfl).symm
  have hQone (s t : ℝ) (hs : 1 ≤ s) : Q (s, t) = Q (1, t) := hQ0one s _ hs
  have hQfix (s t : ℝ) (ht : t ∉ K) : Q (s, t) = Q (0, t) := by
    have htail : (t - a) / h ≤ ν ∨ 1 - ν ≤ (t - a) / h := by
      by_cases hleft : t < a + h * ν / 2
      · left
        apply (div_le_iff₀ hh).mpr
        nlinarith
      · have hright : b - h * ν / 2 < t := by
          by_contra hn
          exact ht ⟨le_of_not_gt hleft, le_of_not_gt hn⟩
        right
        apply (le_div_iff₀ hh).mpr
        dsimp [h] at *
        nlinarith
    exact (hQ0fix s _ htail).trans (hQ0zero 0 _ le_rfl).symm
  have hQdelete (t : ℝ) (ht : t ∈ U) :
      Q (0, t) = polygonArcDeleteVertex (H t) k := by
    change Q0 (0, (t - a) / h) = _
    rw [hQ0zero 0 _ le_rfl]
    change polygonArcDeleteVertex (H (θ (a + h * ((t - a) / h)))) k = _
    rw [hunscale, hθid t ⟨ht.1.le, ht.2.le⟩]
  obtain ⟨w, hws, hw, hwrecover⟩ := exists_polygonalArc_straight_weight H i hH_smooth
    (a := a - ρ / 4) (b := b + ρ / 4) (d := ρ / 4)
    (by linarith) (by positivity) (fun t _ => (hH_good t).1)
    (fun t ht => by
      rw [hkleft, hkright]
      exact hstraight t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  obtain ⟨R, hRin, _, hRs, hRg, hRzero, hRone, hRfix, _, _⟩ :=
    exists_relative_polygonalArc_lift A B X hAB i H Q w
      (K := K) (U := U) isClosed_Icc isOpen_Ioo hKU hH_smooth hH_good
      hQs hQg hws hw hQzero hQone hQfix hQdelete
      (fun t ht => hwrecover t ⟨ht.1.le, ht.2.le⟩)
  refine ⟨h * ν / 4, by positivity, ?_, R, hRs, hRg, hRzero, hRone, ?_, ?_⟩
  · change h * ν / 4 < h / 4
    nlinarith
  · intro s t ht
    apply hRfix
    intro hmem
    rcases ht with ht | ht
    · linarith [hmem.1]
    · linarith [hmem.2]
  · intro t ht
    have htU : t ∈ U := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht01 : (t - a) / h ∈ Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (sub_nonneg.mpr ht.1) hh.le, ?_⟩
      apply (div_le_one hh).mpr
      dsimp [h]
      linarith [ht.2]
    rw [hRin 1 t htU]
    obtain ⟨hc, hr, _, _, _⟩ := polygonArcInsertVertex_spec (Q (1, t)) i (w t)
    intro j
    rcases Fin.eq_self_or_eq_succAbove i.castSucc.succ j with rfl | ⟨j, rfl⟩
    · rw [hc]
      exact (convex_segment (𝕜 := ℝ) A B).lineMap_mem
        (hQ0flat _ ht01 i.castSucc) (hQ0flat _ ht01 i.succ) ⟨(hw t).1.le, (hw t).2.le⟩
    · rw [hr]
      exact hQ0flat _ ht01 j

end PoincareConjecture.M25.Topology3D
