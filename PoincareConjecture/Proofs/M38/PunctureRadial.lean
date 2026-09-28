import PoincareConjecture.Proofs.M38.RadialCoordinates
import Mathlib.Algebra.Order.GroupWithZero.OrderIso

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M38

noncomputable def punctureRadialOrderIso : ℝ ≃o ℝ :=
  (OrderIso.subRight (1 / 2 : ℝ)).trans
    ((OrderIso.divRight₀ 2 (by norm_num)).trans
      ((capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).trans
        ((OrderIso.mulLeft₀ 2 (by norm_num)).trans (OrderIso.subRight (1 / 2)))))

theorem punctureRadialOrderIso_apply (t : ℝ) :
    punctureRadialOrderIso t =
      2 * capRadialProfile (3 / 2) 1 ((t - 1 / 2) / 2) - 1 / 2 := rfl

theorem punctureRadialOrderIso_symm_apply (t : ℝ) :
    punctureRadialOrderIso.symm t =
      2 * (capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).symm
        ((t + 1 / 2) / 2) + 1 / 2 := by
  apply punctureRadialOrderIso.injective
  rw [OrderIso.apply_symm_apply, punctureRadialOrderIso_apply]
  have harg : (2 * (capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).symm
      ((t + 1 / 2) / 2) + 1 / 2 - 1 / 2) / 2 =
      (capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).symm
        ((t + 1 / 2) / 2) := by ring
  rw [harg, ← capRadialOrderIso_apply (3 / 2) 1 (by norm_num) (by norm_num),
    OrderIso.apply_symm_apply]
  ring

theorem punctureRadialOrderIso_smooth : ContDiff ℝ ∞ punctureRadialOrderIso := by
  change ContDiff ℝ ∞ (fun t : ℝ =>
    2 * capRadialProfile (3 / 2) 1 ((t - 1 / 2) / 2) - 1 / 2)
  exact (contDiff_const.mul ((capRadialProfile_smooth (3 / 2) 1).comp
    ((contDiff_id.sub contDiff_const).div_const 2))).sub contDiff_const

theorem punctureRadialOrderIso_symm_smooth :
    ContDiff ℝ ∞ punctureRadialOrderIso.symm := by
  simp_rw [show (punctureRadialOrderIso.symm : ℝ → ℝ) =
    (fun t : ℝ => 2 * (capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).symm
      ((t + 1 / 2) / 2) + 1 / 2) from funext punctureRadialOrderIso_symm_apply]
  exact (contDiff_const.mul ((capRadialOrderIso_symm_smooth
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2)).comp
    ((contDiff_id.add contDiff_const).div_const 2))).add contDiff_const

theorem punctureRadialOrderIso_sub_one (t : ℝ) (ht : t ≤ 1) :
    punctureRadialOrderIso t = t - 1 := by
  rw [punctureRadialOrderIso_apply,
    capRadialProfile_linear (3 / 2) 1 _ (by linarith)]
  ring

@[simp] theorem punctureRadialOrderIso_one : punctureRadialOrderIso 1 = 0 := by
  rw [punctureRadialOrderIso_sub_one 1 le_rfl]
  norm_num

theorem punctureRadialOrderIso_eq_self (t : ℝ) (ht : 3 / 2 ≤ t) :
    punctureRadialOrderIso t = t := by
  rw [punctureRadialOrderIso_apply,
    capRadialProfile_affine (3 / 2) 1 _ (by linarith)]
  ring

theorem punctureRadialOrderIso_symm_eq_self (t : ℝ) (ht : 3 / 2 ≤ t) :
    punctureRadialOrderIso.symm t = t := by
  apply punctureRadialOrderIso.injective
  rw [OrderIso.apply_symm_apply, punctureRadialOrderIso_eq_self t ht]

theorem punctureRadialOrderIso_pos_iff (t : ℝ) :
    0 < punctureRadialOrderIso t ↔ 1 < t := by
  rw [← punctureRadialOrderIso_one, punctureRadialOrderIso.lt_iff_lt]

theorem punctureRadialOrderIso_symm_gt_one {t : ℝ} (ht : 0 < t) :
    1 < punctureRadialOrderIso.symm t := by
  apply (punctureRadialOrderIso_pos_iff _).mp
  rwa [OrderIso.apply_symm_apply]

theorem capRadialMap_norm_of_pos (f : ℝ → ℝ) (x : StandardCapSpace)
    (hx : 0 < ‖x‖) (hf : 0 < f ‖x‖) : ‖capRadialMap f x‖ = f ‖x‖ := by
  rw [capRadialMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hf hx), div_mul_cancel₀ _ hx.ne']

theorem capRadialMap_contDiffAt_of_ne (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : StandardCapSpace) (hx : x ≠ 0) : ContDiffAt ℝ ∞ (capRadialMap f) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x := contDiffAt_norm ℝ hx
  exact ((hf.contDiffAt.comp x hn).div hn (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem capRadialMap_inverse_of_pos (e : ℝ ≃o ℝ) (x : StandardCapSpace)
    (hx : 0 < ‖x‖) (he : 0 < e ‖x‖) :
    capRadialMap e.symm (capRadialMap e x) = x := by
  rw [capRadialMap, capRadialMap_norm_of_pos e x hx he, OrderIso.symm_apply_apply,
    capRadialMap, smul_smul]
  have hscalar : (‖x‖ / e ‖x‖) * (e ‖x‖ / ‖x‖) = 1 := by
    field_simp [he.ne', hx.ne']
  rw [hscalar, one_smul]

noncomputable def punctureCollapse : StandardCapSpace → StandardCapSpace :=
  capRadialMap punctureRadialOrderIso

noncomputable def punctureExpand : StandardCapSpace → StandardCapSpace :=
  capRadialMap punctureRadialOrderIso.symm

theorem punctureCollapse_norm {x : StandardCapSpace} (hx : 1 < ‖x‖) :
    ‖punctureCollapse x‖ = punctureRadialOrderIso ‖x‖ :=
  capRadialMap_norm_of_pos _ _ (by linarith) ((punctureRadialOrderIso_pos_iff _).mpr hx)

theorem punctureExpand_norm {x : StandardCapSpace} (hx : 0 < ‖x‖) :
    ‖punctureExpand x‖ = punctureRadialOrderIso.symm ‖x‖ :=
  capRadialMap_norm_of_pos _ _ hx (by
    have := punctureRadialOrderIso_symm_gt_one hx
    linarith)

theorem punctureExpand_collapse {x : StandardCapSpace} (hx : 1 < ‖x‖) :
    punctureExpand (punctureCollapse x) = x :=
  capRadialMap_inverse_of_pos _ _ (by linarith) ((punctureRadialOrderIso_pos_iff _).mpr hx)

theorem punctureCollapse_expand {x : StandardCapSpace} (hx : 0 < ‖x‖) :
    punctureCollapse (punctureExpand x) = x :=
  capRadialMap_inverse_of_pos punctureRadialOrderIso.symm _ hx (by
    have := punctureRadialOrderIso_symm_gt_one hx
    linarith)

theorem punctureCollapse_smooth :
    ContDiffOn ℝ ∞ punctureCollapse {x | 1 < ‖x‖} := by
  intro x hx
  exact (capRadialMap_contDiffAt_of_ne _ punctureRadialOrderIso_smooth x
    (norm_pos_iff.mp (by change 1 < ‖x‖ at hx; linarith))).contDiffWithinAt

theorem punctureExpand_smooth : ContDiffOn ℝ ∞ punctureExpand {x | 0 < ‖x‖} := by
  intro x hx
  exact (capRadialMap_contDiffAt_of_ne _ punctureRadialOrderIso_symm_smooth x
    (norm_pos_iff.mp hx)).contDiffWithinAt

theorem punctureCollapse_eq_self {x : StandardCapSpace} (hx : 3 / 2 ≤ ‖x‖) :
    punctureCollapse x = x := by
  simpa only [one_smul, punctureCollapse] using capRadialMap_eq_smul punctureRadialOrderIso 1 x
    (by simpa only [one_mul] using punctureRadialOrderIso_eq_self ‖x‖ hx)

theorem punctureExpand_eq_self {x : StandardCapSpace} (hx : 3 / 2 ≤ ‖x‖) :
    punctureExpand x = x := by
  simpa only [one_smul, punctureExpand] using capRadialMap_eq_smul punctureRadialOrderIso.symm 1 x
    (by simpa only [one_mul] using punctureRadialOrderIso_symm_eq_self ‖x‖ hx)

end PoincareConjecture.M38
