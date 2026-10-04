import PoincareLib.Topology.Manifold.Surgery.Event.Radial.RadialCoordinates
import Mathlib.Algebra.Order.GroupWithZero.OrderIso

/-!
# Radial identification of a ball complement with a puncture

The increasing radius map sends one to zero and is the identity from radius
three halves onward. Its radial lift and inverse are smooth only on their
respective positive-radius domains. This permits local identity patching
inside a radius-two ball chart without asserting smoothness at the puncture.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareMT.M38

/-- A smooth radius change from the exterior unit interval to positive radii. -/
noncomputable def punctureRadialOrderIso : ℝ ≃o ℝ :=
  (OrderIso.subRight (1 / 2 : ℝ)).trans
    ((OrderIso.divRight₀ 2 (by norm_num)).trans
      ((capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).trans
        ((OrderIso.mulLeft₀ 2 (by norm_num)).trans (OrderIso.subRight (1 / 2)))))

/-- The forward order isomorphism uses the already verified smooth profile. -/
theorem punctureRadialOrderIso_apply (t : ℝ) :
    punctureRadialOrderIso t =
      2 * capRadialProfile (3 / 2) 1 ((t - 1 / 2) / 2) - 1 / 2 := rfl

/-- The inverse has the corresponding inverse-profile formula. -/
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

/-- The radius map is smooth as a function on the real line. -/
theorem punctureRadialOrderIso_smooth : ContDiff ℝ ∞ punctureRadialOrderIso := by
  change ContDiff ℝ ∞ (fun t : ℝ =>
    2 * capRadialProfile (3 / 2) 1 ((t - 1 / 2) / 2) - 1 / 2)
  exact (contDiff_const.mul ((capRadialProfile_smooth (3 / 2) 1).comp
    ((contDiff_id.sub contDiff_const).div_const 2))).sub contDiff_const

/-- The inverse radius map is smooth on the real line as well. -/
theorem punctureRadialOrderIso_symm_smooth :
    ContDiff ℝ ∞ punctureRadialOrderIso.symm := by
  simp_rw [show (punctureRadialOrderIso.symm : ℝ → ℝ) =
    (fun t : ℝ => 2 * (capRadialOrderIso (3 / 2) 1 (by norm_num) (by norm_num)).symm
      ((t + 1 / 2) / 2) + 1 / 2) from funext punctureRadialOrderIso_symm_apply]
  exact (contDiff_const.mul ((capRadialOrderIso_symm_smooth
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2)).comp
    ((contDiff_id.add contDiff_const).div_const 2))).add contDiff_const

/-- At and below the boundary the scalar formula is translation by minus one. -/
theorem punctureRadialOrderIso_sub_one (t : ℝ) (ht : t ≤ 1) :
    punctureRadialOrderIso t = t - 1 := by
  rw [punctureRadialOrderIso_apply,
    capRadialProfile_linear (3 / 2) 1 _ (by linarith)]
  ring

/-- The boundary radius is sent exactly to the omitted radius. -/
@[simp] theorem punctureRadialOrderIso_one : punctureRadialOrderIso 1 = 0 := by
  rw [punctureRadialOrderIso_sub_one 1 le_rfl]
  norm_num

/-- The radius change is the identity well inside the outer chart boundary. -/
theorem punctureRadialOrderIso_eq_self (t : ℝ) (ht : 3 / 2 ≤ t) :
    punctureRadialOrderIso t = t := by
  rw [punctureRadialOrderIso_apply,
    capRadialProfile_affine (3 / 2) 1 _ (by linarith)]
  ring

/-- The inverse fixes precisely the same outer radii. -/
theorem punctureRadialOrderIso_symm_eq_self (t : ℝ) (ht : 3 / 2 ≤ t) :
    punctureRadialOrderIso.symm t = t := by
  apply punctureRadialOrderIso.injective
  rw [OrderIso.apply_symm_apply, punctureRadialOrderIso_eq_self t ht]

/-- The scalar order equivalence sends exactly radii greater than one to positive radii. -/
theorem punctureRadialOrderIso_pos_iff (t : ℝ) :
    0 < punctureRadialOrderIso t ↔ 1 < t := by
  rw [← punctureRadialOrderIso_one, punctureRadialOrderIso.lt_iff_lt]

/-- Positive inverse input gives an exterior radius. -/
theorem punctureRadialOrderIso_symm_gt_one {t : ℝ} (ht : 0 < t) :
    1 < punctureRadialOrderIso.symm t := by
  apply (punctureRadialOrderIso_pos_iff _).mp
  rwa [OrderIso.apply_symm_apply]

/-- Away from zero the radial norm formula only needs positivity at that radius. -/
theorem capRadialMap_norm_of_pos (f : ℝ → ℝ) (x : StandardCapSpace)
    (hx : 0 < ‖x‖) (hf : 0 < f ‖x‖) : ‖capRadialMap f x‖ = f ‖x‖ := by
  rw [capRadialMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hf hx), div_mul_cancel₀ _ hx.ne']

/-- A smooth scalar function gives a smooth radial map at every nonzero point. -/
theorem capRadialMap_contDiffAt_of_ne (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : StandardCapSpace) (hx : x ≠ 0) : ContDiffAt ℝ ∞ (capRadialMap f) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x := contDiffAt_norm ℝ hx
  exact ((hf.contDiffAt.comp x hn).div hn (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

/-- A positive radius and its positive image suffice for the radial inverse law. -/
theorem capRadialMap_inverse_of_pos (e : ℝ ≃o ℝ) (x : StandardCapSpace)
    (hx : 0 < ‖x‖) (he : 0 < e ‖x‖) :
    capRadialMap e.symm (capRadialMap e x) = x := by
  rw [capRadialMap, capRadialMap_norm_of_pos e x hx he, OrderIso.symm_apply_apply,
    capRadialMap, smul_smul]
  have hscalar : (‖x‖ / e ‖x‖) * (e ‖x‖ / ‖x‖) = 1 := by
    field_simp [he.ne', hx.ne']
  rw [hscalar, one_smul]

/-- The radial collapse, used only outside the closed unit ball. -/
noncomputable def punctureCollapse : StandardCapSpace → StandardCapSpace :=
  capRadialMap punctureRadialOrderIso

/-- The radial expansion, used only off the origin. -/
noncomputable def punctureExpand : StandardCapSpace → StandardCapSpace :=
  capRadialMap punctureRadialOrderIso.symm

/-- The collapse has exactly the transformed positive radius on its domain. -/
theorem punctureCollapse_norm {x : StandardCapSpace} (hx : 1 < ‖x‖) :
    ‖punctureCollapse x‖ = punctureRadialOrderIso ‖x‖ :=
  capRadialMap_norm_of_pos _ _ (by linarith) ((punctureRadialOrderIso_pos_iff _).mpr hx)

/-- The expansion has exactly the transformed exterior radius on its domain. -/
theorem punctureExpand_norm {x : StandardCapSpace} (hx : 0 < ‖x‖) :
    ‖punctureExpand x‖ = punctureRadialOrderIso.symm ‖x‖ :=
  capRadialMap_norm_of_pos _ _ hx (by
    have := punctureRadialOrderIso_symm_gt_one hx
    linarith)

/-- Expansion undoes collapse at every exterior point. -/
theorem punctureExpand_collapse {x : StandardCapSpace} (hx : 1 < ‖x‖) :
    punctureExpand (punctureCollapse x) = x :=
  capRadialMap_inverse_of_pos _ _ (by linarith) ((punctureRadialOrderIso_pos_iff _).mpr hx)

/-- Collapse undoes expansion at every nonzero point. -/
theorem punctureCollapse_expand {x : StandardCapSpace} (hx : 0 < ‖x‖) :
    punctureCollapse (punctureExpand x) = x :=
  capRadialMap_inverse_of_pos punctureRadialOrderIso.symm _ hx (by
    have := punctureRadialOrderIso_symm_gt_one hx
    linarith)

/-- Collapse is smooth on the exterior of the closed unit ball. -/
theorem punctureCollapse_smooth :
    ContDiffOn ℝ ∞ punctureCollapse {x | 1 < ‖x‖} := by
  intro x hx
  exact (capRadialMap_contDiffAt_of_ne _ punctureRadialOrderIso_smooth x
    (norm_pos_iff.mp (by change 1 < ‖x‖ at hx; linarith))).contDiffWithinAt

/-- Expansion is smooth on punctured Euclidean space. -/
theorem punctureExpand_smooth : ContDiffOn ℝ ∞ punctureExpand {x | 0 < ‖x‖} := by
  intro x hx
  exact (capRadialMap_contDiffAt_of_ne _ punctureRadialOrderIso_symm_smooth x
    (norm_pos_iff.mp hx)).contDiffWithinAt

/-- The collapse changes no point at radius at least three halves. -/
theorem punctureCollapse_eq_self {x : StandardCapSpace} (hx : 3 / 2 ≤ ‖x‖) :
    punctureCollapse x = x := by
  simpa only [one_smul, punctureCollapse] using capRadialMap_eq_smul punctureRadialOrderIso 1 x
    (by simpa only [one_mul] using punctureRadialOrderIso_eq_self ‖x‖ hx)

/-- The inverse changes no point at radius at least three halves. -/
theorem punctureExpand_eq_self {x : StandardCapSpace} (hx : 3 / 2 ≤ ‖x‖) :
    punctureExpand x = x := by
  simpa only [one_smul, punctureExpand] using capRadialMap_eq_smul punctureRadialOrderIso.symm 1 x
    (by simpa only [one_mul] using punctureRadialOrderIso_symm_eq_self ‖x‖ hx)

end PoincareMT.M38
