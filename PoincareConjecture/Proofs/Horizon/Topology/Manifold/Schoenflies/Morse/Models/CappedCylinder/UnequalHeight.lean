import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.HeightStretch



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CappedCylinder

private def ramp (t : Real) : Real := t * Real.smoothTransition (4 * t)

private theorem smooth_ramp : ContDiff Real ∞ ramp :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))

private theorem ramp_zero {t : Real} (ht : t ≤ 0) : ramp t = 0 := by
  rw [ramp, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

private theorem ramp_eq {t : Real} (ht : 1 / 4 ≤ t) : ramp t = t := by
  rw [ramp, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

private theorem deriv_ramp_nonneg (t : Real) : 0 ≤ deriv ramp t := by
  by_cases ht : t < 0
  · have heq : ramp =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      exact ramp_zero hx.le
    rw [heq.deriv_eq, deriv_const]
  let k : Real -> Real := fun t => Real.smoothTransition (4 * t)
  have hk : ContDiff Real ∞ k :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hkm : Monotone k := fun x y hxy => Real.smoothTransition.monotone (by linarith)
  have hd := (hasDerivAt_id t).mul (hk.differentiable (by simp) t).hasDerivAt
  change HasDerivAt ramp _ t at hd
  rw [hd.deriv]
  exact add_nonneg (mul_nonneg zero_le_one (Real.smoothTransition.nonneg _))
    (mul_nonneg (le_of_not_gt ht) hkm.deriv_nonneg)



def unequalHeight (a b u w t : Real) : Real :=
  min u w * t + a + (b - a) * Real.smoothTransition (2 * t + 1 / 2) -
    (u - min u w) * ramp (-t) + (w - min u w) * ramp t

theorem contDiff_unequalHeight (a b u w : Real) :
    ContDiff Real ∞ (unequalHeight a b u w) := by
  exact ((((contDiff_const.mul contDiff_id).add contDiff_const).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).add contDiff_const)))).sub
    (contDiff_const.mul (smooth_ramp.comp contDiff_id.neg))).add
    (contDiff_const.mul smooth_ramp)

theorem unequalHeight_of_le (a b u w t : Real) (ht : t ≤ -(1 / 4)) :
    unequalHeight a b u w t = a + u * t := by
  rw [unequalHeight, Real.smoothTransition.zero_of_nonpos (by linarith),
    ramp_eq (by linarith : 1 / 4 ≤ -t), ramp_zero (by linarith : t ≤ 0)]
  ring

theorem unequalHeight_of_ge (a b u w t : Real) (ht : 1 / 4 ≤ t) :
    unequalHeight a b u w t = b + w * t := by
  rw [unequalHeight, Real.smoothTransition.one_of_one_le (by linarith),
    ramp_zero (by linarith : -t ≤ 0), ramp_eq ht]
  ring

theorem deriv_unequalHeight_pos {a b u w : Real} (hab : a ≤ b)
    (hu : 0 < u) (hw : 0 < w) (t : Real) :
    0 < deriv (unequalHeight a b u w) t := by
  let k : Real -> Real := fun t => Real.smoothTransition (2 * t + 1 / 2)
  have hk : ContDiff Real ∞ k := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hkm : Monotone k := fun x y hxy => Real.smoothTransition.monotone (by linarith)
  have hneg : HasDerivAt (fun t => ramp (-t)) (-deriv ramp (-t)) t := by
    simpa only [Function.comp_def, id_eq, mul_neg_one] using
      (smooth_ramp.differentiable (by simp) (-t)).hasDerivAt.comp t (hasDerivAt_id t).neg
  have hd := (((((hasDerivAt_id t).const_mul (min u w)).add_const a).add
    ((hk.differentiable (by simp) t).hasDerivAt.const_mul (b - a))).sub
    (hneg.const_mul (u - min u w))).add
    ((smooth_ramp.differentiable (by simp) t).hasDerivAt.const_mul (w - min u w))
  have hd' : HasDerivAt (unequalHeight a b u w)
      (min u w + (b - a) * deriv k t + (u - min u w) * deriv ramp (-t) +
        (w - min u w) * deriv ramp t) t := by
    convert! hd using 1
    simp only [mul_one, mul_neg, sub_neg_eq_add]
  rw [hd'.deriv]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (lt_min hu hw)
        (mul_nonneg (sub_nonneg.mpr hab) hkm.deriv_nonneg))
      (mul_nonneg (sub_nonneg.mpr (min_le_left _ _)) (deriv_ramp_nonneg _)))
    (mul_nonneg (sub_nonneg.mpr (min_le_right _ _)) (deriv_ramp_nonneg _))

theorem strictMono_unequalHeight {a b u w : Real} (hab : a ≤ b)
    (hu : 0 < u) (hw : 0 < w) : StrictMono (unequalHeight a b u w) :=
  strictMono_of_deriv_pos (deriv_unequalHeight_pos hab hu hw)

theorem surjective_unequalHeight {a b u w : Real} (hu : 0 < u) (hw : 0 < w) :
    Surjective (unequalHeight a b u w) := by
  intro y
  let l := min (-(1 / 4) : Real) ((y - a) / u)
  let r := max (1 / 4 : Real) ((y - b) / w)
  have hl : unequalHeight a b u w l ≤ y := by
    rw [unequalHeight_of_le a b u w l (min_le_left _ _)]
    have h := (le_div_iff₀ hu).mp (min_le_right (-(1 / 4) : Real) ((y - a) / u))
    dsimp only [l]
    nlinarith
  have hr : y ≤ unequalHeight a b u w r := by
    rw [unequalHeight_of_ge a b u w r (le_max_left _ _)]
    have h := (div_le_iff₀ hw).mp (le_max_right (1 / 4 : Real) ((y - b) / w))
    dsimp only [r]
    nlinarith
  exact intermediate_value_univ l r (contDiff_unequalHeight a b u w).continuous ⟨hl, hr⟩

def unequalHeightDiffeomorph {a b u w : Real} (hab : a ≤ b) (hu : 0 < u) (hw : 0 < w) :
    Real ≃ₘ[Real] Real := by
  let H := unequalHeight a b u w
  let D := Plane.fiberDiffeomorph
    ((contDiff_unequalHeight a b u w).comp (contDiff_snd :
      ContDiff Real ∞ (Prod.snd : Real × Real -> Real)))
    (fun _ t => deriv_unequalHeight_pos hab hu hw t)
    (fun _ => surjective_unequalHeight hu hw)
  let K : Real -> Real := fun y => (D.symm (0, y)).2
  exact {
    toFun := H
    invFun := K
    left_inv := fun x => congrArg Prod.snd (D.symm_apply_apply (0, x))
    right_inv := fun y => congrArg Prod.snd (D.apply_symm_apply (0, y))
    contMDiff_toFun := (contDiff_unequalHeight a b u w).contMDiff
    contMDiff_invFun := (D.symm.contDiff.snd.comp
      (f := fun y : Real => (0, y)) (contDiff_const.prodMk contDiff_id)).contMDiff }

@[simp] theorem unequalHeightDiffeomorph_apply {a b u w : Real}
    (hab : a ≤ b) (hu : 0 < u) (hw : 0 < w) (t : Real) :
    unequalHeightDiffeomorph hab hu hw t = unequalHeight a b u w t := rfl

end Poincare.Manifold.Schoenflies.CappedCylinder
