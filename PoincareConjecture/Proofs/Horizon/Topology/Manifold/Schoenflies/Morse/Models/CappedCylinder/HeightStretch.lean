import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.ParametricInverse
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope



noncomputable section
set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies


def cappedCylinderHeight (a b s t : Real) : Real :=
  s * t + a + (b - a) * Real.smoothTransition (2 * t + 1 / 2)

theorem contDiff_cappedCylinderHeight (a b s : Real) :
    ContDiff Real ∞ (cappedCylinderHeight a b s) := by
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).add contDiff_const)))

theorem cappedCylinderHeight_of_le (a b s t : Real) (ht : t ≤ -(1 / 4)) :
    cappedCylinderHeight a b s t = a + s * t := by
  rw [cappedCylinderHeight, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem cappedCylinderHeight_of_ge (a b s t : Real) (ht : 1 / 4 ≤ t) :
    cappedCylinderHeight a b s t = b + s * t := by
  rw [cappedCylinderHeight, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem deriv_cappedCylinderHeight_pos {a b s : Real} (hab : a ≤ b) (hs : 0 < s)
    (t : Real) : 0 < deriv (cappedCylinderHeight a b s) t := by
  let k : Real → Real := fun t => Real.smoothTransition (2 * t + 1 / 2)
  have hk : ContDiff Real ∞ k := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hkm : Monotone k := fun x y hxy => Real.smoothTransition.monotone (by linarith)
  have hd := (((hasDerivAt_id t).const_mul s).add_const a).add
    (((hk.differentiable (by simp)) t).hasDerivAt.const_mul (b - a))
  have hd' : HasDerivAt (cappedCylinderHeight a b s) (s + (b - a) * deriv k t) t := by
    convert! hd using 1
    simp
  rw [hd'.deriv]
  exact add_pos_of_pos_of_nonneg hs (mul_nonneg (sub_nonneg.mpr hab) hkm.deriv_nonneg)

theorem strictMono_cappedCylinderHeight {a b s : Real} (hab : a ≤ b) (hs : 0 < s) :
    StrictMono (cappedCylinderHeight a b s) :=
  strictMono_of_deriv_pos (deriv_cappedCylinderHeight_pos hab hs)

theorem surjective_cappedCylinderHeight {a b s : Real} (hs : 0 < s) :
    Surjective (cappedCylinderHeight a b s) := by
  intro y
  let l := min (-(1 / 4) : Real) ((y - a) / s)
  let u := max (1 / 4 : Real) ((y - b) / s)
  have hl : cappedCylinderHeight a b s l ≤ y := by
    rw [cappedCylinderHeight_of_le a b s l (min_le_left _ _)]
    have h := (le_div_iff₀ hs).mp (min_le_right (-(1 / 4) : Real) ((y - a) / s))
    dsimp only [l]
    nlinarith
  have hu : y ≤ cappedCylinderHeight a b s u := by
    rw [cappedCylinderHeight_of_ge a b s u (le_max_left _ _)]
    have h := (div_le_iff₀ hs).mp (le_max_right (1 / 4 : Real) ((y - b) / s))
    dsimp only [u]
    nlinarith
  exact intermediate_value_univ l u (contDiff_cappedCylinderHeight a b s).continuous ⟨hl, hu⟩


def cappedCylinderHeightDiffeomorph {a b s : Real} (hab : a ≤ b) (hs : 0 < s) :
    Real ≃ₘ[Real] Real := by
  let H := cappedCylinderHeight a b s
  let D := Plane.fiberDiffeomorph
    ((contDiff_cappedCylinderHeight a b s).comp (contDiff_snd :
      ContDiff Real ∞ (Prod.snd : Real × Real → Real)))
    (fun _ t => deriv_cappedCylinderHeight_pos hab hs t)
    (fun _ => surjective_cappedCylinderHeight hs)
  let K : Real → Real := fun y => (D.symm (0, y)).2
  have hright (y : Real) : H (K y) = y := by
    have h := congrArg Prod.snd (D.apply_symm_apply (0, y))
    exact h
  have hleft (x : Real) : K (H x) = x :=
    congrArg Prod.snd (D.symm_apply_apply (0, x))
  exact {
    toFun := H
    invFun := K
    left_inv := hleft
    right_inv := hright
    contMDiff_toFun := (contDiff_cappedCylinderHeight a b s).contMDiff
    contMDiff_invFun := (D.symm.contDiff.snd.comp
      (f := fun y : Real => (0, y)) (contDiff_const.prodMk contDiff_id)).contMDiff }

@[simp] theorem cappedCylinderHeightDiffeomorph_apply {a b s : Real}
    (hab : a ≤ b) (hs : 0 < s) (t : Real) :
    cappedCylinderHeightDiffeomorph hab hs t = cappedCylinderHeight a b s t := rfl

end Poincare.Manifold.Schoenflies
