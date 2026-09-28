import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.UnequalHeight

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

theorem exists_quadraticMinimum_height_adjustment {b s : Real} (hb : 0 < b) (hs : 0 < s) :
    ∃ H : Real ≃ₘ[Real] Real, StrictMono H ∧
      (∀ t ≤ -1, H t = t) ∧ (∀ t, 0 ≤ t → H t = b + s * t) := by
  let d := min (1 : Real) (b / (s + 1))
  have hd : 0 < d := lt_min zero_lt_one (div_pos hb (by linarith))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hds : d * (s + 1) ≤ b :=
    (le_div_iff₀ (show 0 < s + 1 by linarith)).mp (min_le_right _ _)
  have hab : -d / 2 ≤ b - s * d / 2 := by nlinarith
  let A : Real ≃ₘ[Real] Real := {
    toEquiv := {
      toFun := fun t => t / d + 1 / 2
      invFun := fun t => (t - 1 / 2) * d
      left_inv := by intro t; field_simp; ring
      right_inv := by intro t; field_simp; ring }
    contMDiff_toFun := ((contDiff_id.div_const d).add contDiff_const).contMDiff
    contMDiff_invFun := ((contDiff_id.sub contDiff_const).mul contDiff_const).contMDiff }
  let D := CappedCylinder.unequalHeightDiffeomorph hab hd (mul_pos hs hd)
  let H := A.trans D
  have hH (t : Real) : H t =
      CappedCylinder.unequalHeight (-d / 2) (b - s * d / 2) d (s * d) (t / d + 1 / 2) := rfl
  refine ⟨H, ?_, ?_, ?_⟩
  · apply (CappedCylinder.strictMono_unequalHeight hab hd (mul_pos hs hd)).comp
    intro x y hxy
    change x / d + 1 / 2 < y / d + 1 / 2
    linarith [(div_lt_div_iff_of_pos_right hd).mpr hxy]
  · intro t ht
    rw [hH, CappedCylinder.unequalHeight_of_le]
    · field_simp
      ring
    · have hdiv : t / d ≤ -1 := (div_le_iff₀ hd).mpr (by linarith)
      linarith
  · intro t ht
    rw [hH, CappedCylinder.unequalHeight_of_ge]
    · field_simp
      ring
    · have hdiv : 0 ≤ t / d := div_nonneg ht hd.le
      linarith

end Poincare.Manifold.Schoenflies
