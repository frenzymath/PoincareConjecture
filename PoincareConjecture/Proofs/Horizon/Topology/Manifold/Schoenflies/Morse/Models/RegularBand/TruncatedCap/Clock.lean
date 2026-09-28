import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.HeightStretch

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.TruncatedCap

theorem exists_clock {a : Real} (ha : 0 < a) (ha1 : a < 1) :
    ∃ φ : Real ≃ₘ[Real] Real, StrictMono φ ∧
      (∀ t, t ≤ (1+a)/2 → φ t = t-a) ∧
      (∀ t, 1 ≤ t → φ t = t) := by
  let d := 1-a
  let m := (3+a)/4
  have hd : 0 < d := sub_pos.mpr ha1
  have hab : m-a ≤ m := by linarith
  let A : Real ≃ₘ[Real] Real := {
    toEquiv := {
      toFun := fun t => (t-m)/d
      invFun := fun t => d*t+m
      left_inv := by intro t; field_simp; ring
      right_inv := by intro t; field_simp; ring }
    contMDiff_toFun := ((contDiff_id.sub contDiff_const).div_const d).contMDiff
    contMDiff_invFun := ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff }
  let D := cappedCylinderHeightDiffeomorph hab hd
  let φ := A.trans D
  have hφ (t : Real) : φ t = cappedCylinderHeight (m-a) m d ((t-m)/d) := rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · apply (strictMono_cappedCylinderHeight hab hd).comp
    intro x y hxy
    change (x-m)/d < (y-m)/d
    exact (div_lt_div_iff_of_pos_right hd).mpr (sub_lt_sub_right hxy m)
  · intro t ht
    rw [hφ, cappedCylinderHeight_of_le]
    · field_simp
      ring
    · apply (div_le_iff₀ hd).mpr
      dsimp [m, d]
      linarith
  · intro t ht
    rw [hφ, cappedCylinderHeight_of_ge]
    · field_simp
      ring
    · apply (le_div_iff₀ hd).mpr
      dsimp [m, d]
      linarith

end Poincare.Manifold.Schoenflies.TruncatedCap
