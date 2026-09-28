import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.ComparisonAngle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

noncomputable section
set_option autoImplicit false

open InnerProductGeometry

namespace Poincare.Alexandrov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem angle_sum_le_two_pi (u v w : V) :
    angle u v + angle u w + angle v w ≤ 2 * Real.pi := by
  have h := angle_le_angle_add_angle u (-v) w
  rw [angle_neg_right, angle_neg_left] at h
  linarith

theorem comparisonAngle_le_angle_of_cosh_le {r s t : ℝ} (hr : 0 < r) (hs : 0 < s)
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : Real.cosh t ≤ Real.cosh r * Real.cosh s -
      Real.sinh r * Real.sinh s * inner ℝ u v) :
    comparisonAngle r s t ≤ angle u v := by
  unfold comparisonAngle angle
  rw [hu, hv, mul_one, div_one]
  apply Real.arccos_le_arccos
  apply (le_div_iff₀ (mul_pos (Real.sinh_pos_iff.mpr hr)
    (Real.sinh_pos_iff.mpr hs))).mpr
  nlinarith

end Poincare.Alexandrov
