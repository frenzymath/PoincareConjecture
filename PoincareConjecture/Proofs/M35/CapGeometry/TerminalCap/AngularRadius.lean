import PoincareConjecture.Proofs.M35.CapGeometry.RadialCylinderTensor
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetEstimates








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35



theorem radialCylinderTensor_angular_bound {A : ℝ → ℝ} {epsilon s : ℝ}
    (he : 0 < epsilon)
    (hclose : RoundCylinderClose epsilon 0 (radialCylinderTensor A 1))
    (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) : |A s - 2| < 4 * epsilon := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), by simp⟩
  have h := hclose.component_abs_lt he (by norm_num) (by norm_num)
    (z := (q, s)) hs (Nat.zero_le _) ![0, 0]
  dsimp only at h
  have hgram : roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) 0 0 = 2 := by
    rw [roundCylinderGram_center]
    norm_num
  have hh : |A s / 2 * 2 - 2| < (2 : ℝ) ^ 2 * epsilon := by
    simpa only [roundCylinderIteratedDerivative, radialCylinderTensor_coefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, hgram, roundCylinderCoordinateBasis,
    pow_zero, pow_one, one_pow, mul_zero, sub_zero, add_zero, zero_mul,
    Fin.isValue, Matrix.head_cons, one_mul, mul_one] using h
  norm_num at hh
  exact hh

theorem radialCylinderTensor_angular_lt_four {A : ℝ → ℝ} {epsilon : ℝ}
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (hclose : RoundCylinderClose epsilon 0 (radialCylinderTensor A 1)) : A 0 < 4 := by
  have h := radialCylinderTensor_angular_bound he hclose
    (show (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ from
      ⟨neg_neg_of_pos (inv_pos.mpr he), inv_pos.mpr he⟩)
  have hh := (abs_lt.mp h).2
  linarith only [hh, hehalf]

end PoincareConjecture.M35
