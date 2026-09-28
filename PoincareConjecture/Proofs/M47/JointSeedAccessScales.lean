import PoincareConjecture.Proofs.M47.JointSeedBallScales










set_option autoImplicit false

namespace PoincareConjecture.M47



theorem jointSeed_radial_radius_action_budget {A B a v : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (ha : 0 < a) (hav : a ≤ v) :
    2 * (Real.sqrt a / (4 * A * B)) ^ 2 / v ≤ 1 / 8 := by
  have hv : 0 < v := ha.trans_le hav
  have hAB : 1 ≤ A * B := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hrad : Real.sqrt a / (4 * A * B) ≤ Real.sqrt a / 4 :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg a) (by norm_num) (by nlinarith)
  have hradpos : 0 ≤ Real.sqrt a / (4 * A * B) := by positivity
  have hsquare := (sq_le_sq₀ hradpos (by positivity : 0 ≤ Real.sqrt a / 4)).2 hrad
  apply (div_le_iff₀ hv).2
  nlinarith [Real.sq_sqrt ha.le]



theorem jointSeed_radial_scalar_action_budget {A L v : ℝ}
    (hA : 1 ≤ A) (hL : 0 ≤ L) (hv : 0 ≤ v) (hbudget : A * L * v ≤ 1 / 64) :
    8 * L * v ≤ 1 / 8 := by
  have h := mul_le_mul_of_nonneg_right hA (mul_nonneg hL hv)
  nlinarith



theorem jointSeed_mid_age_action_normalization {d v L r : ℝ}
    (hd : 0 < d) (hv : 0 < v) (hvd : v ≤ d / 2)
    (hscalar : 8 * L * v ≤ 1 / 8) (hkinetic : 2 * r ^ 2 / v ≤ 1 / 8) :
    (3 * Real.sqrt d + (8 * L * v + 2 * r ^ 2 / v) * Real.sqrt d) /
      (2 * Real.sqrt (d - v / 2)) < 2 := by
  have htheta : 0 < d - v / 2 := by linarith
  have hden : 0 < 2 * Real.sqrt (d - v / 2) := by positivity
  have hcost : 3 * Real.sqrt d + (8 * L * v + 2 * r ^ 2 / v) * Real.sqrt d ≤
      (13 / 4 : ℝ) * Real.sqrt d := by
    have h := mul_le_mul_of_nonneg_right (show 8 * L * v + 2 * r ^ 2 / v ≤ 1 / 4 by linarith)
      (Real.sqrt_nonneg d)
    linarith
  have hroot : (13 / 4 : ℝ) * Real.sqrt d < 4 * Real.sqrt (d - v / 2) := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).1
    nlinarith [Real.sq_sqrt hd.le, Real.sq_sqrt htheta.le]
  apply (div_lt_iff₀ hden).2
  linarith

end PoincareConjecture.M47
