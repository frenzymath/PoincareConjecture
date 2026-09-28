import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarTensorBound

set_option autoImplicit false

namespace PoincareConjecture.M47

private theorem scalar_numeric_reduction
    {a x y z r alpha delta eta : ℝ}
    (ha0 : 0 ≤ a) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hr0 : 0 ≤ r)
    (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (ha : a ≤ alpha) (hx : x ≤ delta) (hy : y ≤ delta) (hr : r ≤ (71 / 100 : ℝ))
    (hR : alpha * (71 / 100 : ℝ) ≤ 3 / 4)
    (hH : 2 * alpha * delta * ((7 / 4 : ℝ) * alpha + 7 / 4) ≤ 1 / 10)
    (hQ : 18 * alpha ^ 3 * delta ≤ eta) :
    a * x * r + (3 + 2 * a * x * (Real.sqrt 3 * a + Real.sqrt 3)) * z +
        18 * a ^ 3 * y ^ 2 ≤
      (3 / 4 : ℝ) * x + eta * y + (31 / 10 : ℝ) * z := by
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs : Real.sqrt 3 ≤ (7 / 4 : ℝ) := by nlinarith
  have hric : a * r ≤ (3 / 4 : ℝ) := (mul_le_mul ha hr hr0 halpha).trans hR
  have hax : 2 * a * x ≤ 2 * alpha * delta :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hx hx0 (by positivity)
  have hroot : Real.sqrt 3 * a + Real.sqrt 3 ≤ (7 / 4 : ℝ) * alpha + 7 / 4 :=
    add_le_add (mul_le_mul hs ha ha0 (by norm_num)) hs
  have hh : 2 * a * x * (Real.sqrt 3 * a + Real.sqrt 3) ≤ (1 / 10 : ℝ) :=
    (mul_le_mul hax hroot (by positivity) (by positivity)).trans hH
  have ha3 : a ^ 3 ≤ alpha ^ 3 := pow_le_pow_left₀ ha0 ha 3
  have hq : 18 * a ^ 3 * y ≤ eta :=
    (mul_le_mul (mul_le_mul_of_nonneg_left ha3 (by norm_num)) hy hy0 (by positivity)).trans hQ
  have hbase := mul_le_mul_of_nonneg_right hric hx0
  have hhessian := mul_le_mul_of_nonneg_right hh hz0
  have hquadratic := mul_le_mul_of_nonneg_right hq hy0
  nlinarith only [hbase, hhessian, hquadratic]

theorem cap_scalar_arithmetic_fine
    {a x y z r : ℝ}
    (ha0 : 0 ≤ a) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hr0 : 0 ≤ r)
    (ha : a ≤ (1200 / 1199 : ℝ)) (hx : x ≤ (1 / 1200 : ℝ))
    (hy : y ≤ (1 / 1200 : ℝ)) (hr : r ≤ (71 / 100 : ℝ)) :
    a * x * r + (3 + 2 * a * x * (Real.sqrt 3 * a + Real.sqrt 3)) * z +
        18 * a ^ 3 * y ^ 2 ≤
      (3 / 4 : ℝ) * x + (1 / 50 : ℝ) * y + (31 / 10 : ℝ) * z :=
  scalar_numeric_reduction ha0 hx0 hy0 hz0 hr0 (by norm_num) (by norm_num)
    ha hx hy hr (by norm_num) (by norm_num) (by norm_num)

theorem cap_scalar_arithmetic_coarse
    {a x y z r : ℝ}
    (ha0 : 0 ≤ a) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hr0 : 0 ≤ r)
    (ha : a ≤ (200 / 199 : ℝ)) (hx : x ≤ (1 / 200 : ℝ))
    (hy : y ≤ (1 / 200 : ℝ)) (hr : r ≤ (71 / 100 : ℝ)) :
    a * x * r + (3 + 2 * a * x * (Real.sqrt 3 * a + Real.sqrt 3)) * z +
        18 * a ^ 3 * y ^ 2 ≤
      (3 / 4 : ℝ) * x + (1 / 10 : ℝ) * y + (31 / 10 : ℝ) * z :=
  scalar_numeric_reduction ha0 hx0 hy0 hz0 hr0 (by norm_num) (by norm_num)
    ha hx hy hr (by norm_num) (by norm_num) (by norm_num)

theorem cap_scalar_arithmetic_energy
    {x y z epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (henergy : x ^ 2 + y ^ 2 + z ^ 2 ≤ epsilon ^ 2) :
    (3 / 4 : ℝ) * x + (1 / 10 : ℝ) * y + (31 / 10 : ℝ) * z ≤
      (16 / 5 : ℝ) * epsilon := by
  have hxy := sq_nonneg ((3 / 4 : ℝ) * y - (1 / 10 : ℝ) * x)
  have hxz := sq_nonneg ((3 / 4 : ℝ) * z - (31 / 10 : ℝ) * x)
  have hyz := sq_nonneg ((1 / 10 : ℝ) * z - (31 / 10 : ℝ) * y)
  have hcs : ((3 / 4 : ℝ) * x + (1 / 10 : ℝ) * y + (31 / 10 : ℝ) * z) ^ 2 ≤
      (4073 / 400 : ℝ) * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith only [hxy, hxz, hyz]
  have hsum := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 4073 / 400)
  nlinarith only [hcs, hsum, hepsilon, sq_nonneg epsilon]

end PoincareConjecture.M47
