import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring










set_option autoImplicit false

namespace PoincareConjecture.M47

private theorem normalization_three_term_cauchy (a b c x y z : ℝ) :
    (a * x + b * y + c * z) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith only [sq_nonneg (a * y - b * x), sq_nonneg (a * z - c * x),
    sq_nonneg (b * z - c * y)]



theorem cap_normalization_factor_bounds {gamma x y z E d : ℝ}
    (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 1200)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hcomponents : x ^ 2 + y ^ 2 + z ^ 2 ≤ E) (hE : E ≤ gamma ^ 2)
    (hd : |d| ≤ (3 / 4 : ℝ) * x + (1 / 50 : ℝ) * y + (31 / 10 : ℝ) * z) :
    |d| ≤ 4 * gamma ∧ |1 + d| ≤ 301 / 300 := by
  have hnonneg : 0 ≤ (3 / 4 : ℝ) * x + (1 / 50 : ℝ) * y + (31 / 10 : ℝ) * z :=
    by positivity
  have hsq := (sq_le_sq₀ (abs_nonneg d) hnonneg).mpr hd
  have hcs := normalization_three_term_cauchy (3 / 4) (1 / 50) (31 / 10) x y z
  have hsum : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hfour : |d| ≤ 4 * gamma := by
    nlinarith [sq_abs d, abs_nonneg d]
  refine ⟨hfour, ?_⟩
  calc
    |1 + d| ≤ 1 + |d| := by simpa using abs_add_le (1 : ℝ) d
    _ ≤ 301 / 300 := by linarith




theorem cap_normalization_energy_le {gamma x y z E d : ℝ}
    (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 1200)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hcomponents : x ^ 2 + y ^ 2 + z ^ 2 ≤ E) (hE : E ≤ gamma ^ 2)
    (hd : |d| ≤ (3 / 4 : ℝ) * x + (1 / 50 : ℝ) * y + (31 / 10 : ℝ) * z) :
    (|1 + d| * x + Real.sqrt 3 * |d|) ^ 2 + (1 + d) ^ 2 * (E - x ^ 2) ≤ 36 * E := by
  have hfactor := (cap_normalization_factor_bounds hgamma hsmall hx hy hz hcomponents hE hd).2
  have hroot : Real.sqrt 3 ≤ (7 / 4 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hfirst : |1 + d| * x + Real.sqrt 3 * |d| ≤
      (2779 / 1200 : ℝ) * x + (7 / 200 : ℝ) * y + (217 / 40 : ℝ) * z := by
    calc
      _ ≤ (301 / 300 : ℝ) * x + (7 / 4 : ℝ) *
          ((3 / 4 : ℝ) * x + (1 / 50 : ℝ) * y + (31 / 10 : ℝ) * z) :=
        add_le_add (mul_le_mul_of_nonneg_right hfactor hx)
          (mul_le_mul hroot hd (abs_nonneg d) (by norm_num))
      _ = _ := by ring
  have hfirst0 : 0 ≤ |1 + d| * x + Real.sqrt 3 * |d| := by positivity
  have hlinear0 : 0 ≤
      (2779 / 1200 : ℝ) * x + (7 / 200 : ℝ) * y + (217 / 40 : ℝ) * z := by positivity
  have hfirstSq := (sq_le_sq₀ hfirst0 hlinear0).mpr hfirst
  have hcs := normalization_three_term_cauchy (2779 / 1200) (7 / 200) (217 / 40) x y z
  let C : ℝ := (2779 / 1200 : ℝ) ^ 2 + (7 / 200 : ℝ) ^ 2 + (217 / 40 : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hzero : (|1 + d| * x + Real.sqrt 3 * |d|) ^ 2 ≤ C * E :=
    hfirstSq.trans (hcs.trans (mul_le_mul_of_nonneg_left hcomponents hC))
  have hfactorSq : (1 + d) ^ 2 ≤ (301 / 300 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (1 + d)) (by norm_num : (0 : ℝ) ≤ 301 / 300)).mpr hfactor
  have htail : 0 ≤ E - x ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hE0 : 0 ≤ E := by nlinarith [sq_nonneg x]
  calc
    _ ≤ C * E + (301 / 300 : ℝ) ^ 2 * (E - x ^ 2) :=
      add_le_add hzero (mul_le_mul_of_nonneg_right hfactorSq htail)
    _ ≤ (C + (301 / 300 : ℝ) ^ 2) * E := by nlinarith [sq_nonneg x]
    _ ≤ 36 * E := mul_le_mul_of_nonneg_right (by norm_num [C]) hE0



theorem cap_normalization_strict_witness {gamma epsilon bound : ℝ}
    (hgamma : 0 ≤ gamma) (hscale : 6 * gamma ≤ epsilon) (hbound : bound < gamma ^ 2) :
    36 * bound < epsilon ^ 2 := by
  have hepsilon : 0 ≤ epsilon := (by positivity : (0 : ℝ) ≤ 6 * gamma).trans hscale
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 6 * gamma) hepsilon).mpr hscale
  nlinarith

end PoincareConjecture.M47
