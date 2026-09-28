import PoincareConjecture.Statements.M14GeneralizedLGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic









set_option autoImplicit false

namespace PoincareConjecture.M14



theorem positiveStart_initial_factor {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.rpow (a / b) (3 / 2 : ℝ) = (a * Real.sqrt a) / (b * Real.sqrt b) := by
  rw [Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (div_pos ha hb), Real.rpow_one, ← Real.sqrt_eq_rpow,
    Real.sqrt_div ha.le]
  ring




theorem positiveStart_correction_algebra {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (L E S C K d g : ℝ)
    (hK : K = L / 2 - ((Real.sqrt b) ^ 3 * S + Real.sqrt b * E / 4) +
      a * Real.sqrt a * C)
    (hd : d = S / 2 - E / (8 * (Real.sqrt b) ^ 2) - L / (4 * (Real.sqrt b) ^ 3))
    (hg : g = E / (4 * (Real.sqrt b) ^ 2)) :
    d = S - (L / (2 * Real.sqrt b)) / b + K / (2 * b * Real.sqrt b) -
        (Real.rpow (a / b) (3 / 2 : ℝ) * C) / 2 ∧
    g = (L / (2 * Real.sqrt b)) / b - K / (b * Real.sqrt b) - S +
        Real.rpow (a / b) (3 / 2 : ℝ) * C := by
  rw [positiveStart_initial_factor ha hb, hK, hd, hg]
  have hsq := Real.sq_sqrt hb.le
  have hpos := Real.sqrt_pos.mpr hb
  generalize hroot : Real.sqrt b = r at *
  rw [← hsq]
  constructor <;> field_simp [hpos.ne'] <;> ring

end PoincareConjecture.M14
