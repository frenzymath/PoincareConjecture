import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false

namespace PoincareConjecture.M10

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance correctionBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance correctionBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem metric_hessian_correction_le
    (B : E →L[ℝ] E →L[ℝ] ℝ) (Q : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (d : E →L[ℝ] ℝ) (v : E) {S H : ℝ} (hS : 0 ≤ S)
    (hB : ‖B‖ ≤ S) (hQ : ‖Q‖ ≤ S) (hI : ‖B.inverse‖ ≤ S) (hd : ‖d‖ ≤ S)
    (hH : H ≤ S * B v v) :
    H + Q v v (B.inverse d) - Q (B.inverse d) v v / 2 ≤
      (S ^ 2 + 2 * S ^ 3) * ‖v‖ ^ 2 := by
  let a := B.inverse d
  have ha : ‖a‖ ≤ S ^ 2 := by
    calc
      ‖a‖ ≤ ‖B.inverse‖ * ‖d‖ := B.inverse.le_opNorm d
      _ ≤ S * S := mul_le_mul hI hd (norm_nonneg _) hS
      _ = S ^ 2 := by ring
  have hBv : B v v ≤ S * ‖v‖ ^ 2 := calc
    B v v ≤ |B v v| := le_abs_self _
    _ ≤ ‖B‖ * ‖v‖ * ‖v‖ := B.le_opNorm₂ v v
    _ ≤ S * ‖v‖ * ‖v‖ := by gcongr
    _ = S * ‖v‖ ^ 2 := by ring
  have hQa (x y z : E) : |Q x y z| ≤ S * ‖x‖ * ‖y‖ * ‖z‖ := calc
    |Q x y z| ≤ ‖Q x‖ * ‖y‖ * ‖z‖ := (Q x).le_opNorm₂ y z
    _ ≤ (‖Q‖ * ‖x‖) * ‖y‖ * ‖z‖ := by gcongr; exact Q.le_opNorm x
    _ ≤ S * ‖x‖ * ‖y‖ * ‖z‖ := by gcongr
  have hfirst : |Q v v a| ≤ S ^ 3 * ‖v‖ ^ 2 := calc
    _ ≤ S * ‖v‖ * ‖v‖ * ‖a‖ := hQa v v a
    _ ≤ S * ‖v‖ * ‖v‖ * S ^ 2 := by gcongr
    _ = S ^ 3 * ‖v‖ ^ 2 := by ring
  have hsecond : |Q a v v| ≤ S ^ 3 * ‖v‖ ^ 2 := calc
    _ ≤ S * ‖a‖ * ‖v‖ * ‖v‖ := hQa a v v
    _ ≤ S * S ^ 2 * ‖v‖ * ‖v‖ := by gcongr
    _ = S ^ 3 * ‖v‖ ^ 2 := by ring
  have hH' := hH.trans (mul_le_mul_of_nonneg_left hBv hS)
  have hfirst' := (abs_le.mp hfirst).2
  have hsecond' := (abs_le.mp hsecond).1
  change H + Q v v a - Q a v v / 2 ≤ _
  nlinarith [mul_nonneg (pow_nonneg hS 3) (sq_nonneg ‖v‖)]

end

end PoincareConjecture.M10
