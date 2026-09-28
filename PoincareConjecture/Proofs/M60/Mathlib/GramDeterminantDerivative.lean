import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring











set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M60



theorem inverse_contraction_fin_two (G H : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, (G⁻¹) i j * H j i) =
      (H 0 0 * G 1 1 + G 0 0 * H 1 1 - H 0 1 * G 1 0 - G 0 1 * H 1 0) /
        Matrix.det G := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring



theorem hasDerivWithinAt_sqrt_det_fin_two {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : Matrix (Fin 2) (Fin 2) ℝ} {J : Set ℝ} {t : ℝ}
    (hG : ∀ i j, HasDerivWithinAt (fun s => G s i j) (H i j) J t)
    (hpos : 0 < Matrix.det (G t)) :
    HasDerivWithinAt (fun s => Real.sqrt (Matrix.det (G s)))
      (((∑ i : Fin 2, ∑ j : Fin 2, ((G t)⁻¹) i j * H j i) / 2) *
        Real.sqrt (Matrix.det (G t))) J t := by
  have hdet : HasDerivWithinAt (fun s => Matrix.det (G s))
      (H 0 0 * G t 1 1 + G t 0 0 * H 1 1 - H 0 1 * G t 1 0 - G t 0 1 * H 1 0) J t := by
    convert! ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0)) using 1
    · funext s
      exact Matrix.det_fin_two (G s)
    · ring
  convert hdet.sqrt hpos.ne' using 1
  rw [inverse_contraction_fin_two]
  have hsqrt : Real.sqrt (Matrix.det (G t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsquare := Real.sq_sqrt hpos.le
  field_simp
  rw [hsquare]

end PoincareConjecture.M60
