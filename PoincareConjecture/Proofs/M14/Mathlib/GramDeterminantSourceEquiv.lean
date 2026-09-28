import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Real.Sqrt










set_option autoImplicit false

namespace PoincareConjecture.M14



theorem sqrt_max_det_bilin_source_equiv
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (B : LinearMap.BilinForm ℝ V) (C : V ≃ₗ[ℝ] V) :
    Real.sqrt (max 0 (Matrix.det (fun i j => B (C (b i)) (C (b j))))) =
      |LinearMap.det C.toLinearMap| *
        Real.sqrt (max 0 (Matrix.det (fun i j => B (b i) (b j)))) := by
  have hm := LinearMap.BilinForm.toMatrix_comp b b B C.toLinearMap C.toLinearMap
  have hd := congrArg Matrix.det hm
  simp only [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hd
  have hg : Matrix.det (fun i j => B (C (b i)) (C (b j))) =
      LinearMap.det C.toLinearMap ^ 2 * Matrix.det (fun i j => B (b i) (b j)) := by
    have hleft : (fun i j => B (C (b i)) (C (b j))) =
        LinearMap.BilinForm.toMatrix b (B.comp C.toLinearMap C.toLinearMap) := by
      ext i j
      simp only [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.comp_apply]
      rfl
    have hright : (fun i j => B (b i) (b j)) = LinearMap.BilinForm.toMatrix b B := by
      ext i j
      simp only [LinearMap.BilinForm.toMatrix_apply]
    rw [hleft, hright, hd]
    ring
  rw [hg]
  have hmax : max 0 (LinearMap.det C.toLinearMap ^ 2 *
      Matrix.det (fun i j => B (b i) (b j))) =
      LinearMap.det C.toLinearMap ^ 2 * max 0 (Matrix.det (fun i j => B (b i) (b j))) := by
    rw [mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero]
  rw [hmax, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end PoincareConjecture.M14
