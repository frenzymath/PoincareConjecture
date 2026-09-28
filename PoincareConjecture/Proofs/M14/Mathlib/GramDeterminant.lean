import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt









set_option autoImplicit false

namespace LinearMap.BilinForm




theorem sqrt_max_det_comp_eq_abs_det_toMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W]
    (b : Module.Basis ι ℝ V) (c : Module.Basis ι ℝ W)
    (g : LinearMap.BilinForm ℝ W)
    (hc : ∀ i j, g (c i) (c j) = if i = j then 1 else 0)
    (A : V →ₗ[ℝ] W) :
    Real.sqrt (max 0 (Matrix.det (fun i j => g (A (b i)) (A (b j))))) =
      |Matrix.det (LinearMap.toMatrix b c A)| := by
  have hg : toMatrix c g = 1 := by
    ext i j
    simpa only [toMatrix_apply, Matrix.one_apply] using hc i j
  have hm : (fun i j => g (A (b i)) (A (b j))) =
      (LinearMap.toMatrix b c A).transpose * LinearMap.toMatrix b c A := by
    have h := toMatrix_comp c b g A A
    rw [hg, Matrix.mul_one] at h
    have heq : (fun i j => g (A (b i)) (A (b j))) = toMatrix b (g.comp A A) := by
      ext i j
      simp only [toMatrix_apply, comp_apply]
    exact heq.trans h
  have hd : Matrix.det (fun i j => g (A (b i)) (A (b j))) =
      Matrix.det (LinearMap.toMatrix b c A) ^ 2 := by
    rw [hm, Matrix.det_mul, Matrix.det_transpose, pow_two]
  rw [hd, max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs]

end LinearMap.BilinForm
