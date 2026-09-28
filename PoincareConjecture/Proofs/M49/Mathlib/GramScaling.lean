import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt










set_option autoImplicit false

namespace Matrix



theorem sqrt_det_smul_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt ((c ^ 2 • A).det) = c ^ Fintype.card ι * Real.sqrt A.det := by
  rw [det_smul]
  have hp : (c ^ 2) ^ Fintype.card ι = (c ^ Fintype.card ι) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hc _)]

end Matrix
