import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/GramScaling.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Spatial scaling of the Gram volume density

The determinant contributes one metric scale per dimension and its square
root gives length scale to that dimension. This is the scaling used in
Morgan-Tian Lemma 17.12, p. 410, corrected to the cubic three-dimensional
power as in Perelman II, Section 8.1, p. 21.
-/

set_option autoImplicit false

namespace Matrix

/-- Squared length scaling gives the corresponding dimensional density
factor (MT Lemma 17.12, p. 410; Perelman II, Section 8.1, p. 21). -/
theorem sqrt_det_smul_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt ((c ^ 2 • A).det) = c ^ Fintype.card ι * Real.sqrt A.det := by
  rw [det_smul]
  have hp : (c ^ 2) ^ Fintype.card ι = (c ^ Fintype.card ι) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hc _)]

end Matrix
