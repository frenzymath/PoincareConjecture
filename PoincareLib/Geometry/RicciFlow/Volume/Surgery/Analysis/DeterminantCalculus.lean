import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/DeterminantCalculus.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Derivatives of determinants and Gram Jacobians

The continuous multilinear determinant gives the row-replacement formula.
A row evolution of the form C * A gives trace(C) * det(A), including for
singular matrices and empty index types. Strict positivity is required
only for the subsequent square-root derivative.
-/

set_option autoImplicit false

open scoped BigOperators

namespace PoincareMT.SurgeryVolume.Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant as the actual continuous multilinear function of its rows. -/
noncomputable def continuousRowDeterminant :
    ContinuousMultilinearMap ℝ (fun _ : ι ↦ ι → ℝ) ℝ where
  toMultilinearMap := by
    let A := ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).compContinuousLinearMap
        (fun i ↦ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)))
    exact A.toContinuousMultilinearMap.toMultilinearMap
  cont := by
    exact (ContinuousAlternatingMap.coe_continuous _)

theorem continuousRowDeterminant_apply (A : Matrix ι ι ℝ) :
    continuousRowDeterminant A = A.det := by
  have hAlt :
      (ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).compContinuousLinearMap
          (fun i ↦ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)))).toAlternatingMap =
        Matrix.detRowAlternating := by
    ext v
    change _ = MultilinearMap.alternatization
      ((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap
        (fun i ↦ (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ))) v
    simp [MultilinearMap.alternatization_apply]
  change ((ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).compContinuousLinearMap
        (fun i ↦ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)))).toContinuousMultilinearMap) A = _
  change ((ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ).compContinuousLinearMap
        (fun i ↦ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)))).toAlternatingMap) A = _
  rw [hAlt]
  rfl

/-- Differentiating an actual matrix determinant replaces one row at a time. -/
theorem hasDerivAt_matrix_det {A : ℝ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A B t) :
    HasDerivAt (fun s ↦ (A s).det) (∑ i, ((A t).updateRow i (B i)).det) t := by
  have h := ((continuousRowDeterminant (ι := ι)).hasFDerivAt (A t)).comp_hasDerivAt t hA
  have h' := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s ↦ (continuousRowDeterminant_apply (A s)).symm))
  apply h'.congr_deriv
  change (continuousRowDeterminant (ι := ι)).linearDeriv
      (fun i ↦ A t i) (fun i ↦ B i) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← continuousRowDeterminant_apply ((A t).updateRow i (B i))]
  rfl

/-- Multiplicative row evolution gives the trace formula without requiring invertibility. -/
theorem hasDerivAt_matrix_det_of_mul {A : ℝ → Matrix ι ι ℝ} {C : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A (C * A t) t) :
    HasDerivAt (fun s ↦ (A s).det) (C.trace * (A t).det) t := by
  have hrow (i : ι) : (C * A t) i = ∑ k, C i k • A t k := by
    ext j
    simp [Matrix.mul_apply]
  have hdet (i : ι) : ((A t).updateRow i ((C * A t) i)).det = C i i * (A t).det := by
    rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  simpa only [hdet, Matrix.trace, Matrix.diag, Finset.sum_mul] using hasDerivAt_matrix_det hA

/-- At the identity the determinant derivative is the ordinary matrix trace. -/
theorem hasDerivAt_matrix_det_of_eq_one {A : ℝ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    {t : ℝ} (hA : HasDerivAt A B t) (hAt : A t = 1) :
    HasDerivAt (fun s ↦ (A s).det) B.trace t := by
  have h : HasDerivAt A (B * A t) t := by simpa only [hAt, mul_one] using hA
  simpa only [hAt, Matrix.det_one, mul_one] using hasDerivAt_matrix_det_of_mul h

/-- A positive Gram determinant has the expected half-trace square-root derivative. -/
theorem hasDerivAt_sqrt_matrix_det_of_mul {A : ℝ → Matrix ι ι ℝ} {C : Matrix ι ι ℝ}
    {t : ℝ} (hA : HasDerivAt A (C * A t) t) (hpos : 0 < (A t).det) :
    HasDerivAt (fun s ↦ Real.sqrt (A s).det)
      (C.trace * Real.sqrt (A t).det / 2) t := by
  have hsqrt : Real.sqrt (A t).det ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have h := (hasDerivAt_matrix_det_of_mul hA).sqrt hpos.ne'
  convert h using 1
  field_simp [hsqrt]
  rw [Real.sq_sqrt hpos.le]

/-- At an identity Gram matrix the volume Jacobian derivative is half the trace. -/
theorem hasDerivAt_sqrt_matrix_det_of_eq_one {A : ℝ → Matrix ι ι ℝ}
    {B : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A B t) (hAt : A t = 1) :
    HasDerivAt (fun s ↦ Real.sqrt (A s).det) (B.trace / 2) t := by
  have h : HasDerivAt A (B * A t) t := by simpa only [hAt, mul_one] using hA
  have hpos : 0 < (A t).det := by simp only [hAt, Matrix.det_one, zero_lt_one]
  simpa only [hAt, Matrix.det_one, Real.sqrt_one, mul_one] using
    hasDerivAt_sqrt_matrix_det_of_mul h hpos

end PoincareMT.SurgeryVolume.Measure
