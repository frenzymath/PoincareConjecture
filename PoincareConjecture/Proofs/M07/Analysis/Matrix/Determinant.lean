import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace Poincare.Matrix

open scoped BigOperators Matrix.Norms.Elementwise

variable {n : Type*} [Fintype n] [DecidableEq n]

private def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

private theorem detMultilinear_linearDeriv (A B : Matrix n n ℝ) :
    (detMultilinear.linearDeriv A) B = Matrix.trace (Matrix.adjugate A * B) := by
  change (detMultilinear.linearDeriv (fun i j => A i j)) (fun i j => B i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (B i)).det) = _
  trans ∑ i, ∑ j, A.adjugate j i * B i j
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    rfl
  · rw [Finset.sum_comm]
    rfl

theorem fderiv_det_eq_trace_adjugate_mul (A B : Matrix n n ℝ) :
    fderiv ℝ Matrix.det A B = Matrix.trace (Matrix.adjugate A * B) := by
  change fderiv ℝ (fun a : n → n → ℝ => (Matrix.of a).det)
    (fun i j => A i j) (fun i j => B i j) = _
  have h := detMultilinear.hasFDerivAt (fun i j => A i j)
  change HasFDerivAt (fun a : n → n → ℝ => (Matrix.of a).det)
    (detMultilinear.linearDeriv (fun i j => A i j)) (fun i j => A i j) at h
  rw [h.fderiv]
  exact detMultilinear_linearDeriv A B

theorem fderiv_det_eq_det_mul_trace_inv_mul (A B : Matrix n n ℝ)
    (hA : IsUnit A.det) :
    fderiv ℝ Matrix.det A B = A.det * Matrix.trace (A⁻¹ * B) := by
  rw [fderiv_det_eq_trace_adjugate_mul]
  have hadj : Matrix.adjugate A = A.det • A⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hA, one_smul]
  rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differentiableAt_det {G : E → Matrix n n ℝ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    DifferentiableAt ℝ (fun y => (G y).det) x := by
  exact (detMultilinear.hasFDerivAt (fun i j => G x i j)).differentiableAt.comp x
    (differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr (hG i))

theorem fderiv_det {G : E → Matrix n n ℝ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hunit : IsUnit (G x).det) (v : E) :
    fderiv ℝ (fun y => (G y).det) x v =
      (G x).det * Matrix.trace ((G x)⁻¹ *
        Matrix.of (fun i j => fderiv ℝ (fun y => G y i j) x v)) := by
  have h := (detMultilinear.hasFDerivAt (fun i j => G x i j)).comp x
    (hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j => (hG i j).hasFDerivAt)
  change HasFDerivAt (fun y => (G y).det)
    ((detMultilinear.linearDeriv (fun i j => G x i j)).comp
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        fderiv ℝ (fun y => G y i j) x)) x at h
  rw [h.fderiv]
  change (detMultilinear.linearDeriv (fun i j => G x i j))
    (fun i j => fderiv ℝ (fun y => G y i j) x v) = _
  exact (detMultilinear_linearDeriv (G x)
    (Matrix.of (fun i j => fderiv ℝ (fun y => G y i j) x v))).trans
    ((fderiv_det_eq_trace_adjugate_mul _ _).symm.trans
      (fderiv_det_eq_det_mul_trace_inv_mul _ _ hunit))

private theorem sqrt_det_factor {d : ℝ} (hd : 0 < d) (a : ℝ) :
    (1 / (2 * Real.sqrt d)) * (d * a) =
      (1 / 2) * a * Real.sqrt d := by
  have hs : Real.sqrt d ≠ 0 := Real.sqrt_ne_zero'.mpr hd
  have hdiv : d / Real.sqrt d = Real.sqrt d := by
    rw [eq_comm, eq_div_iff hs]
    exact Real.mul_self_sqrt hd.le
  calc
    (1 / (2 * Real.sqrt d)) * (d * a) = (d / Real.sqrt d) * ((1 / 2) * a) := by ring
    _ = (1 / 2) * a * Real.sqrt d := by rw [hdiv]; ring

theorem fderiv_sqrt_det {G : E → Matrix n n ℝ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hpos : 0 < (G x).det) (v : E) :
    fderiv ℝ (fun y => Real.sqrt (G y).det) x v =
      (1 / 2) * Matrix.trace ((G x)⁻¹ *
        Matrix.of (fun i j => fderiv ℝ (fun y => G y i j) x v)) *
        Real.sqrt (G x).det := by
  rw [_root_.fderiv_sqrt (differentiableAt_det hG) (ne_of_gt hpos),
    smul_apply, smul_eq_mul, fderiv_det hG (ne_of_gt hpos).isUnit]
  exact sqrt_det_factor hpos _

theorem hasDerivAt_det_eq_det_mul_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hunit : IsUnit (G t).det) :
    HasDerivAt (fun s => (G s).det)
      ((G t).det * Matrix.trace ((G t)⁻¹ * G')) t := by
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun s => G s i j) t :=
    fun i j => (hG i j).differentiableAt
  have h := (differentiableAt_det hdiff).hasDerivAt
  rw [deriv, fderiv_det hdiff hunit] at h
  have hentries : Matrix.of (fun i j => fderiv ℝ (fun s => G s i j) t 1) = G' := by
    ext i j
    exact (hG i j).deriv
  rwa [hentries] at h

theorem hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / 2) * Matrix.trace ((G t)⁻¹ * G') * Real.sqrt (G t).det) t := by
  have hdet := hasDerivAt_det_eq_det_mul_trace_inv_mul G G' t hG (ne_of_gt hpos).isUnit
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp t hdet
  rw [sqrt_det_factor hpos] at h
  simpa only [Function.comp_def] using! h

end Poincare.Matrix
