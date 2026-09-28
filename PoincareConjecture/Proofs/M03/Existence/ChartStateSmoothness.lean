import PoincareConjecture.Proofs.M03.Existence.ChartStateContinuity

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

private theorem contDiff_det :
    ContDiff ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by
  have h : ContDiff ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, A (σ i) i) := by
    fun_prop
  convert h using 1
  funext A
  exact Matrix.det_apply' A

private theorem contDiff_adjugate :
    ContDiff ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  change ContDiff ℝ 1
    (fun x : Matrix (Fin n) (Fin n) ℝ => Matrix.adjugate x i j)
  have hrow : ContDiff ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ =>
      A.updateRow j (Pi.single i 1)) := by
    apply contDiff_pi.2
    intro r
    apply contDiff_pi.2
    intro c
    by_cases hr : r = j
    · subst r
      simp [Matrix.updateRow_apply]
      fun_prop
    · simp [Matrix.updateRow_apply, hr]
      fun_prop
  have hc := (contDiff_det (n := n)).comp hrow
  convert hc using 1 <;> funext A <;>
    simp only [Function.comp_apply, Matrix.adjugate_apply]

theorem contDiffAt_matrix_inv_of_nonsingular
    (G : Matrix (Fin n) (Fin n) ℝ) (hdet : G.det ≠ 0) :
    ContDiffAt ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) G := by
  have hd : ContDiffAt ℝ 1
      (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) G :=
    (contDiff_det (n := n)).contDiffAt
  have hi := hd.inv hdet
  have ha : ContDiffAt ℝ 1
      (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) G :=
    (contDiff_adjugate (n := n)).contDiffAt
  have hs : ContDiffAt ℝ 1 (fun A : Matrix (Fin n) (Fin n) ℝ =>
      A.det⁻¹ • A.adjugate) G := hi.smul ha
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv'] using hs

end PoincareConjecture.DeTurckNative
