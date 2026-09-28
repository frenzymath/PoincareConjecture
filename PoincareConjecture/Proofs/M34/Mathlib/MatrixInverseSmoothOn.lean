import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
  {n : ℕ∞ω} {S : Set E} {A : E → Matrix ι ι 𝕜}

theorem ContDiffOn.matrix_det (hA : ∀ a b, ContDiffOn 𝕜 n (fun x => A x a b) S) :
    ContDiffOn 𝕜 n (fun x => (A x).det) S := by
  classical
  have heq : (fun x => (A x).det) = fun x =>
      ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : 𝕜) * ∏ i, A x (σ i) i := by
    funext x
    simp [Matrix.det_apply, Units.smul_def]
  rw [heq]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem ContDiffOn.matrix_inv (hA : ∀ a b, ContDiffOn 𝕜 n (fun x => A x a b) S)
    (hdet : ∀ x ∈ S, (A x).det ≠ 0) (a b : ι) :
    ContDiffOn 𝕜 n (fun x => (A x)⁻¹ a b) S := by
  classical
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  apply ((ContDiffOn.matrix_det hA).inv hdet).mul
  apply ContDiffOn.matrix_det
  intro i j
  by_cases hi : i = b
  · subst i
    simpa only [Matrix.updateRow_self] using
      (contDiffOn_const (c := (Pi.single a (1 : 𝕜) : ι → 𝕜) j) :
        ContDiffOn 𝕜 n (fun _ : E => (Pi.single a (1 : 𝕜) : ι → 𝕜) j) S)
  · simpa only [Matrix.updateRow_ne hi] using hA i j
