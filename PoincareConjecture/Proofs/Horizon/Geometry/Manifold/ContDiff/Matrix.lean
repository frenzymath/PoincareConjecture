import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Poincare.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contMDiffAt_matrix_det (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => G y i j) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (G y).det) x := by
  simp only [Matrix.det_apply']
  exact ContMDiffAt.sum fun σ _ => contMDiffAt_const.mul
    (ContMDiffAt.prod fun i _ => hG (σ i) i)

lemma contMDiffAt_matrix_inv_entry (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => G y i j) x)
    (hx : (G x).det ≠ 0) (i j : ι) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((contMDiffAt_matrix_det G x hG).inv₀ hx).mul
  apply contMDiffAt_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contMDiffAt_const (I := I) (x := x) (n := ∞)
      (c := (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hG a b

end Poincare.Manifold
