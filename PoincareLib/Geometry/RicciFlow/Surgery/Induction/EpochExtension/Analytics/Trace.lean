import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Trace

/-!
# Basis independence of the metric trace

The diagonal contraction of a covariant bilinear form is the trace of its
Riesz endomorphism. This supporting algebra for the M48 scalar Laplacian
uses no symmetry hypothesis and works in dimension zero.
-/

set_option autoImplicit false

open scoped BigOperators

namespace PoincareMT.M48ScalarCalculus

/-- In an orthonormal basis, the metric diagonal contraction is the trace
of the endomorphism obtained by raising the second covariant index. -/
theorem sum_diag_eq_trace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (b : OrthonormalBasis ι ℝ E) :
    (∑ i, B (b i) (b i)) =
      LinearMap.trace ℝ E (InnerProductSpace.continuousLinearMapOfBilin B).toLinearMap := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis]
  apply Finset.sum_congr rfl
  intro i _hi
  change B (b i) (b i) = (b.repr (InnerProductSpace.continuousLinearMapOfBilin B (b i))) i
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm,
    InnerProductSpace.continuousLinearMapOfBilin_apply]

/-- The diagonal contraction of a covariant bilinear form is independent
of the chosen orthonormal basis. -/
theorem sum_diag_basis_independent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, B (b i) (b i)) = ∑ i, B (c i) (c i) := by
  exact (sum_diag_eq_trace B b).trans (sum_diag_eq_trace B c).symm

end PoincareMT.M48ScalarCalculus
