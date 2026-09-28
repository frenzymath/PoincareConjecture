import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Trace









set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M48ScalarCalculus



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



theorem sum_diag_basis_independent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, B (b i) (b i)) = ∑ i, B (c i) (c i) := by
  exact (sum_diag_eq_trace B b).trans (sum_diag_eq_trace B c).symm

end PoincareConjecture.M48ScalarCalculus
