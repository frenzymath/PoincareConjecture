import PoincareConjecture.Proofs.M09.BilinearTrace

set_option autoImplicit false

open scoped BigOperators RealInnerProductSpace

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem bilinear_trace_basis_eq (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ E) :
    (∑ i, B (e i) (e i)) = ∑ j, B (f j) (f j) :=
  (continuousTrace_formOperator B e).symm.trans (continuousTrace_formOperator B f)

theorem endomorphism_square_trace (L : E →L[ℝ] E) (e : OrthonormalBasis ι ℝ E) :
    (∑ i, ⟪L (e i), L (e i)⟫) = continuousTrace (L.adjoint * L) := by
  rw [continuousTrace_apply, LinearMap.trace_eq_sum_inner _ e]
  apply Finset.sum_congr rfl
  intro i _
  exact (L.adjoint_inner_right (e i) (L (e i))).symm

theorem bilinear_square_contraction (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (x : E) :
    (∑ j, (B x (e j)) ^ 2) = ⟪formOperator B x, formOperator B x⟫ := by
  simpa only [formOperator_pairing, real_inner_self_eq_norm_sq] using
    e.sum_sq_inner_left (formOperator B x)

theorem bilinear_square_trace (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) :
    (∑ i, ∑ j, (B (e i) (e j)) ^ 2) =
      continuousTrace ((formOperator B).adjoint * formOperator B) := by
  simp_rw [bilinear_square_contraction B e]
  exact endomorphism_square_trace (formOperator B) e

theorem bilinear_square_basis_eq (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, (B (e i) (e j)) ^ 2) = ∑ i, ∑ j, (B (f i) (f j)) ^ 2 :=
  (bilinear_square_trace B e).trans (bilinear_square_trace B f).symm

end PoincareConjecture.Proofs.M09
