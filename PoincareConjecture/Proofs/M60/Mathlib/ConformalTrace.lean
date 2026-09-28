import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem sum_bilinear_conformal_basis (B : LinearMap.BilinForm ℝ E)
    (b : OrthonormalBasis κ ℝ E) (w : ι → E)
    (hdim : Fintype.card ι = Module.finrank ℝ E) {a : ℝ} (ha : 0 < a)
    (hw : ∀ i j, inner ℝ (w i) (w j) = a * (if i = j then 1 else 0)) :
    (∑ i, B (w i) (w i)) = a * ∑ j, B (b j) (b j) := by
  let c : ℝ := (Real.sqrt a)⁻¹
  have hc : c * c = a⁻¹ := by
    dsimp [c]
    rw [← mul_inv_rev, ← pow_two, Real.sq_sqrt ha.le]
  have ho : Orthonormal ℝ (fun i => c • w i) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [real_inner_smul_left, real_inner_smul_right, hw]
    by_cases hij : i = j
    · simp only [hij, ite_true, mul_one]
      rw [← mul_assoc, hc, inv_mul_cancel₀ ha.ne']
    · simp only [hij, ite_false, mul_zero]
  let o := OrthonormalBasis.mk ho
    (ho.linearIndependent.span_eq_top_of_card_eq_finrank' hdim).ge
  have hscale : (∑ i, B (w i) (w i)) = a * ∑ i, B (o i) (o i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [o, OrthonormalBasis.coe_mk, map_smul, LinearMap.smul_apply, smul_eq_mul]
    calc
      _ = (a * (c * c)) * B (w i) (w i) := by rw [hc, mul_inv_cancel₀ ha.ne', one_mul]
      _ = _ := by ring
  exact hscale.trans (congrArg (a * ·) (bilinear_sum_orthonormalBasis_eq B o b))

end PoincareConjecture.M60
