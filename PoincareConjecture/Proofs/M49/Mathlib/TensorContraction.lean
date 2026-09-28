import Mathlib.Analysis.Matrix.Order










set_option autoImplicit false

open scoped BigOperators Matrix

namespace Matrix


set_option backward.isDefEq.respectTransparency false in


theorem tensor_contraction_nonneg {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) (T : (σ → ι) → ℝ) :
    0 ≤ ∑ a : σ → ι, ∑ b : σ → ι,
      (∏ j : σ, G (a j) (b j)) * T a * T b := by
  classical
  have hK (s : Finset σ) :
      (show Matrix (σ → ι) (σ → ι) ℝ from
        fun a b => ∏ j ∈ s, G (a j) (b j)).PosSemidef := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.prod_empty, vecMulVec, of, Equiv.refl_apply, Pi.star_apply,
          star_one, mul_one] using!
          posSemidef_vecMulVec_self_star (fun _ : σ → ι => (1 : ℝ))
    | @insert j s hj ih =>
        have h := (hG.submatrix (fun a : σ → ι => a j)).hadamard ih
        simpa only [Finset.prod_insert hj, hadamard, submatrix, of] using! h
  have h := (hK Finset.univ).dotProduct_mulVec_nonneg T
  simpa only [star_trivial, dotProduct, mulVec, Finset.mul_sum,
    mul_left_comm, mul_assoc] using h

end Matrix
