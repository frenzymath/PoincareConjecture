import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped BigOperators
open Matrix

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

lemma quadratic_input_action_zero {A : Matrix I I ℝ} (hA : A.PosSemidef)
    (z : I → ℝ) (hz : z ⬝ᵥ (A *ᵥ z) = 0) (L : Matrix I I ℝ) :
    z ⬝ᵥ ((L * A + A * L.transpose) *ᵥ z) = 0 := by
  have hzero : A *ᵥ z = 0 :=
    (hA.dotProduct_mulVec_zero_iff z).mp (by simpa only [star_trivial] using hz)
  have hleft : z ᵥ* A = 0 := by
    ext i
    have hs (j) : A j i = A i j := by simpa only [star_trivial] using hA.1.apply i j
    simpa only [vecMul, mulVec, dotProduct, hs, mul_comm] using congrFun hzero i
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, hzero, mulVec_zero, dotProduct_zero,
    zero_add, ← mulVec_mulVec, dotProduct_mulVec, hleft, zero_dotProduct]

lemma hamiltonBlock_input_action_zero
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U C : I → I → ℝ) (W : I → ℝ)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef)
    (hnull : (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) = 0) :
    (∑ a, ∑ b, (∑ e, (C a e * M e b + C b e * M a e)) * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c,
        (∑ e, (C a e * P e b c + C b e * P a e c + C c e * P a b e)) * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        (∑ e, (C a e * R e b c d + C b e * R a e c d +
          C c e * R a b e d + C d e * R a b c e)) * U a b * U c d) = 0 := by
  let A : Matrix ((I × I) ⊕ I) ((I × I) ⊕ I) ℝ := Matrix.fromBlocks
    (fun ac bd => R ac.1 ac.2 bd.1 bd.2) (fun ac d => P ac.1 ac.2 d)
    (fun c bd => P bd.1 bd.2 c) M
  let L : Matrix ((I × I) ⊕ I) ((I × I) ⊕ I) ℝ := Matrix.fromBlocks
    (fun ac bd => (if ac.2 = bd.2 then C ac.1 bd.1 else 0) +
      (if ac.1 = bd.1 then C ac.2 bd.2 else 0)) 0 0 C
  let S : Matrix ((I × I) ⊕ I) ((I × I) ⊕ I) ℝ := Matrix.fromBlocks
    (fun ac bd => ∑ e, (C ac.1 e * R e ac.2 bd.1 bd.2 +
      C ac.2 e * R ac.1 e bd.1 bd.2 + C bd.1 e * R ac.1 ac.2 e bd.2 +
      C bd.2 e * R ac.1 ac.2 bd.1 e))
    (fun ac d => ∑ e, (C ac.1 e * P e ac.2 d + C ac.2 e * P ac.1 e d +
      C d e * P ac.1 ac.2 e))
    (fun c bd => ∑ e, (C bd.1 e * P e bd.2 c + C bd.2 e * P bd.1 e c +
      C c e * P bd.1 bd.2 e))
    (fun a b => ∑ e, (C a e * M e b + C b e * M a e))
  have hS : L * A + A * L.transpose = S := by
    ext (ac | a) (bd | b) <;>
      simp only [L, A, S, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
        Fintype.sum_sum_type, Fintype.sum_prod_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
        add_zero, zero_add, add_mul, mul_add, ite_mul, mul_ite,
        Finset.sum_add_distrib, Finset.sum_ite_irrel,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    all_goals simp only [mul_comm, add_comm, add_assoc]
  let z : ((I × I) ⊕ I) → ℝ := Sum.elim (fun ac => U ac.1 ac.2) W
  have hz : z ⬝ᵥ (A *ᵥ z) = 0 :=
    (hamiltonBlock_quadratic_eq R P M U W).trans hnull
  have h := quadratic_input_action_zero hQ z hz L
  rw [hS] at h
  have heval := hamiltonBlock_quadratic_eq
    (fun a b c d => ∑ e, (C a e * R e b c d + C b e * R a e c d +
      C c e * R a b e d + C d e * R a b c e))
    (fun a b c => ∑ e, (C a e * P e b c + C b e * P a e c + C c e * P a b e))
    (fun a b => ∑ e, (C a e * M e b + C b e * M a e)) U W
  exact heval.symm.trans h

end Poincare.RicciFlow.Harnack
