import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear











set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M10

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]


theorem abs_bilinear_self_le_of_basis_bound (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) {K : ℝ}
    (hcoeff : ∀ i j, |B (b i) (b j)| ≤ K) (v : E) :
    |B v v| ≤ (Fintype.card ι : ℝ) ^ 2 * K * ‖v‖ ^ 2 := by
  classical
  let c := fun i ↦ b.repr v i
  have hc (i : ι) : |c i| ≤ ‖v‖ := by
    dsimp only [c]
    rw [b.repr_apply_apply]
    simpa only [b.norm_eq_one, one_mul] using abs_real_inner_le_norm (b i) v
  have hexpand : B v v = ∑ i, ∑ j, c i * c j * B (b i) (b j) := by
    calc
      B v v = B (∑ i, c i • b i) (∑ j, c j • b j) := by
        rw [b.sum_repr]
      _ = ∑ i, ∑ j, c i * c j * B (b i) (b j) := by
        simp only [map_sum, map_smul, sum_apply, smul_apply,
          smul_eq_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hexpand]
  calc
    |∑ i, ∑ j, c i * c j * B (b i) (b j)| ≤
        ∑ i, ∑ j, |c i * c j * B (b i) (b j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖v‖ * ‖v‖ * K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hc i) (hc j) (abs_nonneg _) (norm_nonneg _))
        (hcoeff i j) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (Fintype.card ι : ℝ) ^ 2 * K * ‖v‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end PoincareConjecture.M10
