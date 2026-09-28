import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckComparison

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem capPersistence_component_sq_le (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : (Fin r → Fin 3) → ℝ) (a : Fin r → Fin 3) :
    (1 / 2 : ℝ) ^ r * T a ^ 2 ≤
      roundCylinderTensorNormSquared 0 (chartAt E₂ q) (chartAt E₂ q q, s) T := by
  classical
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_chart_center_inv (by norm_num : (0 : ℝ) ≠ 1),
    diagonal_tensor_contraction]
  let d : Fin 3 → ℝ := ![(2 * (1 - (0 : ℝ)))⁻¹, (2 * (1 - (0 : ℝ)))⁻¹, 1]
  have hd (i : Fin 3) : (1 / 2 : ℝ) ≤ d i := by fin_cases i <;> norm_num [d]
  have hd0 (i : Fin 3) : 0 ≤ d i := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hd i)
  have hp : (1 / 2 : ℝ) ^ r ≤ ∏ i, d (a i) := by
    have hp0 (i : Fin r) (_hi : i ∈ (Finset.univ : Finset (Fin r))) :
        (0 : ℝ) ≤ 1 / 2 := by norm_num
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod hp0 (fun i _ => hd (a i)))
  exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans
    (Finset.single_le_sum (fun b _ =>
      mul_nonneg (Finset.prod_nonneg fun i _ => hd0 (b i)) (sq_nonneg _))
      (Finset.mem_univ a))

theorem capPersistence_iterated_component_bound {delta : ℝ} {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose delta 0 B) (N : ℕ) (hN : N ≤ Nat.floor delta⁻¹)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-delta⁻¹) delta⁻¹)
    (k : ℕ) (hk : k ≤ N) (a : Fin (2 + k) → Fin 3) :
    |roundCylinderIteratedDerivative 0 (chartAt E₂ q) B k (chartAt E₂ q q, s) a| ≤
      Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + N)) := by
  obtain ⟨_, b, hb, hbound⟩ := hB
  have hterm : roundCylinderTensorNormSquared 0 (chartAt E₂ q) (chartAt E₂ q q, s)
      (roundCylinderIteratedDerivative 0 (chartAt E₂ q) B k (chartAt E₂ q q, s)) ≤
      delta ^ 2 := by
    apply le_trans (Finset.single_le_sum (fun j _ =>
      roundCylinderTensorNormSquared_chart_center_nonneg (by norm_num : (0 : ℝ) < 1)
        q s (roundCylinderIteratedDerivative 0 (chartAt E₂ q) B j (chartAt E₂ q q, s)))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.trans hN))))
    exact (hbound (q, s) hs).trans hb.le
  have hp : 0 < (1 / 2 : ℝ) ^ (2 + N) := pow_pos (by norm_num) _
  have hpow : (1 / 2 : ℝ) ^ (2 + N) ≤ (1 / 2 : ℝ) ^ (2 + k) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_left hk 2)
  have hsq : (roundCylinderIteratedDerivative 0 (chartAt E₂ q) B k
      (chartAt E₂ q q, s) a) ^ 2 ≤ delta ^ 2 / (1 / 2 : ℝ) ^ (2 + N) := by
    apply (le_div_iff₀ hp).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans
      ((capPersistence_component_sq_le q s _ a).trans hterm)
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hsq

end PoincareConjecture.M34
