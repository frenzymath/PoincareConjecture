import PoincareConjecture.Proofs.M35.CapGeometry.CylinderTimeWeights
import PoincareConjecture.Proofs.M35.CapGeometry.CylinderTimeJets









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35



theorem roundCylinderJetErrorSquared_time_affine_le
    (B : ℝ → RoundCylinderTwoTensor)
    (haffine : ∀ u ≤ 0, ∀ z v w,
      B u z v w = (1 + 2 * u) * B 0 z v w - 2 * u * B (-1 / 2) z v w)
    (epsilon : ℝ) (hs0 : RoundCylinderTensorSmoothOn epsilon (B 0))
    (hshalf : RoundCylinderTensorSmoothOn epsilon (B (-1 / 2)))
    (order : ℕ) (u : ℝ) (hu : u ∈ Icc (-2 : ℝ) 0)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (b : ℝ) (hb : 0 ≤ b)
    (h0 : roundCylinderJetErrorSquared 0 (B 0) order z ≤ b)
    (hhalf : roundCylinderJetErrorSquared (-1 / 2) (B (-1 / 2)) order z ≤ b) :
    roundCylinderJetErrorSquared u (B u) order z ≤
      ((order + 1 : ℕ) : ℝ) * (18 + 32 * 2 ^ (order + 2)) * b := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  have hp : p ∈ c.target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨c.map_source (mem_chart_source _ _), hz⟩
  have hu1 : u < 1 := hu.2.trans_lt zero_lt_one
  have hA : (1 + 2 * u) ^ 2 ≤ 9 := by
    have h := mul_nonneg (show 0 ≤ 1 + 2 * u + 3 by linarith [hu.1])
      (show 0 ≤ 3 - (1 + 2 * u) by linarith [hu.2])
    nlinarith only [h]
  have hB : (-2 * u) ^ 2 ≤ 16 := by
    have h := mul_nonneg (show 0 ≤ -2 * u + 4 by linarith [hu.2])
      (show 0 ≤ 4 - (-2 * u) by linarith [hu.1])
    nlinarith only [h]
  have hterm (k : ℕ) (hk : k ≤ order) :
      roundCylinderTensorNormSquared u c p (roundCylinderIteratedDerivative u c (B u) k p) ≤
        (18 + 32 * 2 ^ (order + 2)) * b := by
    let T := roundCylinderIteratedDerivative 0 c (B 0) k p
    let S := roundCylinderIteratedDerivative (-1 / 2) c (B (-1 / 2)) k p
    have hEq : roundCylinderIteratedDerivative u c (B u) k p =
        fun a => (1 + 2 * u) * T a + (-2 * u) * S a := by
      funext a
      rw [roundCylinderIteratedDerivative_time_affine B haffine epsilon hs0 hshalf
        u hu.2 z.1 k p hp a]
      dsimp only [T, S]
      ring
    have hT : roundCylinderTensorNormSquared u c p T ≤ b :=
      (roundCylinderTensorNormSquared_mono_time hu.2 zero_lt_one z.1 z.2 T).trans
        ((roundCylinder_derivative_norm_le_jet zero_lt_one (B 0) z hk).trans h0)
    have hS : roundCylinderTensorNormSquared u c p S ≤ 2 ^ (2 + k) * b :=
      (roundCylinderTensorNormSquared_mono_time hu.2 zero_lt_one z.1 z.2 S).trans
        ((roundCylinderTensorNormSquared_zero_le_half z.1 z.2 S).trans
          (mul_le_mul_of_nonneg_left
            ((roundCylinder_derivative_norm_le_jet (by norm_num : (-1 / 2 : ℝ) < 1)
              (B (-1 / 2)) z hk).trans hhalf) (by positivity)))
    have hpw : (2 : ℝ) ^ (2 + k) ≤ 2 ^ (order + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hEq]
    calc
      _ ≤ 2 * (1 + 2 * u) ^ 2 * roundCylinderTensorNormSquared u c p T +
          2 * (-2 * u) ^ 2 * roundCylinderTensorNormSquared u c p S :=
        roundCylinderTensorNormSquared_linear_le hu1 z.1 z.2 _ _ T S
      _ ≤ 2 * (1 + 2 * u) ^ 2 * b + 2 * (-2 * u) ^ 2 * (2 ^ (2 + k) * b) :=
        add_le_add (mul_le_mul_of_nonneg_left hT (by positivity))
          (mul_le_mul_of_nonneg_left hS (by positivity))
      _ ≤ 18 * b + 32 * (2 ^ (2 + k) * b) :=
        add_le_add (mul_le_mul_of_nonneg_right (by nlinarith only [hA]) hb)
          (mul_le_mul_of_nonneg_right (by nlinarith only [hB])
            (mul_nonneg (by positivity) hb))
      _ ≤ 18 * b + 32 * (2 ^ (order + 2) * b) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpw hb) (show (0 : ℝ) ≤ 32 by norm_num))
      _ = _ := by ring
  unfold roundCylinderJetErrorSquared
  calc
    _ ≤ ∑ _k ∈ Finset.range (order + 1), (18 + 32 * 2 ^ (order + 2)) * b :=
      Finset.sum_le_sum fun k hk => hterm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end PoincareConjecture.M35
