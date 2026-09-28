import PoincareConjecture.Proofs.M49.Mathlib.FiniteJumpBalance
import PoincareConjecture.Proofs.M49.Mathlib.ExponentialLeftLimit

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal BigOperators

namespace ENNReal

theorem expWeighted_add_sum_le_of_finite_left_jumps (k : ℝ)
    {V loss : ℝ → ℝ≥0∞} {a b : ℝ} (S : Finset ℝ)
    (hab : a ≤ b) (hS : (S : Set ℝ) ⊆ Ioc a b)
    (hregular : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Disjoint (S : Set ℝ) (Ioc x y) →
        V y ≤ ENNReal.ofReal (Real.exp (k * (y - x))) * V x)
    (hjump : ∀ T ∈ S, ∃ L : ℝ≥0∞, Tendsto V (𝓝[<] T) (𝓝 L) ∧
      V T + loss T ≤ L) :
    ENNReal.ofReal (Real.exp (-(k * b))) * V b +
        ∑ T ∈ S, ENNReal.ofReal (Real.exp (-(k * T))) * loss T ≤
      ENNReal.ofReal (Real.exp (-(k * a))) * V a := by
  let w := fun t => ENNReal.ofReal (Real.exp (-(k * t))) * V t
  have hbalance : w b + ∑ T ∈ S, ENNReal.ofReal (Real.exp (-(k * T))) * loss T ≤
      w a + ∑ _T ∈ S, (0 : ℝ≥0∞) := by
    apply add_sum_le_add_sum_of_finite_left_jumps S hab hS
    · intro x hx y hy hxy hdis
      have h := mul_le_mul_right (hregular x hx y hy hxy hdis)
        (ENNReal.ofReal (Real.exp (-(k * y))))
      rw [← mul_assoc, ← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at h
      have he : -(k * y) + k * (y - x) = -(k * x) := by ring
      rwa [he] at h
    · intro T hT
      obtain ⟨L, hL, hdrop⟩ := hjump T hT
      have hweight : Continuous (fun t : ℝ => ENNReal.ofReal (Real.exp (-(k * t)))) :=
        continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
      refine ⟨ENNReal.ofReal (Real.exp (-(k * T))) * L, ?_, ?_⟩
      · exact ENNReal.Tendsto.mul
          ((hweight.tendsto T).mono_left nhdsWithin_le_nhds)
          (Or.inl (ne_of_gt (ofReal_pos.mpr (Real.exp_pos _))))
          hL (Or.inr ofReal_ne_top)
      · simpa only [w, mul_add, add_zero] using
          mul_le_mul_right hdrop (ENNReal.ofReal (Real.exp (-(k * T))))
  simpa only [Finset.sum_const_zero, add_zero] using hbalance

end ENNReal
