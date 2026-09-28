
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith













namespace Poincare

theorem negativePart_le_of_hamiltonIvey {R X t : ℝ}
    (ht : 0 ≤ t)
    (hpinch : 0 < X → 2 * X * (Real.log X + Real.log (1 + t) - 3) ≤ R) :
    X ≤ max R (Real.exp 4) := by
  by_cases hX : X ≤ Real.exp 4
  · exact hX.trans (le_max_right _ _)
  have hXpos : 0 < X := (Real.exp_pos 4).trans (lt_of_not_ge hX)
  have hlogX : 4 ≤ Real.log X := by
    simpa using (Real.log_le_log_iff (Real.exp_pos 4) hXpos).mpr
      (le_of_not_ge hX)
  have hlogt : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hR : X ≤ R := by
    have := hpinch hXpos
    nlinarith
  exact hR.trans (le_max_left _ _)

theorem fullNorm_le_of_orderedSpectrum {k1 k2 k3 N R R₀ K : ℝ}
    (h12 : k2 ≤ k1) (h23 : k3 ≤ k2)
    (hscalar : R = 2 * (k1 + k2 + k3))
    (hnorm : N ^ 2 = 4 * (k1 ^ 2 + k2 ^ 2 + k3 ^ 2))
    (hR : R ≤ R₀) (hR₀ : R₀ ≤ K) (hK : 0 ≤ K) (hk3 : -K ≤ k3) :
    N ≤ 13 * K := by
  have h1 : -3 * K ≤ k1 ∧ k1 ≤ 3 * K := by constructor <;> linarith
  have h2 : -3 * K ≤ k2 ∧ k2 ≤ 3 * K := by constructor <;> linarith
  have h3 : -3 * K ≤ k3 ∧ k3 ≤ 3 * K := by constructor <;> linarith
  have hsq1 := mul_nonneg (sub_nonneg.mpr h1.2) (by linarith : 0 ≤ 3 * K + k1)
  have hsq2 := mul_nonneg (sub_nonneg.mpr h2.2) (by linarith : 0 ≤ 3 * K + k2)
  have hsq3 := mul_nonneg (sub_nonneg.mpr h3.2) (by linarith : 0 ≤ 3 * K + k3)
  nlinarith [sq_nonneg (N - 13 * K)]

theorem fullNorm_le_of_hamiltonIvey {k1 k2 k3 N R R₀ t : ℝ}
    (ht : 0 ≤ t) (h12 : k2 ≤ k1) (h23 : k3 ≤ k2)
    (hscalar : R = 2 * (k1 + k2 + k3))
    (hnorm : N ^ 2 = 4 * (k1 ^ 2 + k2 ^ 2 + k3 ^ 2))
    (hR : R ≤ R₀)
    (hpinch : 0 < max (-k3) 0 →
      2 * max (-k3) 0 * (Real.log (max (-k3) 0) + Real.log (1 + t) - 3) ≤ R) :
    N ≤ 13 * max R₀ (Real.exp 4) := by
  have hX := negativePart_le_of_hamiltonIvey ht hpinch
  have hK : 0 ≤ max R₀ (Real.exp 4) :=
    (Real.exp_pos 4).le.trans (le_max_right _ _)
  have hneg : -k3 ≤ max R₀ (Real.exp 4) :=
    (le_max_left _ _).trans (hX.trans (max_le_max_right _ hR))
  exact fullNorm_le_of_orderedSpectrum h12 h23 hscalar hnorm hR
    (le_max_left _ _) hK (by linarith)

theorem continuous_hamiltonIveyFullNormBound :
    Continuous (fun R₀ : ℝ => 13 * max R₀ (Real.exp 4)) :=
  continuous_const.mul (continuous_id.max continuous_const)

end Poincare
