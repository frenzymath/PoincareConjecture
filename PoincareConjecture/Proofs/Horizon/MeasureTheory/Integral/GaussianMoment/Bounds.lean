import PoincareConjecture.Proofs.Horizon.MeasureTheory.Integral.GaussianMoment.Shells
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.UniformSpace.UniformConvergence









set_option autoImplicit false

open Set MeasureTheory Function Filter
open scoped ENNReal Topology

namespace Poincare.MeasureTheory.GaussianMoment

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
private theorem gaussian_le_on_shell (x : X) {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    {j : ℕ} {y : X} (hy : y ∈ shell x r j) :
    Real.exp (-dist x y ^ 2 / (c * r ^ 2)) ≤ Real.exp (-(j : ℝ) ^ 2 / c) := by
  apply Real.exp_le_exp.mpr
  have hsq : ((j : ℝ) * r) ^ 2 ≤ dist x y ^ 2 :=
    pow_le_pow_left₀ (by positivity) hy.1 2
  apply (div_le_div_iff₀ (by positivity : 0 < c * r ^ 2) hc).mpr
  nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hsq)]

theorem gaussian_weighted_integrable (μ : Measure X) (x : X)
    (n k : ℕ) {A B c r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hr : 0 < r) (hr1 : r ≤ 1)
    (hpos : 0 < μ.real (Metric.ball x r))
    (hfinite : ∀ R > 0, μ (Metric.ball x R) < ⊤)
    (hgrowth : ∀ R, r ≤ R → μ.real (Metric.ball x R) ≤
      A * (R / r) ^ n * Real.exp (B * R) * μ.real (Metric.ball x r))
    (hsum : Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ (n + k) *
      Real.exp (B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c)))
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hgauss : ∀ y, ‖f y‖ ≤ dist x y ^ k *
      (A / μ.real (Metric.ball x r)) * Real.exp (-dist x y ^ 2 / (c * r ^ 2))) :
    Integrable f μ ∧ (∫ y, ‖f y‖ ∂μ) ≤
      (A ^ 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ (n + k) *
        Real.exp (B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c)) * r ^ k := by
  let V := μ.real (Metric.ball x r)
  let K : ℕ → ℝ := fun j ↦ (((j : ℝ) + 1) * r) ^ k * (A / V) *
    Real.exp (-(j : ℝ) ^ 2 / c)
  let D : ℕ → ℝ := fun j ↦ (A ^ 2 * (((j : ℝ) + 1) ^ (n + k) *
    Real.exp (B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c))) * r ^ k
  have hRpos (j : ℕ) : 0 < ((j : ℝ) + 1) * r := by positivity
  have hRge (j : ℕ) : r ≤ ((j : ℝ) + 1) * r := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hV (j : ℕ) : μ.real (shell x r j) ≤
      A * ((j : ℝ) + 1) ^ n * Real.exp (B * ((j : ℝ) + 1)) * V := by
    calc
      μ.real (shell x r j) ≤ μ.real (Metric.ball x (((j : ℝ) + 1) * r)) :=
        measureReal_mono (shell_subset_ball x r j) (hfinite _ (hRpos j)).ne
      _ ≤ A * ((((j : ℝ) + 1) * r) / r) ^ n *
          Real.exp (B * (((j : ℝ) + 1) * r)) * V := hgrowth _ (hRge j)
      _ ≤ A * ((j : ℝ) + 1) ^ n * Real.exp (B * ((j : ℝ) + 1)) * V := by
        rw [mul_div_cancel_right₀ _ hr.ne']
        gcongr
        nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity)
          (sub_nonneg.mpr hr1)]
  have hK (j : ℕ) : 0 ≤ K j := by dsimp [K]; positivity
  have hD : Summable D := (hsum.mul_left (A ^ 2)).mul_right (r ^ k)
  have hresult := integrable_of_shell_bounds μ x hr hf K D
    (fun j ↦ (measure_mono (shell_subset_ball x r j)).trans_lt (hfinite _ (hRpos j)))
    (fun j y hy ↦ (hgauss y).trans (by
      dsimp [K]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ dist_nonneg hy.2.le k) (div_nonneg hA hpos.le))
        (gaussian_le_on_shell x hr hc hy) (Real.exp_nonneg _)
        (by positivity)))
    (fun j ↦ (mul_le_mul_of_nonneg_left (hV j) (hK j)).trans_eq (by
      dsimp [K, D]
      rw [Real.exp_sub, mul_pow, pow_add]
      have hVne : V ≠ 0 := hpos.ne'
      rw [show -(j : ℝ) ^ 2 / c = -((j : ℝ) ^ 2 / c) by ring, Real.exp_neg]
      field_simp)) hD
  refine ⟨hresult.1, hresult.2.trans_eq ?_⟩
  dsimp [D]
  rw [tsum_mul_right, tsum_mul_left]

end Poincare.MeasureTheory.GaussianMoment
