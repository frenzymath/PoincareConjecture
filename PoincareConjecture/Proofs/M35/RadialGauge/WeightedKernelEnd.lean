import PoincareConjecture.Proofs.M35.RadialGauge.HeatWeight
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {A F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

omit [NormedSpace ℝ F] in

theorem weighted_gaussian_moment_vanishes_uniformly
    {f : A → V → F} {C S : ℝ} (hS : 0 ≤ S)
    (hf : ∀ a, Continuous (f a))
    (hbound : ∀ a x, (1 + ‖x‖) * ‖f a x‖ ≤ C)
    (hend : ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ a x,
      R ≤ ‖x‖ → (1 + ‖x‖) * ‖f a x‖ < e)
    {q : V → ℝ} (hq : ∀ z, 0 ≤ q z)
    (hqi : Integrable q (stdGaussian V))
    (hqzi : Integrable (fun z => q z * ‖z‖) (stdGaussian V)) :
    ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ a b, b ∈ Icc 0 S → ∀ x, R ≤ ‖x‖ →
      (∫ z, q z * ((1 + ‖x‖) * ‖f a (x + b • z)‖) ∂stdGaussian V) < e := by
  classical
  intro e he
  by_contra hfail
  push Not at hfail
  choose a b hb x hx hlarge using fun k : ℕ => hfail (k : ℝ)
  let J (k : ℕ) (z : V) := q z * ((1 + ‖x k‖) * ‖f (a k) (x k + b k • z)‖)
  let M (z : V) := C * q z * (1 + S * ‖z‖)
  have hMi : Integrable M (stdGaussian V) := by
    have heq : M = fun z => C * q z + (C * S) * (q z * ‖z‖) := by
      funext z
      dsimp [M]
      ring
    rw [heq]
    exact (hqi.const_mul C).add (hqzi.const_mul (C * S))
  have hJmeas (k : ℕ) : AEStronglyMeasurable (J k) (stdGaussian V) :=
    hqi.aestronglyMeasurable.mul
      ((((hf (a k)).comp (by fun_prop)).norm.const_mul (1 + ‖x k‖)).aestronglyMeasurable)
  have hweight (k : ℕ) (z : V) :
      (1 + ‖x k‖) * ‖f (a k) (x k + b k • z)‖ ≤
        (1 + S * ‖z‖) * ((1 + ‖x k + b k • z‖) * ‖f (a k) (x k + b k • z)‖) := by
    have h := mul_le_mul_of_nonneg_right (radial_weight_translation (x k) z (hb k).1)
      (norm_nonneg (f (a k) (x k + b k • z)))
    have hs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb k).2 (norm_nonneg z))
      (mul_nonneg (show 0 ≤ 1 + ‖x k + b k • z‖ by positivity)
        (norm_nonneg (f (a k) (x k + b k • z))))
    nlinarith only [h, hs]
  have hJbound (k : ℕ) : ∀ᵐ z ∂stdGaussian V, ‖J k z‖ ≤ M z := by
    refine Eventually.of_forall (fun z => ?_)
    have h := (hweight k z).trans (mul_le_mul_of_nonneg_left
      (hbound (a k) (x k + b k • z)) (by positivity))
    have hqmul := mul_le_mul_of_nonneg_left h (hq z)
    dsimp only [J, M]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq z) (by positivity))]
    nlinarith only [hqmul]
  have hlim (z : V) : Tendsto (fun k => J k z) atTop (𝓝 0) := by
    have hynorm : Tendsto (fun k => ‖x k + b k • z‖) atTop atTop := by
      apply tendsto_atTop.mpr
      intro R
      have hn : ∀ᶠ k : ℕ in atTop, R + S * ‖z‖ ≤ (k : ℝ) :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
      filter_upwards [hn] with k hk
      have hn := norm_sub_le (x k + b k • z) (b k • z)
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb k).1] at hn
      have hs := mul_le_mul_of_nonneg_right (hb k).2 (norm_nonneg z)
      linarith [hx k]
    have hsource : Tendsto
        (fun k => (1 + ‖x k + b k • z‖) * ‖f (a k) (x k + b k • z)‖) atTop (𝓝 0) := by
      apply tendsto_order.mpr
      constructor
      · intro r hr
        exact Eventually.of_forall (fun k => lt_of_lt_of_le hr (by positivity))
      · intro d hd
        obtain ⟨R, hR⟩ := hend d hd
        filter_upwards [hynorm.eventually (eventually_ge_atTop R)] with k hk
        exact hR (a k) (x k + b k • z) hk
    apply squeeze_zero (fun k => show 0 ≤ J k z by
      exact mul_nonneg (hq z) (mul_nonneg (by positivity) (norm_nonneg _)))
      (fun k => mul_le_mul_of_nonneg_left (hweight k z) (hq z))
    simpa only [mul_zero] using (hsource.const_mul (1 + S * ‖z‖)).const_mul (q z)
  have hint : Tendsto (fun k => ∫ z, J k z ∂stdGaussian V) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence M hJmeas hMi
      hJbound (Eventually.of_forall hlim)
  obtain ⟨k, hk⟩ := ((tendsto_order.mp hint).2 e he).exists
  exact (not_lt_of_ge (hlarge k)) hk

end PoincareConjecture.M35.RadialGauge
