import PoincareConjecture.Proofs.Horizon.MeasureTheory.Integral.GaussianMoment.Bounds
import PoincareConjecture.Proofs.Horizon.MeasureTheory.Integral.GaussianMoment.Series








set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Poincare.MeasureTheory.GaussianMoment

universe u



theorem exists_gaussian_first_moment_bound
    (n : ℕ) (A B c : ℝ) (hn : 0 < n) (hA : 1 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
        (μ : Measure X),
        (∀ x : X, ∀ r > 0, 0 < μ (Metric.ball x r) ∧ μ (Metric.ball x r) < ⊤) →
        (∀ x : X, ∀ r R : ℝ, 0 < r → r ≤ R →
          μ.real (Metric.ball x R) ≤
            A * (R / r) ^ n * Real.exp (B * R) * μ.real (Metric.ball x r)) →
        ∀ (x : X) (t : ℝ), 0 < t → t ≤ 1 →
        ∀ h : X → ℝ, Measurable h → (∀ y, 0 ≤ h y) →
          (∀ y, h y ≤ A / μ.real (Metric.ball x (Real.sqrt t)) *
            Real.exp (-dist x y ^ 2 / (c * t))) →
          Integrable h μ ∧ Integrable (fun y ↦ dist x y * h y) μ ∧
            (∫ y, dist x y * h y ∂μ) ≤ C * Real.sqrt t := by
  let C := A ^ 2 * ∑' j : ℕ, ((j : ℝ) + 1) ^ (n + 1) *
    Real.exp (B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c)
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hC : 0 < C := mul_pos (sq_pos_of_pos hA0) (tsum_weight_pos (n + 1) B hc)
  refine ⟨C, hC, ?_⟩
  intro X _ _ _ μ hballs hgrowth x t ht ht1 h hm hnonneg hgauss
  let r := Real.sqrt t
  have hr : 0 < r := Real.sqrt_pos.2 ht
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr ht1
  have hr2 : r ^ 2 = t := Real.sq_sqrt ht.le
  have hball : 0 < μ.real (Metric.ball x r) :=
    ENNReal.toReal_pos (hballs x r hr).1.ne' (hballs x r hr).2.ne
  have hfin : ∀ R > 0, μ (Metric.ball x R) < ⊤ := fun R hR ↦ (hballs x R hR).2
  have hg0 := gaussian_weighted_integrable μ x n 0 hA0.le hB hc hr hr1 hball hfin
    (fun R hR ↦ hgrowth x r R hr hR) (summable_weight (n + 0) B hc)
    hm.aestronglyMeasurable (fun y ↦ by
      simpa only [pow_zero, one_mul, hr2, Real.norm_of_nonneg (hnonneg y)] using hgauss y)
  have hdist : Measurable (fun y : X ↦ dist x y) :=
    (continuous_const.dist continuous_id).measurable
  have hprod : ∀ y, 0 ≤ dist x y * h y := fun y ↦ mul_nonneg dist_nonneg (hnonneg y)
  have hg1 := gaussian_weighted_integrable μ x n 1 hA0.le hB hc hr hr1 hball hfin
    (fun R hR ↦ hgrowth x r R hr hR) (summable_weight (n + 1) B hc)
    (hdist.mul hm).aestronglyMeasurable (fun y ↦ by
      simp only [Pi.mul_apply]
      rw [Real.norm_of_nonneg (hprod y), pow_one, hr2, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hgauss y) dist_nonneg)
  refine ⟨hg0.1, hg1.1, ?_⟩
  simpa only [Pi.mul_apply, Real.norm_of_nonneg (hprod _), pow_one] using hg1.2



theorem tendstoUniformly_gaussian_first_moment
    (n : ℕ) (A B c : ℝ) (hn : 0 < n) (hA : 1 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (hballs : ∀ x : X, ∀ r > 0,
      0 < μ (Metric.ball x r) ∧ μ (Metric.ball x r) < ⊤)
    (hgrowth : ∀ x : X, ∀ r R : ℝ, 0 < r → r ≤ R →
      μ.real (Metric.ball x R) ≤
        A * (R / r) ^ n * Real.exp (B * R) * μ.real (Metric.ball x r))
    (H : ℝ → X → X → ℝ)
    (hH : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : X,
      Measurable (H t x) ∧ (∀ y, 0 ≤ H t x y) ∧
        (∀ y, H t x y ≤ A / μ.real (Metric.ball x (Real.sqrt t)) *
          Real.exp (-dist x y ^ 2 / (c * t)))) :
    TendstoUniformly (fun t x ↦ ∫ y, dist x y * H t x y ∂μ)
      (fun _ ↦ 0) (𝓝[>] 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_first_moment_bound.{u} n A B c hn hA hB hc
  have hlim : Tendsto (fun t : ℝ ↦ C * Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (Real.continuous_sqrt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun t : ℝ ↦ C * Real.sqrt t) (𝓝[>] 0) (𝓝 (C * Real.sqrt 0)))
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (Iio_mem_nhds hε),
    (show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin),
    (show ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 from
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))] with t ht ht0 ht1
  intro x
  obtain ⟨hm, hn0, hg⟩ := hH t ht0 ht1.le x
  have hi := (hbound X μ hballs hgrowth x t ht0 ht1.le (H t x) hm hn0 hg).2.2
  have hi0 : 0 ≤ ∫ y, dist x y * H t x y ∂μ :=
    integral_nonneg (fun y ↦ mul_nonneg dist_nonneg (hn0 y))
  simpa only [dist_zero_left, Real.norm_of_nonneg hi0] using hi.trans_lt ht

end Poincare.MeasureTheory.GaussianMoment
