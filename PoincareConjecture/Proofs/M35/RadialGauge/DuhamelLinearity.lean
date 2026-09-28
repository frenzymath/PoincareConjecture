import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem heatAverage_sub {f g : V → F} (hf : Continuous f) (hg : Continuous g)
    {C D : ℝ} (hfb : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (hgb : ∀ x, (1 + ‖x‖) * ‖g x‖ ≤ D) (t : ℝ) (x : V) :
    heatAverage t (fun y => f y - g y) x = heatAverage t f x - heatAverage t g x :=
  integral_sub (heatAverage_integrable hf hfb t x) (heatAverage_integrable hg hgb t x)

theorem heatGradientKernel_sub {f g : V → F} (hf : Continuous f) (hg : Continuous g)
    {C D : ℝ} (hfb : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (hgb : ∀ x, (1 + ‖x‖) * ‖g x‖ ≤ D) (t : ℝ) (x : V) :
    heatGradientKernel t (fun y => f y - g y) x =
      heatGradientKernel t f x - heatGradientKernel t g x := by
  unfold heatGradientKernel
  rw [← smul_sub]
  congr 1
  rw [← integral_sub (heatGradientKernel_integrable hf hfb t x)
    (heatGradientKernel_integrable hg hgb t x)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by ext v; simp [smul_sub])

theorem heatDuhamel_intervalIntegrable {f : ℝ → V → F} {C t : ℝ} (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    IntervalIntegrable (fun s => heatAverage (t - s) (f s) x) volume 0 t := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIoc 0 t)) := by
    rw [uIoc_of_le ht]
    infer_instance
  rw [intervalIntegrable_iff]
  apply (integrable_const C).mono'
    (heatAverage_time_stronglyMeasurable hfm t x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le ht] at hs
  have hb (z : V) : ‖f s (x + Real.sqrt (2 * (t - s)) • z)‖ ≤ C := by
    have h := hbound s ⟨hs.1.le, hs.2⟩ (x + Real.sqrt (2 * (t - s)) • z)
    nlinarith [mul_nonneg (norm_nonneg (x + Real.sqrt (2 * (t - s)) • z))
      (norm_nonneg (f s (x + Real.sqrt (2 * (t - s)) • z)))]
  simpa [heatAverage] using
    norm_integral_le_of_norm_le_const (μ := stdGaussian V) (Eventually.of_forall hb)

theorem heatDuhamelGradient_intervalIntegrable {f : ℝ → V → F} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s))
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    IntervalIntegrable (fun s => heatGradientKernel (t - s) (f s) x) volume 0 t := by
  let B (s : ℝ) := C * (gaussianFirstMoment (n + 1) * (t - s) ^ (-(1 / 2 : ℝ)) +
    gaussianSecondMoment (n + 1))
  have hB : IntervalIntegrable B volume 0 t :=
    (((intervalIntegrable_backwards_invSqrt t).const_mul (gaussianFirstMoment (n + 1))).add
      intervalIntegrable_const).const_mul C
  rw [intervalIntegrable_iff] at hB ⊢
  apply hB.mono' (heatGradientKernel_time_stronglyMeasurable hfm t x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    (volume.restrict (uIoc 0 t)).ae_ne t] with s hs hne
  rw [uIoc_of_le ht] at hs
  have h := heatGradientKernel_weighted_norm_le_rpow
    (hf s ⟨hs.1.le, hs.2⟩) hC (hbound s ⟨hs.1.le, hs.2⟩)
    (sub_pos.mpr (lt_of_le_of_ne hs.2 hne)) x
  dsimp only [B]
  nlinarith [h, mul_nonneg (norm_nonneg x)
    (norm_nonneg (heatGradientKernel (t - s) (f s) x))]

theorem heatDuhamel_sub {f g : ℝ → V → F} {C D t : ℝ} (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hgm : StronglyMeasurable (Function.uncurry g))
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s)) (hg : ∀ s ∈ Icc 0 t, Continuous (g s))
    (hfb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C)
    (hgb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖g s x‖ ≤ D) (x : V) :
    heatDuhamel (fun s y => f s y - g s y) t x = heatDuhamel f t x - heatDuhamel g t x := by
  unfold heatDuhamel
  rw [← intervalIntegral.integral_sub
    (heatDuhamel_intervalIntegrable ht hfm hfb x) (heatDuhamel_intervalIntegrable ht hgm hgb x)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact heatAverage_sub (hf s hs) (hg s hs) (hfb s hs) (hgb s hs) (t - s) x

theorem heatDuhamelGradient_sub {f g : ℝ → V → F} {C D t : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hgm : StronglyMeasurable (Function.uncurry g))
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s)) (hg : ∀ s ∈ Icc 0 t, Continuous (g s))
    (hfb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C)
    (hgb : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖g s x‖ ≤ D) (x : V) :
    heatDuhamelGradient (fun s y => f s y - g s y) t x =
      heatDuhamelGradient f t x - heatDuhamelGradient g t x := by
  unfold heatDuhamelGradient
  rw [← intervalIntegral.integral_sub
    (heatDuhamelGradient_intervalIntegrable hC ht hfm hf hfb x)
    (heatDuhamelGradient_intervalIntegrable hD ht hgm hg hgb x)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact heatGradientKernel_sub (hf s hs) (hg s hs) (hfb s hs) (hgb s hs) (t - s) x

end PoincareConjecture.M35.RadialGauge
