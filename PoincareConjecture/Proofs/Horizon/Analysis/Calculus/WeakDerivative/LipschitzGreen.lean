import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal

namespace Poincare.Analysis.WeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ae_differentiableAt_of_lipschitzOn
    (μ : Measure E) [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzOnWith C f U) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  filter_upwards [hF.ae_differentiableAt (μ := μ)] with x hx hxU
  exact hx.congr_of_eventuallyEq (heq.eventuallyEq_of_mem (hU.mem_nhds hxU))

theorem integral_mul_fderiv_eq_neg
    (μ : Measure E) [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    {f w : E → ℝ} {C : ℝ≥0} (hf : LipschitzOnWith C f U)
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ U) (v : E) :
    Integrable (fun x => fderiv ℝ f x v * w x) μ ∧
    Integrable (fun x => f x * fderiv ℝ w x v) μ ∧
    (∫ x, f x * fderiv ℝ w x v ∂μ) =
      -∫ x, fderiv ℝ f x v * w x ∂μ := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hderiv : ∀ x ∈ U, fderiv ℝ f x = fderiv ℝ F x := by
    intro x hx
    exact (heq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq
  have hpair : (fun x => fderiv ℝ f x v * w x) =ᵐ[μ]
      (fun x => lineDeriv ℝ F x v * w x) := by
    filter_upwards [hF.ae_differentiableAt (μ := μ)] with x hx
    by_cases hxw : x ∈ tsupport w
    · rw [hderiv x (hwU hxw), hx.lineDeriv_eq_fderiv]
    · simp [image_eq_zero_of_notMem_tsupport hxw]
  have hwp : (fun x => f x * fderiv ℝ w x v) =
      (fun x => F x * fderiv ℝ w x v) := by
    funext x
    by_cases hxw : x ∈ tsupport w
    · rw [heq (hwU hxw)]
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hx => hxw (tsupport_fderiv_apply_subset ℝ v hx)), mul_zero, mul_zero]
  have hdw : ContDiff ℝ ∞ (fun x => fderiv ℝ w x v) :=
    (hw.fderiv_right (by simp)).clm_apply contDiff_const
  have hwi := hw.continuous.integrable_of_hasCompactSupport (μ := μ) hwc
  have hpairInt : Integrable (fun x => lineDeriv ℝ F x v * w x) μ :=
    hwi.mul_of_top_right (hF.memLp_lineDeriv _)
  have hwpInt : Integrable (fun x => F x * fderiv ℝ w x v) μ :=
    (hF.continuous.mul hdw.continuous).integrable_of_hasCompactSupport
      (hwc.fderiv_apply ℝ v).mul_left
  refine ⟨hpairInt.congr hpair.symm, hwp ▸ hwpInt, ?_⟩
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hwc hw (by simp)
  have hibp := hF.integral_lineDeriv_mul_eq (μ := μ) hD hwc v
  simp_rw [(hw.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    map_neg, neg_mul, integral_neg] at hibp
  rw [hwp, integral_congr_ae hpair]
  simpa only [mul_comm, neg_neg] using congrArg Neg.neg hibp.symm

theorem integral_mul_sum_fderiv_eq_neg
    (μ : Measure E) [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzOnWith C f U)
    {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → E → ℝ)
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hwc : ∀ i, HasCompactSupport (w i))
    (hwU : ∀ i, tsupport (w i) ⊆ U) :
    Integrable (fun x => ∑ i, fderiv ℝ f x (v i) * w i x) μ ∧
    Integrable (fun x => f x * ∑ i, fderiv ℝ (w i) x (v i)) μ ∧
    (∫ x, f x * ∑ i, fderiv ℝ (w i) x (v i) ∂μ) =
      -∫ x, ∑ i, fderiv ℝ f x (v i) * w i x ∂μ := by
  classical
  have hscalar i := integral_mul_fderiv_eq_neg μ hU hf (hw i) (hwc i) (hwU i) (v i)
  simp_rw [Finset.mul_sum]
  refine ⟨integrable_finsetSum _ (fun i _ => (hscalar i).1),
    integrable_finsetSum _ (fun i _ => (hscalar i).2.1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hscalar i).2.1),
    integral_finsetSum _ (fun i _ => (hscalar i).1), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (hscalar i).2.2

end Poincare.Analysis.WeakDerivative
