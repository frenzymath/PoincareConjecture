import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity










noncomputable section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.HarmonicCoordinates


theorem continuous_memLp_restrict_isCompact {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasureOnCompacts μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) (q : ℝ≥0∞) :
    MemLp f q (μ.restrict S) := by
  let : IsFiniteMeasure (μ.restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC (mem_image_of_mem _ hx)


theorem continuous_memLp_restrict_closedBall {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasureOnCompacts μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (z : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (q : ℝ≥0∞) :
    MemLp f q (μ.restrict (Metric.closedBall z ρ)) :=
  continuous_memLp_restrict_isCompact hf (isCompact_closedBall z ρ) q


theorem continuous_memLp_restrict_ball {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasureOnCompacts μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (z : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (q : ℝ≥0∞) :
    MemLp f q (μ.restrict (Metric.ball z ρ)) :=
  (continuous_memLp_restrict_closedBall hf z ρ q).mono_measure
    (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)


theorem eLpNorm_rpow_toReal_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hfn : ∀ x, 0 ≤ f x)
    (q : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (eLpNorm (fun x => f x ^ p) q μ).toReal ^ 2 =
      (eLpNorm f (q * ENNReal.ofReal p) μ).toReal ^ (2 * p) := by
  have heq := eLpNorm_norm_rpow (p := q) (μ := μ) f hp
  simp only [Real.norm_of_nonneg (hfn _)] at heq
  have hreal := congrArg ENNReal.toReal heq
  rw [← ENNReal.toReal_rpow] at hreal
  rw [hreal, ← Real.rpow_mul_natCast ENNReal.toReal_nonneg]
  congr 1
  norm_num
  ring


theorem setIntegral_rpow_sq_eq_eLpNorm_rpow {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasureOnCompacts μ]
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (∫ x in S, (f x ^ p) ^ 2 ∂μ) =
      (eLpNorm f (ENNReal.ofReal (2 * p)) (μ.restrict S)).toReal ^ (2 * p) := by
  have hfp : Continuous (fun x => f x ^ p) := hf.rpow_const (fun _ => Or.inr hp.le)
  rw [← Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral
    (continuous_memLp_restrict_isCompact hfp hS 2)]
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    using eLpNorm_rpow_toReal_sq (μ := μ.restrict S) hfn 2 hp

end PoincareConjecture.HarmonicCoordinates
