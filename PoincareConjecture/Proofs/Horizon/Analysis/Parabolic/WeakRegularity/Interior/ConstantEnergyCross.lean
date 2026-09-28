




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.Basic









open MeasureTheory Set
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem integrable_contDiff_compactSupport {q : Spacetime n → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) : Integrable q := by
  apply (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport q)).mp
  exact hq.continuous.continuousOn.integrableOn_compact hqc.isCompact

private theorem integrable_fderiv_contDiff_compactSupport
    {q : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (w : Spacetime n) :
    Integrable (fun z => fderiv ℝ q z w) := by
  have hq' : ContDiff ℝ ∞ (fun z => fderiv ℝ q z w) :=
    (hq.fderiv_right (by simp)).clm_apply contDiff_const
  have hqc' : HasCompactSupport (fun z => fderiv ℝ q z w) :=
    hqc.fderiv_apply ℝ w
  apply (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport _)).mp
  exact hq'.continuous.continuousOn.integrableOn_compact hqc'.isCompact



theorem integral_fderiv_eq_zero_of_contDiff_compactSupport
    {q : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (w : Spacetime n) :
    (∫ z, fderiv ℝ q z w) = 0 := by
  have hqI : Integrable q := integrable_contDiff_compactSupport hq hqc
  have hq'I : Integrable (fun z => fderiv ℝ q z w) :=
    integrable_fderiv_contDiff_compactSupport hq hqc w
  have hzero : (fun z => fderiv ℝ (fun _ : Spacetime n => (1 : ℝ)) z w * q z) =
      (0 : Spacetime n → ℝ) := by
    funext z
    simp [fderiv_const]
  have hconstI : Integrable
      (fun z => fderiv ℝ (fun _ : Spacetime n => (1 : ℝ)) z w * q z) := by
    have hz : Integrable (fun _ : Spacetime n => (0 : ℝ)) := by
      exact integrable_zero (Spacetime n) ℝ (volume : Measure (Spacetime n))
    rw [hzero]
    exact hz
  have hprodI : Integrable
      (fun z => (1 : ℝ) * fderiv ℝ q z w) := by simpa using hq'I
  have hres := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Spacetime n)))
    (f := fun _ : Spacetime n => (1 : ℝ)) (g := q) (v := w)
    hconstI hprodI (by simpa using hqI)
    (fun _ _ => differentiableAt_const (c := (1 : ℝ)))
    (fun z _ => hq.differentiable (by simp) z)
  rw [hzero] at hres
  have hzint : integral (volume : Measure (Spacetime n)) (0 : Spacetime n → ℝ) = 0 :=
    MeasureTheory.integral_zero (Spacetime n) ℝ
  rw [hzint, neg_zero] at hres
  simpa only [one_mul] using hres

theorem integral_spatialDeriv_eq_zero_of_contDiff_compactSupport
    {q : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (i : Fin n) :
    (∫ z, spatialDeriv i q z) = 0 :=
  integral_fderiv_eq_zero_of_contDiff_compactSupport hq hqc
    (spatialDirection i)

theorem integral_timeDeriv_eq_zero_of_contDiff_compactSupport
    {q : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    (∫ z, timeDeriv q z) = 0 :=
  integral_fderiv_eq_zero_of_contDiff_compactSupport hq hqc (0, 1)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
