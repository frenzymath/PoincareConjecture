/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import PoincareLib.Analysis.Parabolic.WeakRegularity.Interior.Producer
import PoincareLib.Analysis.Convolution.RescaledKernel

open MeasureTheory Set
open scoped Topology Convolution ContDiff NNReal
open Poincare.Analysis.Convolution

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem lebesgueConvolution_flux_commutator_eq_integral
    {q u ρ : Spacetime n → ℝ} {r : ℝ} (hr : 0 < r) (v x : Spacetime n)
    (hD : Integrable
      (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y) v * u y))
    (hDq : Integrable
      (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y) v * (q y * u y)))
    (hKq : Integrable
      (fun y => rescaledKernel ρ r (x - y) * (fderiv ℝ q y v * u y))) :
    q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v) u x -
        lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v)
          (fun y => q y * u y) x +
        lebesgueConvolution (rescaledKernel ρ r)
          (fun y => fderiv ℝ q y v * u y) x =
      ∫ y, (fderiv ℝ (rescaledKernel ρ r) (x - y) v *
          (q x - q y) + rescaledKernel ρ r (x - y) * fderiv ℝ q y v) * u y := by
  have hsum : Integrable
      (fun y => (fderiv ℝ (rescaledKernel ρ r) (x - y) v *
          (q x - q y) + rescaledKernel ρ r (x - y) * fderiv ℝ q y v) * u y) := by
    have h0 := ((hD.const_mul (q x)).sub hDq).add hKq
    apply h0.congr
    filter_upwards [] with y
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  simp only [lebesgueConvolution]
  rw [← integral_const_mul, ← integral_sub (hD.const_mul (q x)) hDq, ← integral_add]
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  · exact ((hD.const_mul (q x)).sub hDq)
  · exact hKq

theorem abs_lebesgueConvolution_flux_commutator_le
    {q u ρ : Spacetime n → ℝ} {L : ℝ≥0} {r : ℝ}
    (hq : LipschitzWith L q) (hqreg : ContDiff ℝ 1 q) (hr : 0 < r)
    (v x : Spacetime n)
    (hD : Integrable
      (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y) v * u y))
    (hDq : Integrable
      (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y) v * (q y * u y)))
    (hKq : Integrable
      (fun y => rescaledKernel ρ r (x - y) * (fderiv ℝ q y v * u y)))
    (hmajor : Integrable
      (fun y => ((L : ℝ) * (‖x - y‖ *
          |fderiv ℝ (rescaledKernel ρ r) (x - y) v|) +
        (L : ℝ) * ‖v‖ * |rescaledKernel ρ r (x - y)|) * |u y|)) :
    |q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v) u x -
        lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v)
          (fun y => q y * u y) x +
        lebesgueConvolution (rescaledKernel ρ r)
          (fun y => fderiv ℝ q y v * u y) x| ≤
      ∫ y, ((L : ℝ) * (‖x - y‖ *
          |fderiv ℝ (rescaledKernel ρ r) (x - y) v|) +
        (L : ℝ) * ‖v‖ * |rescaledKernel ρ r (x - y)|) * |u y| := by
  rw [lebesgueConvolution_flux_commutator_eq_integral hr v x hD hDq hKq]
  have hleft : Integrable
      (fun y => (fderiv ℝ (rescaledKernel ρ r) (x - y) v *
          (q x - q y) + rescaledKernel ρ r (x - y) * fderiv ℝ q y v) * u y) := by
    have h0 := ((hD.const_mul (q x)).sub hDq).add hKq
    apply h0.congr
    filter_upwards [] with y
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  calc
    |∫ y, (fderiv ℝ (rescaledKernel ρ r) (x - y) v *
        (q x - q y) + rescaledKernel ρ r (x - y) * fderiv ℝ q y v) * u y| ≤
        ∫ y, |(fderiv ℝ (rescaledKernel ρ r) (x - y) v *
          (q x - q y) + rescaledKernel ρ r (x - y) * fderiv ℝ q y v) * u y| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := fun y =>
          (fderiv ℝ (rescaledKernel ρ r) (x - y) v *
            (q x - q y) + rescaledKernel ρ r (x - y) * fderiv ℝ q y v) * u y))
    _ ≤ ∫ y, ((L : ℝ) * (‖x - y‖ *
          |fderiv ℝ (rescaledKernel ρ r) (x - y) v|) +
        (L : ℝ) * ‖v‖ * |rescaledKernel ρ r (x - y)|) * |u y| := by
      apply integral_mono_ae hleft.norm hmajor
      filter_upwards [] with y
      have hqd : |q x - q y| ≤ (L : ℝ) * ‖x - y‖ := by
        simpa only [dist_eq_norm, Real.norm_eq_abs] using hq.dist_le_mul x y
      have hqv : |fderiv ℝ q y v| ≤ (L : ℝ) * ‖v‖ := by
        simpa only [Real.norm_eq_abs] using ((fderiv ℝ q y).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hq)
            (norm_nonneg v))
      simp only [norm_mul, Real.norm_eq_abs]
      calc
        |(fderiv ℝ (rescaledKernel ρ r) (x - y) v * (q x - q y) +
            rescaledKernel ρ r (x - y) * fderiv ℝ q y v)| * |u y| ≤
            (|fderiv ℝ (rescaledKernel ρ r) (x - y) v * (q x - q y)| +
              |rescaledKernel ρ r (x - y) * fderiv ℝ q y v|) * |u y| :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
        _ ≤ (|fderiv ℝ (rescaledKernel ρ r) (x - y) v| *
              ((L : ℝ) * ‖x - y‖) + |rescaledKernel ρ r (x - y)| *
                ((L : ℝ) * ‖v‖)) * |u y| := by
          apply mul_le_mul_of_nonneg_right (add_le_add ?_ ?_) (abs_nonneg _)
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hqd (abs_nonneg _)
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hqv (abs_nonneg _)
        _ = ((L : ℝ) * (‖x - y‖ *
            |fderiv ℝ (rescaledKernel ρ r) (x - y) v|) +
          (L : ℝ) * ‖v‖ * |rescaledKernel ρ r (x - y)|) * |u y| := by ring

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

/-!
## Informal proof

The pointwise commutator estimate is an order estimate.  If its nonnegative
majorant belongs to (L^2), then monotonicity of the (L^2) seminorm transfers
that membership to the actual commutator.  This consumer keeps every
convolution in the expression explicit; the independent (L^1*L^2\to L^2)
Young estimate supplies the majorant hypothesis in the parabolic induction.

## Proposed formal statements

```lean
theorem memLp_of_abs_le_of_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {c g : α → ℝ} (hc : AEStronglyMeasurable c μ)
    (hcg : ∀ᵐ x ∂μ, |c x| ≤ g x) (hg : MemLp g 2 μ) :
    MemLp c 2 μ := by
  exact hg.mono' hc hcg

theorem memLp_lebesgueConvolution_flux_commutator
    {n : ℕ} {q u ρ : Spacetime n → ℝ} {L : ℝ≥0} {r : ℝ}
    (hr : 0 < r) (hq : LipschitzWith L q) (hqreg : ContDiff ℝ 1 q)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hC : AEStronglyMeasurable (fun x =>
      q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x) volume)
    (hg : MemLp (fun x =>
      ∫ y, ((L : ℝ) * (‖x - y‖ *
        |fderiv ℝ (rescaledKernel ρ r) (x - y) (0 : Spacetime n)|) +
        (L : ℝ) * ‖(0 : Spacetime n)‖ *
          |rescaledKernel ρ r (x - y)|) * |u y|) 2 volume)
    (hint : ∀ x,
      Integrable (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y)
        (0 : Spacetime n) * u y))
    (hintq : ∀ x,
      Integrable (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y)
        (0 : Spacetime n) * (q y * u y)))
    (hintρ : ∀ x,
      Integrable (fun y => rescaledKernel ρ r (x - y) *
        (fderiv ℝ q y (0 : Spacetime n) * u y))) :
    MemLp (fun x =>
      q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x) 2 volume := by
  exact memLp_of_abs_le_of_memLp hC hpoint hg
```

## Informal translation

**Proposition.** An almost-everywhere strongly measurable function dominated
in absolute value by an (L^2) function is itself in (L^2).  In particular,
the explicit differentiated coefficient-mollifier flux commutator is in
(L^2) whenever its published pointwise majorant is in (L^2), with the
convolutions defined by the displayed integrability hypotheses.

## Alignment review

- [x] The translation matches the order-theoretic (L^2) consumer and keeps the actual convolution expression and hypotheses explicit.

## Formal proof
 -/

theorem memLp_of_abs_le_of_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {c g : α → ℝ} (hc : AEStronglyMeasurable c μ)
    (hcg : ∀ᵐ x ∂μ, |c x| ≤ g x) (hg : MemLp g 2 μ) :
    MemLp c 2 μ := by
  exact hg.mono' hc hcg

theorem memLp_lebesgueConvolution_flux_commutator
    {n : ℕ} {q u ρ : Spacetime n → ℝ} {L : ℝ≥0} {r : ℝ}
    (hr : 0 < r) (hq : LipschitzWith L q) (hqreg : ContDiff ℝ 1 q)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hC : AEStronglyMeasurable (fun x =>
      q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x) volume)
    (hg : MemLp (fun x =>
      ∫ y, ((L : ℝ) * (‖x - y‖ *
        |fderiv ℝ (rescaledKernel ρ r) (x - y) (0 : Spacetime n)|) +
        (L : ℝ) * ‖(0 : Spacetime n)‖ *
          |rescaledKernel ρ r (x - y)|) * |u y|) 2 volume)
    (hint : ∀ x,
      Integrable (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y)
        (0 : Spacetime n) * u y))
    (hintq : ∀ x,
      Integrable (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y)
        (0 : Spacetime n) * (q y * u y)))
    (hintρ : ∀ x,
      Integrable (fun y => rescaledKernel ρ r (x - y) *
        (fderiv ℝ q y (0 : Spacetime n) * u y)))
    (hpoint : ∀ᵐ x ∂volume, |(q x * lebesgueConvolution
      (fun y => fderiv ℝ (rescaledKernel ρ r) y (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x)| ≤
      ∫ y, ((L : ℝ) * (‖x - y‖ *
        |fderiv ℝ (rescaledKernel ρ r) (x - y) (0 : Spacetime n)|) +
        (L : ℝ) * ‖(0 : Spacetime n)‖ *
          |rescaledKernel ρ r (x - y)|) * |u y|) :
    MemLp (fun x =>
      q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x) 2 volume := by
  exact memLp_of_abs_le_of_memLp hC hpoint hg

/-! The pointwise estimate itself supplies the domination used by the
`MemLp` consumer; callers need only prove integrability of the displayed
convolution majorant, rather than pass a duplicate a.e. inequality. -/
theorem memLp_lebesgueConvolution_flux_commutator_of_integrable_majorant
    {n : ℕ} {q u ρ : Spacetime n → ℝ} {L : ℝ≥0} {r : ℝ}
    (hr : 0 < r) (hq : LipschitzWith L q) (hqreg : ContDiff ℝ 1 q)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hC : AEStronglyMeasurable (fun x =>
      q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x) volume)
    (hg : MemLp (fun x =>
      ∫ y, ((L : ℝ) * (‖x - y‖ *
        |fderiv ℝ (rescaledKernel ρ r) (x - y) (0 : Spacetime n)|) +
        (L : ℝ) * ‖(0 : Spacetime n)‖ *
          |rescaledKernel ρ r (x - y)|) * |u y|) 2 volume)
    (hint : ∀ x, Integrable (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y)
      (0 : Spacetime n) * u y))
    (hintq : ∀ x, Integrable (fun y => fderiv ℝ (rescaledKernel ρ r) (x - y)
      (0 : Spacetime n) * (q y * u y)))
    (hintρ : ∀ x, Integrable (fun y => rescaledKernel ρ r (x - y) *
      (fderiv ℝ q y (0 : Spacetime n) * u y)))
    (hmajor : ∀ x, Integrable (fun y => ((L : ℝ) * (‖x - y‖ *
      |fderiv ℝ (rescaledKernel ρ r) (x - y) (0 : Spacetime n)|) +
      (L : ℝ) * ‖(0 : Spacetime n)‖ *
        |rescaledKernel ρ r (x - y)|) * |u y|)) :
    MemLp (fun x =>
      q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) u x -
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y
        (0 : Spacetime n)) (fun y => q y * u y) x +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun y => fderiv ℝ q y (0 : Spacetime n) * u y) x) 2 volume := by
  apply memLp_lebesgueConvolution_flux_commutator hr hq hqreg hρ hρc hC hg
    hint hintq hintρ
  filter_upwards [] with x
  exact abs_lebesgueConvolution_flux_commutator_le hq hqreg hr (0 : Spacetime n) x
    (hint x) (hintq x) (hintρ x) (hmajor x)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical

