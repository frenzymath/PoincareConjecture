import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Producer
import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.RescaledKernel
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
