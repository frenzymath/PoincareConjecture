import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.L2Commutator.FluxL2
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.L2Approximation
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Set MeasureTheory
open Poincare.Analysis.Convolution
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

local instance {n : ℕ} : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem kernel_integrable {n : ℕ} {u η : Spacetime n → ℝ}
    (hu : MemLp u 2 volume) (hη : Continuous η) (hηc : HasCompactSupport η)
    (x : Spacetime n) : Integrable (fun y => η (x-y) * u y) volume := by
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (hηc.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hη (hu.locallyIntegrable (by norm_num)) x).integrable_swap

private theorem square_integral {n : ℕ} {u : Spacetime n → ℝ}
    (hu : MemLp u 2 volume) : ‖hu.toLp u‖ ^ 2 = ∫ y, (u y) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with y hy
  simp [hy, pow_two]

theorem exists_uniform_l2_flux_commutator_bound
    {n : ℕ} {q u ρ : Spacetime n → ℝ}
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (hu : MemLp u 2 volume) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (v : Spacetime n) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r →
      let F : Spacetime n → ℝ := fun x =>
        q x * lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v) u x -
          lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v)
            (fun y => q y * u y) x +
          lebesgueConvolution (rescaledKernel ρ r)
            (fun y => fderiv ℝ q y v * u y) x
      MemLp F 2 volume ∧ (∫ x, (F x) ^ 2) ≤ B := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hqc hq (by simp)
  let M : ℝ := (L : ℝ) * ((∫ y, ‖y‖ * |fderiv ℝ ρ y v|) +
    ‖v‖ * ∫ y, |ρ y|)
  have huI : 0 ≤ ∫ y, (u y) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨M ^ 2 * (∫ y, (u y) ^ 2) + 1, by positivity, ?_⟩
  intro r hr
  dsimp only
  let η := rescaledKernel ρ r
  let D : Spacetime n → ℝ := fun y => fderiv ℝ η y v
  let K : Spacetime n → ℝ := fun y =>
    (L : ℝ) * (‖y‖ * |D y|) + (L : ℝ) * ‖v‖ * |η y|
  let F : Spacetime n → ℝ := fun x =>
    q x * lebesgueConvolution D u x - lebesgueConvolution D (fun y => q y * u y) x +
      lebesgueConvolution η (fun y => fderiv ℝ q y v * u y) x
  have hη : ContDiff ℝ ∞ η :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hηc : HasCompactSupport η :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hD : Continuous D := (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport D := hηc.fderiv_apply ℝ v
  have hK : Continuous K :=
    (continuous_const.mul (continuous_norm.mul hD.abs)).add
      (continuous_const.mul hη.continuous.abs)
  have hKc : HasCompactSupport K :=
    (hDc.abs.mul_left.mul_left).add hηc.abs.mul_left
  have hK0 (y : Spacetime n) : 0 ≤ K y := by dsimp only [K]; positivity
  have hqtop : MemLp q ⊤ volume := hq.continuous.memLp_top_of_hasCompactSupport hqc volume
  have hdqtop : MemLp (fun y => fderiv ℝ q y v) ⊤ volume :=
    ((hq.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hqc.fderiv_apply ℝ v) volume
  have hqu : MemLp (fun y => q y * u y) 2 volume := hu.mul' hqtop
  have hdqu : MemLp (fun y => fderiv ℝ q y v * u y) 2 volume := hu.mul' hdqtop
  have hFm : MemLp F 2 volume :=
    (((memLp_lebesgueConvolution hu hD hDc).mul' hqtop).sub
      (memLp_lebesgueConvolution hqu hD hDc)).add
      (memLp_lebesgueConvolution hdqu hη.continuous hηc)
  have hua : MemLp (fun y => |u y|) 2 volume := by
    simpa only [Real.norm_eq_abs] using hu.norm
  have hmajor (x : Spacetime n) : |F x| ≤ lebesgueConvolution K (fun y => |u y|) x :=
    abs_lebesgueConvolution_flux_commutator_le hL (hq.of_le (by simp)) hr v x
      (kernel_integrable hu hD hDc x) (kernel_integrable hqu hD hDc x)
      (kernel_integrable hdqu hη.continuous hηc x) (kernel_integrable hua hK hKc x)
  have hKm : MemLp (lebesgueConvolution K (fun y => |u y|)) 2 volume :=
    memLp_lebesgueConvolution hua hK hKc
  have hmass : (∫ y, ‖K y‖) = M := by
    simp_rw [Real.norm_of_nonneg (hK0 _)]
    have hi1 : Integrable (fun y => (L : ℝ) * (‖y‖ * |D y|)) volume :=
      (continuous_const.mul (continuous_norm.mul hD.abs)).integrable_of_hasCompactSupport
        hDc.abs.mul_left.mul_left
    have hi2 : Integrable (fun y => (L : ℝ) * ‖v‖ * |η y|) volume :=
      (continuous_const.mul hη.continuous.abs).integrable_of_hasCompactSupport hηc.abs.mul_left
    rw [show K = fun y => (L : ℝ) * (‖y‖ * |D y|) +
      (L : ℝ) * ‖v‖ * |η y| from rfl, integral_add hi1 hi2]
    simp only [integral_const_mul]
    have hmom := integral_firstMoment_fderiv_rescaledKernel volume
      (hρ.differentiable (by simp)) hr v
    have habs : (∫ y, |η y|) = ∫ y, |ρ y| := by
      have he : (fun y => |η y|) = rescaledKernel (fun y => |ρ y|) r := by
        funext y
        simp only [η, rescaledKernel, abs_mul, abs_inv, abs_pow, abs_of_pos hr]
      rw [he, integral_rescaledKernel volume _ hr]
    change (L : ℝ) * (∫ y, ‖y‖ * |fderiv ℝ (rescaledKernel ρ r) y v|) +
      (L : ℝ) * ‖v‖ * (∫ y, |η y|) = M
    rw [hmom, habs]
    dsimp only [M]
    ring
  have hYoung := norm_toLp_lebesgueConvolution_le hua hK hKc
  rw [hmass] at hYoung
  have hsq := mul_self_le_mul_self (norm_nonneg _) hYoung
  simp only [← pow_two, mul_pow, square_integral hKm, square_integral hua, sq_abs] at hsq
  refine ⟨hFm, ?_⟩
  have hcompare : (∫ y, (F y) ^ 2) ≤
      ∫ y, (lebesgueConvolution K (fun y => |u y|) y) ^ 2 := by
    apply integral_mono hFm.integrable_sq hKm.integrable_sq
    intro y
    have hm := hmajor y
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg (F y)) hm
  exact hcompare.trans (hsq.trans (by linarith))

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
