import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.MollifiedForcingBounds

open Set Filter MeasureTheory ContinuousLinearMap
open Poincare.Analysis.Convolution
open scoped ContDiff Topology Convolution

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

local instance {n : ℕ} : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem tendstoUniformly_mollifiedValue
    {n : ℕ} {u ρ : Spacetime n → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hmass : (∫ y, ρ y) = 1)
    {r : ℕ → ℝ} (hr : ∀ m, 0 < r m)
    (hlim : Tendsto r atTop (𝓝 0)) :
    TendstoUniformly (fun m => mollifiedValue u ρ (r m)) u atTop := by
  have huc' : UniformContinuous u := huc.uniformContinuous_of_continuous hu
  let M : ℝ := ∫ y, ‖ρ y‖
  have hM : 0 ≤ M := integral_nonneg (fun y => norm_nonneg _)
  obtain ⟨R, hRpos, hR⟩ := hρc.isBounded.exists_pos_norm_lt
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hmodpos : 0 < ε / (2 * (M + 1)) := by positivity
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuous_iff.mp huc' (ε / (2 * (M + 1))) hmodpos
  filter_upwards [hlim.eventually_lt_const (div_pos hδ hRpos)] with m hm
  intro z
  have hscale : ContDiff ℝ ∞ (rescaledKernel ρ (r m)) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul (r m)⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ (r m)) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 (r m)⁻¹ (inv_ne_zero (hr m).ne')))).mul_left
  have hsupport : Function.support (rescaledKernel ρ (r m)) ⊆
      Metric.ball (0 : Spacetime n) (r m * R) := by
    intro y hy
    have hρy : ρ ((r m)⁻¹ • y) ≠ 0 := by
      intro he
      exact hy (by simp [rescaledKernel, he])
    have hb := hR _ (subset_tsupport ρ hρy)
    have hn : ‖(r m)⁻¹ • y‖ = (r m)⁻¹ * ‖y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos (hr m)]
    rw [hn] at hb
    have hb' := mul_lt_mul_of_pos_left hb (hr m)
    simpa [mem_ball_zero_iff, ← mul_assoc, (hr m).ne'] using hb'
  have habs : (∫ y, ‖rescaledKernel ρ (r m) y‖) = M := by
    have he : (fun y => ‖rescaledKernel ρ (r m) y‖) =
        rescaledKernel (fun y => ‖ρ y‖) (r m) := by
      funext y
      simp only [rescaledKernel, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow,
        abs_of_pos (hr m)]
    rw [he, integral_rescaledKernel volume _ (hr m)]
  have hd := dist_convolution_le' (μ := volume) (lsmul ℝ ℝ) hmodpos.le
    (hscale.continuous.integrable_of_hasCompactSupport hcompact) hsupport
    hu.aestronglyMeasurable (x₀ := z) (z₀ := u z)
    (fun y hy => (hmod ((Metric.mem_ball.mp hy).trans
      ((lt_div_iff₀ hRpos).mp hm))).le)
  simp only [lsmul_apply, smul_eq_mul, integral_mul_const,
    integral_rescaledKernel volume ρ (hr m), hmass, one_mul, habs] at hd
  have hb : (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * M) * (ε / (2 * (M + 1))) ≤
      M * (ε / (2 * (M + 1))) := by
    apply mul_le_mul_of_nonneg_right _ hmodpos.le
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (opNorm_lsmul_le (𝕜 := ℝ) (R := ℝ) (E := ℝ)) hM
  have hsmall : M * (ε / (2 * (M + 1))) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * (M + 1))]
    nlinarith
  rw [dist_comm]
  simpa only [mollifiedValue, lebesgueConvolution_eq_convolution] using
    hd.trans_lt (hb.trans_lt hsmall)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
