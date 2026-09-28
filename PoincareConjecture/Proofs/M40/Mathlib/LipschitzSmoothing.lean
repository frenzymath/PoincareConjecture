import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

open Function Set Filter Metric MeasureTheory ContinuousLinearMap
open scoped Convolution Topology ContDiff NNReal

namespace PoincareConjecture.M40

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

noncomputable def normalizedConvolution (μ : Measure E)
    (φ : ContDiffBump (0 : E)) (f : E → F) : E → F :=
  fun x => (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f : E → F) x

omit [CompleteSpace F] in

theorem normalizedConvolution_contDiff (φ : ContDiffBump (0 : E))
    {f : E → F} (hf : LocallyIntegrable f μ) :
    ContDiff ℝ ∞ (normalizedConvolution μ φ f) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

omit [CompleteSpace F] in

private theorem normalizedConvolution_integrable (φ : ContDiffBump (0 : E))
    {f : E → F} (hf : LocallyIntegrable f μ) (x : E) :
    Integrable (fun t => φ.normed μ t • f (x - t)) μ := by
  exact ((φ.hasCompactSupport_normed.convolutionExists_left
    (lsmul ℝ ℝ) φ.continuous_normed hf) x).integrable

theorem normalizedConvolution_lipschitzOn (φ : ContDiffBump (0 : E))
    {f : E → F} {U s : Set E} {L : ℝ≥0}
    (hf : LocallyIntegrable f μ) (hlip : LipschitzOnWith L f U)
    (hsub : ∀ x ∈ s, ∀ t ∈ ball (0 : E) φ.rOut, x - t ∈ U) :
    LipschitzOnWith L (normalizedConvolution μ φ f) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxi := normalizedConvolution_integrable (μ := μ) φ hf x
  have hyi := normalizedConvolution_integrable (μ := μ) φ hf y
  change dist
    (∫ t, φ.normed μ t • f (x - t) ∂μ)
    (∫ t, φ.normed μ t • f (y - t) ∂μ) ≤ _
  rw [dist_eq_norm, ← integral_sub hxi hyi]
  calc
    ‖∫ t, φ.normed μ t • f (x - t) - φ.normed μ t • f (y - t) ∂μ‖
        ≤ ∫ t, φ.normed μ t * ((L : ℝ) * dist x y) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      apply Eventually.of_forall
      intro t
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
      by_cases ht : t ∈ support (φ.normed μ)
      · apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
        rw [φ.support_normed_eq] at ht
        simpa only [← dist_eq_norm, dist_sub_right] using
          hlip.dist_le_mul (x - t) (hsub x hx t ht) (y - t) (hsub y hy t ht)
      · rw [notMem_support.mp ht, zero_mul, zero_mul]
    _ = (L : ℝ) * dist x y := by
      rw [integral_mul_const, φ.integral_normed, one_mul]

theorem normalizedConvolution_lipschitz (φ : ContDiffBump (0 : E))
    {f : E → F} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (normalizedConvolution μ φ f) := by
  rw [← lipschitzOnWith_univ]
  exact normalizedConvolution_lipschitzOn (U := univ) φ hf.continuous.locallyIntegrable
    hf.lipschitzOnWith (by simp)

theorem normalizedConvolution_dist_le (φ : ContDiffBump (0 : E))
    {f : E → F} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    dist (normalizedConvolution μ φ f x) (f x) ≤ (L : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left hy.le L.coe_nonneg)

theorem normalizedConvolution_norm_fderiv_le (φ : ContDiffBump (0 : E))
    {f : E → F} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    ‖fderiv ℝ (normalizedConvolution μ φ f) x‖ ≤ L :=
  norm_fderiv_le_of_lipschitz ℝ (normalizedConvolution_lipschitz φ hf)

theorem exists_contDiff_lipschitz_approx (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → F} {L : ℝ≥0} (hf : LipschitzWith L f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let r : ℝ := ε / (2 * ((L : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  let φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨normalizedConvolution μ φ f,
    normalizedConvolution_contDiff φ hf.continuous.locallyIntegrable,
    normalizedConvolution_lipschitz φ hf, ?_⟩
  intro x
  apply (normalizedConvolution_dist_le (μ := μ) φ hf x).trans_lt
  change (L : ℝ) * r < ε
  have hden : 0 < 2 * ((L : ℝ) + 1) := by positivity
  have heq : r * (2 * ((L : ℝ) + 1)) = ε := by
    dsimp [r]
    exact div_mul_cancel₀ ε hden.ne'
  nlinarith [L.coe_nonneg]

end PoincareConjecture.M40
