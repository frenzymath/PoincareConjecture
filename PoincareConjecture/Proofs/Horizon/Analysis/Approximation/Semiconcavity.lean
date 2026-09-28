import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity
import Mathlib.Analysis.InnerProductSpace.Basic









set_option autoImplicit false

open Set ContinuousLinearMap MeasureTheory
open scoped Convolution NNReal ContDiff

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem concaveOn_sub_norm_sq_translate {f : E → ℝ} {C : ℝ} {s T : Set E}
    (hf : ConcaveOn ℝ T (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (hs : Convex ℝ s) (t : E) (hsub : ∀ x ∈ s, x - t ∈ T) :
    ConcaveOn ℝ s (fun x => f (x - t) - C * ‖x‖ ^ 2 / 2) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 (hsub x hx) (hsub y hy) ha hb hab
  have ht : a • (x - t) + b • (y - t) = (a • x + b • y) - t := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  rw [ht] at h
  simp only [norm_sub_sq_real, inner_add_left, real_inner_smul_left,
    smul_eq_mul] at h ⊢
  have hb' : b = 1 - a := by linarith
  rw [hb'] at h ⊢
  nlinarith [h]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]



theorem concaveOn_sub_norm_sq_normed_convolution_on
    {f : E → ℝ} {C : ℝ} {s T : Set E} (hs : Convex ℝ s)
    (hf : Continuous f)
    (hconc : ConcaveOn ℝ T (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (φ : ContDiffBump (0 : E))
    (hsub : ∀ t ∈ Metric.ball (0 : E) φ.rOut, ∀ x ∈ s, x - t ∈ T) :
    ConcaveOn ℝ s
      (fun x => (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x - C * ‖x‖ ^ 2 / 2) := by
  have hi : ConvolutionExists (φ.normed μ) f (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable hf
  simp only [ConvolutionExists, ConvolutionExistsAt, lsmul_apply, smul_eq_mul] at hi
  have hc : ConcaveOn ℝ s
      (fun x => ∫ t, φ.normed μ t * (f (x - t) - C * ‖x‖ ^ 2 / 2) ∂μ) := by
    apply integral_concaveOn_of_integrand_ae hs
    · exact Filter.Eventually.of_forall fun t => by
        by_cases ht : t ∈ Metric.ball (0 : E) φ.rOut
        · simpa only [smul_eq_mul] using
            (concaveOn_sub_norm_sq_translate hconc hs t (hsub t ht)).smul
              (φ.nonneg_normed t)
        · have hz : φ.normed μ t = 0 := by
            by_contra hn
            apply ht
            rw [← φ.support_normed_eq (μ := μ)]
            exact hn
          simpa only [hz, zero_mul] using concaveOn_const (0 : ℝ) hs
    · intro x _
      simp_rw [mul_sub]
      exact (hi x).sub (φ.integrable_normed.mul_const _)
  convert hc using 1
  ext x
  simp only [convolution_def, lsmul_apply, smul_eq_mul, mul_sub]
  rw [integral_sub (hi x) (φ.integrable_normed.mul_const _),
    integral_mul_const, φ.integral_normed, one_mul]


theorem concaveOn_sub_norm_sq_normed_convolution {f : E → ℝ} {C : ℝ}
    (hf : Continuous f)
    (hconc : ConcaveOn ℝ univ (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (φ : ContDiffBump (0 : E)) :
    ConcaveOn ℝ univ
      (fun x => (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x - C * ‖x‖ ^ 2 / 2) :=
  concaveOn_sub_norm_sq_normed_convolution_on μ convex_univ hf hconc φ
    (fun _ _ _ _ => mem_univ _)

end Poincare

namespace Poincare


theorem exists_contDiff_lipschitz_semiconcave_approx
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith K f)
    (hconc : ConcaveOn ℝ univ (fun x => f x - C * ‖x‖ ^ 2 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) ≤ ε) ∧
      ConcaveOn ℝ univ (fun x => u x - C * ‖x‖ ^ 2 / 2) := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let r : ℝ := ε / (K + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨φ.normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_,
    lipschitzWith_normed_convolution μ hf φ, ?_,
    concaveOn_sub_norm_sq_normed_convolution μ hf.continuous hconc φ⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _
      φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply (dist_normed_convolution_le_radius μ hf φ x).trans
    change (K : ℝ) * r ≤ ε
    have heq : r * (K + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith



theorem exists_contDiff_lipschitz_hessian_approx_on_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith K f) {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x => f x - C * ‖x‖ ^ 2 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) ≤ ε) ∧
      ∀ x ∈ Metric.ball x₀ r, ∀ v : E,
        fderiv ℝ (fderiv ℝ u) x v v ≤ C * ‖v‖ ^ 2 := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let ρ : ℝ := min (R - r) (ε / (K + 1))
  have hρ : 0 < ρ := lt_min (sub_pos.mpr hrR) (div_pos hε (by positivity))
  let φ : ContDiffBump (0 : E) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  let u := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hu : ContDiff ℝ ∞ u := φ.hasCompactSupport_normed.contDiff_convolution_left _
    φ.contDiff_normed hf.continuous.locallyIntegrable
  refine ⟨u, hu, lipschitzWith_normed_convolution μ hf φ, ?_, ?_⟩
  · intro x
    apply (dist_normed_convolution_le_radius μ hf φ x).trans
    change (K : ℝ) * ρ ≤ ε
    have hsmall : ρ ≤ ε / (K + 1) := min_le_right _ _
    have hbound := (le_div_iff₀ (show 0 < (K : ℝ) + 1 by positivity)).mp hsmall
    nlinarith [K.coe_nonneg]
  · have hc : ConcaveOn ℝ (Metric.ball x₀ r) (fun x => u x - C * ‖x‖ ^ 2 / 2) := by
      apply concaveOn_sub_norm_sq_normed_convolution_on μ (convex_ball x₀ r)
        hf.continuous hconc φ
      intro t ht x hx
      have ht' : ‖t‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using ht
      have hx' : ‖x - x₀‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hsmall : ρ ≤ R - r := min_le_left _ _
      rw [Metric.mem_ball, dist_eq_norm]
      have heq : x - t - x₀ = (x - x₀) - t := by abel
      rw [heq]
      exact (norm_sub_le _ _).trans_lt (by linarith)
    intro x hx v
    exact Analysis.fderiv_fderiv_le_of_concaveOn_sub_norm_sq
      Metric.isOpen_ball hu.contDiffOn hc hx v



theorem exists_contDiff_hessian_approx_of_lipschitzOn_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    {x₀ : E} {r R : ℝ} (hrR : r < R)
    (hf : LipschitzOnWith K f (Metric.ball x₀ R))
    (hconc : ConcaveOn ℝ (Metric.ball x₀ R) (fun x => f x - C * ‖x‖ ^ 2 / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ Metric.ball x₀ R, dist (u x) (f x) ≤ ε) ∧
      ∀ x ∈ Metric.ball x₀ r, ∀ v : E,
        fderiv ℝ (fderiv ℝ u) x v v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hc : ConcaveOn ℝ (Metric.ball x₀ R)
      (fun x => F x - C * ‖x‖ ^ 2 / 2) :=
    hconc.congr (fun x hx => congrArg (fun z => z - C * ‖x‖ ^ 2 / 2) (heq hx))
  obtain ⟨u, hu, hLu, herr, hess⟩ :=
    exists_contDiff_lipschitz_hessian_approx_on_ball hF hrR hc hε
  exact ⟨u, hu, hLu, fun x hx => by simpa only [heq hx] using herr x, hess⟩

end Poincare
