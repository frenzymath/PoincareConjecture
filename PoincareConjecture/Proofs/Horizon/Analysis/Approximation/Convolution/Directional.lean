import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Semiconcavity
import Mathlib.Analysis.Calculus.Deriv.Slope









set_option autoImplicit false

open Set Filter ContinuousLinearMap MeasureTheory
open scoped Convolution NNReal ContDiff Topology

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]



theorem normed_convolution_increment_le {f : E → ℝ} (hf : Continuous f)
    (φ : ContDiffBump (0 : E)) {x v : E} {t c : ℝ}
    (hbound : ∀ y ∈ Metric.ball x φ.rOut, f (y + t • v) - f y ≤ c) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) (x + t • v) -
      (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x ≤ c := by
  have hi : ConvolutionExists (φ.normed μ) f (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable hf
  simp only [ConvolutionExists, ConvolutionExistsAt, lsmul_apply, smul_eq_mul] at hi
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_sub (hi _) (hi _)]
  calc
    _ ≤ ∫ z, φ.normed μ z * c ∂μ := by
      apply integral_mono ((hi _).sub (hi _)) (φ.integrable_normed.mul_const _)
      intro z
      dsimp only [Pi.sub_apply]
      rw [← mul_sub]
      by_cases hz : z ∈ Metric.ball (0 : E) φ.rOut
      · apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
        have hy : x - z ∈ Metric.ball x φ.rOut := by
          simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left,
            norm_neg, sub_zero] using hz
        have heq : x + t • v - z = (x - z) + t • v := by abel
        simpa only [heq] using hbound (x - z) hy
      · have hzero : φ.normed μ z = 0 := by
          by_contra hn
          apply hz
          rw [← φ.support_normed_eq (μ := μ)]
          exact hn
        simp only [hzero, zero_mul, le_refl]
    _ = c := by rw [integral_mul_const, φ.integral_normed, one_mul]



theorem fderiv_normed_convolution_apply_le_of_increment_bound
    {f : E → ℝ} (hf : Continuous f) (φ : ContDiffBump (0 : E))
    {x v : E} {c r : ℝ} (hr : 0 < r)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) r, ∀ y ∈ Metric.ball x φ.rOut,
      f (y + t • v) - f y ≤ t * c) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x v ≤ c := by
  let u := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hu : ContDiff ℝ ∞ u :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _
      φ.contDiff_normed hf.locallyIntegrable
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hderiv : HasDerivAt (fun t : ℝ => u (x + t • v)) (fderiv ℝ u x v) 0 := by
    simpa only [Function.comp_def] using
      (hu.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
        (by simp only [zero_smul, add_zero])
  apply le_of_tendsto hderiv.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with t ht htr
  have ht0 : 0 < t := ht
  have hinc := normed_convolution_increment_le μ hf φ (hbound t ⟨ht0, htr⟩)
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  exact (inv_mul_le_iff₀ ht0).mpr hinc


theorem fderiv_normed_convolution_apply_le {f : E → ℝ} (hf : Continuous f)
    (φ : ContDiffBump (0 : E)) {v : E} {c : ℝ}
    (hbound : ∀ y : E, ∀ t : ℝ, 0 ≤ t → f (y + t • v) - f y ≤ t * c)
    (x : E) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x v ≤ c :=
  fderiv_normed_convolution_apply_le_of_increment_bound μ hf φ zero_lt_one
    (fun t ht y _ => hbound y t ht.1.le)

end Poincare

namespace Poincare



theorem exists_contDiff_lipschitz_semiconcave_directional_approx
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {f : E → ℝ} {K : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith K f)
    (hconc : ConcaveOn ℝ univ (fun x => f x - C * ‖x‖ ^ 2 / 2))
    (v : ι → E) (c : ι → ℝ)
    (hbound : ∀ i y t, 0 ≤ t → f (y + t • v i) - f y ≤ t * c i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) ≤ ε) ∧
      ConcaveOn ℝ univ (fun x => u x - C * ‖x‖ ^ 2 / 2) ∧
      ∀ i x, fderiv ℝ u x (v i) ≤ c i := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let r : ℝ := ε / (K + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨φ.normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_,
    lipschitzWith_normed_convolution μ hf φ, ?_,
    concaveOn_sub_norm_sq_normed_convolution μ hf.continuous hconc φ, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _
      φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply (dist_normed_convolution_le_radius μ hf φ x).trans
    change (K : ℝ) * r ≤ ε
    have heq : r * (K + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  · intro i x
    exact fderiv_normed_convolution_apply_le μ hf.continuous φ (hbound i) x

end Poincare
