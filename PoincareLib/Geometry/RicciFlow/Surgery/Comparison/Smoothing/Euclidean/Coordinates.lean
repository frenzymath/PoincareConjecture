import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Euclidean.Approximation
/-!
# Convolution estimates in fixed tangent norms

The local smoothing estimate must be applied in the actual source and target
tangent norms at the point where the derivative is estimated. A fixed linear
target transformation commutes with convolution. Consequently translated
finite differences measured in those norms give the same bound for the
smoothed differential, without an almost-everywhere differentiability
argument. This is the quantitative local step in the SurgeryComparison.Transport smoothing
obligation following Morgan--Tian Claim 18.22, printed p. 433.
-/

set_option autoImplicit false

open Function Set Filter Metric MeasureTheory ContinuousLinearMap
open scoped Convolution Topology ContDiff NNReal

namespace PoincareMT.SurgeryComparison.Transport

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A fixed linear change of target coordinates commutes with normalized
convolution. The equality preserves the operator itself, not just a bound
by the norm of the coordinate change. SurgeryComparison.Transport quantitative smoothing,
Morgan--Tian Claim 18.22, p. 433. -/
theorem normalizedConvolution_map (φ : ContDiffBump (0 : E))
    (B : F →L[ℝ] G) {f : E → F} (hf : LocallyIntegrable f μ) (x : E) :
    B (normalizedConvolution μ φ f x) =
      normalizedConvolution μ φ (B ∘ f) x := by
  have hi : Integrable (fun t => φ.normed μ t • f (x - t)) μ :=
    ((φ.hasCompactSupport_normed.convolutionExists_left
      (lsmul ℝ ℝ) φ.continuous_normed hf) x).integrable
  change B (∫ t, φ.normed μ t • f (x - t) ∂μ) =
    ∫ t, φ.normed μ t • B (f (x - t)) ∂μ
  rw [← B.integral_comp_comm hi]
  simp only [map_smul]

/-- If all translates inside the mollifier support obey a bound in fixed
source and target norms, the convolution obeys that same bound. The source
coordinate map `a` need not be an isometry, and the proof does not replace
`B` by its operator norm. SurgeryComparison.Transport quantitative smoothing, Morgan--Tian
Claim 18.22, p. 433. -/
theorem normalizedConvolution_lipschitzOn_of_translated_bound
    {X : Type*} [PseudoMetricSpace X] (φ : ContDiffBump (0 : E))
    (a : X → E) (B : F →L[ℝ] G) {f : E → F} {s : Set X} {L : ℝ≥0}
    (hf : LocallyIntegrable f μ)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, ∀ t ∈ ball (0 : E) φ.rOut,
      dist (B (f (a x - t))) (B (f (a y - t))) ≤ (L : ℝ) * dist x y) :
    LipschitzOnWith L (fun x => B (normalizedConvolution μ φ f (a x))) s := by
  have hi (x : X) : Integrable (fun t => φ.normed μ t • B (f (a x - t))) μ := by
    have hi' : Integrable (fun t => φ.normed μ t • f (a x - t)) μ :=
      ((φ.hasCompactSupport_normed.convolutionExists_left
        (lsmul ℝ ℝ) φ.continuous_normed hf) (a x)).integrable
    simpa only [lsmul_apply, map_smul] using B.integrable_comp hi'
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [normalizedConvolution_map φ B hf, normalizedConvolution_map φ B hf]
  change dist
    (∫ t, φ.normed μ t • B (f (a x - t)) ∂μ)
    (∫ t, φ.normed μ t • B (f (a y - t)) ∂μ) ≤ _
  rw [dist_eq_norm, ← integral_sub (hi x) (hi y)]
  calc
    ‖∫ t, φ.normed μ t • B (f (a x - t)) -
        φ.normed μ t • B (f (a y - t)) ∂μ‖
        ≤ ∫ t, φ.normed μ t * ((L : ℝ) * dist x y) ∂μ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      apply Eventually.of_forall
      intro t
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
      by_cases ht : t ∈ support (φ.normed μ)
      · apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
        rw [φ.support_normed_eq] at ht
        simpa only [← dist_eq_norm] using hbound x hx y hy t ht
      · rw [notMem_support.mp ht, zero_mul, zero_mul]
    _ = (L : ℝ) * dist x y := by
      rw [integral_mul_const, φ.integral_normed, one_mul]

/-- Pass the translated finite-difference estimate to a differential norm.
The caller uses `a` and `B` to identify coordinate vectors with the tangent
norms at the point under consideration. SurgeryComparison.Transport quantitative smoothing,
Morgan--Tian Claim 18.22, p. 433. -/
theorem normalizedConvolution_norm_fderiv_le_of_translated_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : ContDiffBump (0 : E)) (a : V → E) (B : F →L[ℝ] G)
    {f : E → F} {s : Set V} {L : ℝ≥0} {x : V}
    (hf : LocallyIntegrable f μ) (hs : s ∈ 𝓝 x)
    (hbound : ∀ z ∈ s, ∀ y ∈ s, ∀ t ∈ ball (0 : E) φ.rOut,
      dist (B (f (a z - t))) (B (f (a y - t))) ≤ (L : ℝ) * dist z y) :
    ‖fderiv ℝ (fun z => B (normalizedConvolution μ φ f (a z))) x‖ ≤ L :=
  norm_fderiv_le_of_lipschitzOn ℝ hs
    (normalizedConvolution_lipschitzOn_of_translated_bound φ a B hf hbound)

end PoincareMT.SurgeryComparison.Transport
