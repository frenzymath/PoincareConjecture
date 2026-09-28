import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod













noncomputable section
set_option autoImplicit false

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

namespace Poincare.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

private def polarScale : sphere (0 : E) 1 × Ioi (0 : ℝ) → E :=
  fun p => (p.2 : ℝ) • (p.1 : E)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem continuous_polarScale : Continuous (polarScale (E := E)) := by
  unfold polarScale
  fun_prop

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem measurable_polarScale : Measurable (polarScale (E := E)) :=
  continuous_polarScale.measurable

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem polarScale_homeomorphUnitSphereProd
    (x : ({0}ᶜ : Set E)) :
    polarScale (homeomorphUnitSphereProd E x) = (x : E) := by
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
  simp [polarScale, smul_smul, mul_inv_cancel₀ hn]



theorem lintegral_eq_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ ω : sphere (0 : E) 1,
        (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hms : MeasurableSet ({0}ᶜ : Set E) :=
    (measurableSet_singleton (0 : E)).compl
  have step1 : ∫⁻ x, f x ∂μ =
      ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
    rw [lintegral_subtype_comap hms, restrict_compl_singleton]
  have step2 : ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑))
      = ∫⁻ p, f (polarScale p) ∂
        (μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _) (fun p => f (polarScale p))]
    exact lintegral_congr fun x => by
      rw [polarScale_homeomorphUnitSphereProd x]
  have hmeas : Measurable
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p)) :=
    hf.comp measurable_polarScale
  rw [step1, step2, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hinner : Measurable
      (fun t : Ioi (0 : ℝ) => f ((t : ℝ) • (ω : E))) :=
    hf.comp ((continuous_id.smul continuous_const).comp continuous_subtype_val).measurable
  have hdens : Measurable (fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (finrank ℝ E - 1))) := by
    fun_prop
  simp only [polarScale]
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul _ hdens hinner]
  exact lintegral_subtype_comap measurableSet_Ioi
    (fun t : ℝ => ENNReal.ofReal (t ^ (finrank ℝ E - 1)) *
      f (t • (ω : E)))


theorem setLIntegral_ball_eq_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, f x ∂μ =
      ∫⁻ ω : sphere (0 : E) 1,
        (∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hind : Measurable ((ball (0 : E) r).indicator f) :=
    hf.indicator measurableSet_ball
  rw [← lintegral_indicator measurableSet_ball,
    lintegral_eq_polar μ hind]
  refine lintegral_congr fun ω => ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  rw [← lintegral_indicator measurableSet_Ioo,
    ← lintegral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    have hnorm : ‖t • (ω : E)‖ = t := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    by_cases htr : t < r
    · have hmem : t • (ω : E) ∈ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_mem, ht, htr, htpos, hmem, mem_Ioo]
    · have hmem : t • (ω : E) ∉ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_notMem, ht, htr, hmem, mem_Ioo]
  · have hnot : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [indicator_of_notMem, ht, hnot]

end Poincare.VolumeComparison
