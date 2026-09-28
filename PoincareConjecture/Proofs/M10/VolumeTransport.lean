import PoincareConjecture.Proofs.M10.GaussianDomination
import PoincareConjecture.Proofs.M10.Continuity

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

omit [MeasurableSpace M] [BorelSpace M] in

theorem reducedVolumeDensity_continuous
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Continuous (reducedVolumeDensity F T p τ) := by
  have hc : Continuous (fun q : M ↦ reducedLength F T p q τ) :=
    (reducedLength_continuousOn hL hDifferential p).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨mem_univ _, hτ, hmax⟩)
  have heq : reducedVolumeDensity F T p τ =
      (fun q ↦ Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-reducedLength F T p q τ)) := by
    funext q
    exact if_pos hτ
  rw [heq]
  exact continuous_const.mul (Real.continuous_exp.comp hc.neg)

theorem lintegral_reducedVolumeDensity_eq_regularWeight
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    (∫⁻ q, ENNReal.ofReal (reducedVolumeDensity F T p τ q)
      ∂calibratedMetricVolume (F.metric (T - τ))) =
      ∫⁻ x, ENNReal.ofReal (regularWeightedJacobian G τ x) := by
  classical
  let S := (exponentialSliceChart G τ).source
  have hS : MeasurableSet S := (exponentialSliceChart G τ).open_source.measurableSet
  have hf : AEMeasurable (fun q ↦ ENNReal.ofReal (reducedVolumeDensity F T p τ q))
      (calibratedMetricVolume (F.metric (T - τ))) := (ENNReal.continuous_ofReal.comp
    (reducedVolumeDensity_continuous hL hDifferential hτ hmax)).measurable.aemeasurable
  calc
    _ = ∫⁻ x in S, ENNReal.ofReal (exponentialSliceJacobian G τ x) *
        ENNReal.ofReal (reducedVolumeDensity F T p τ (exponentialSliceChart G τ x)) :=
      lintegral_eq_exponentialSliceJacobian hL hDifferential hwindow G hτ hmax hf
    _ = ∫⁻ x in S, ENNReal.ofReal (weightedExponentialJacobian G τ x) := by
      apply setLIntegral_congr_fun hS
      intro x hx
      have hreg : (metricCoordinates (F.metric T) p x, τ) ∈
          G.toLExponentialFamily.regularDomain := by
        simpa only [S, exponentialSliceChart_source, mem_ofPred_eq] using hx
      dsimp only
      rw [weightedExponentialJacobian_eq_density_mul hL G x hreg,
        ENNReal.ofReal_mul reducedVolumeDensity_nonneg]
      exact mul_comm _ _
    _ = _ := by
      rw [← lintegral_indicator hS]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ S
      · simp only [regularWeightedJacobian, S, indicator_of_mem hx]
      · simp only [regularWeightedJacobian, S, indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem reducedVolumeDensity_integrable
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    Integrable (reducedVolumeDensity F T p τ) (calibratedMetricVolume (F.metric (T - τ))) := by
  have hsource := regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax
  have hc := reducedVolumeDensity_continuous (p := p) hL hDifferential hτ hτmax
  refine ⟨hc.measurable.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ reducedVolumeDensity_nonneg))).mpr ?_⟩
  rw [lintegral_reducedVolumeDensity_eq_regularWeight hL hDifferential hwindow G hτ hτmax]
  exact (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (regularWeightedJacobian_nonneg G hτ))).mp hsource.hasFiniteIntegral

theorem reducedVolume_eq_integral_regularWeight
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    reducedVolume F T p τ = ∫ x, regularWeightedJacobian G τ x := by
  have htarget := reducedVolumeDensity_integrable hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax
  have hsource := regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax
  calc
    _ = ENNReal.toReal (∫⁻ q, ENNReal.ofReal (reducedVolumeDensity F T p τ q)
        ∂calibratedMetricVolume (F.metric (T - τ))) :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ ↦ reducedVolumeDensity_nonneg))
        htarget.aestronglyMeasurable
    _ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (regularWeightedJacobian G τ x)) :=
      congrArg ENNReal.toReal
        (lintegral_reducedVolumeDensity_eq_regularWeight hL hDifferential hwindow G hτ hτmax)
    _ = _ := (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (regularWeightedJacobian_nonneg G hτ)) hsource.aestronglyMeasurable).symm

end PoincareConjecture.M10
