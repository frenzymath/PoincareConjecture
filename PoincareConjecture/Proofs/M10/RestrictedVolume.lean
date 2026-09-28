import PoincareConjecture.Proofs.M10.RestrictedRays
import PoincareConjecture.Proofs.M10.VolumeTransport









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

theorem restrictedWeightedJacobian_integrable
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {A : Set (M × ℝ)} (hA : IsOpen A) {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    Integrable (restrictedWeightedJacobian G A τ) := by
  apply (regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax).mono'
      (restrictedWeightedJacobian_measurable G hA hτ hτmax).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (restrictedWeightedJacobian_nonneg G A hτ x)]
  exact restrictedWeightedJacobian_le_regular G A hτ x


theorem lintegral_reducedVolumeDensityOn_eq_restrictedWeight
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    {A : Set (M × ℝ)} (hA : IsOpen A) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    (∫⁻ q in {q | (q, τ) ∈ A}, ENNReal.ofReal (reducedVolumeDensity F T p τ q)
      ∂calibratedMetricVolume (F.metric (T - τ))) =
      ∫⁻ x, ENNReal.ofReal (restrictedWeightedJacobian G A τ x) := by
  classical
  let B : Set M := {q | (q, τ) ∈ A}
  have hB : MeasurableSet B :=
    (hA.preimage (continuous_id.prodMk continuous_const)).measurableSet
  have hf : Measurable (B.indicator (fun q ↦ ENNReal.ofReal (reducedVolumeDensity F T p τ q))) :=
    ((ENNReal.continuous_ofReal.comp
      (reducedVolumeDensity_continuous hL hDifferential hτ hmax)).measurable).indicator hB
  rw [← lintegral_indicator hB,
    lintegral_eq_exponentialSliceJacobian hL hDifferential hwindow G hτ hmax hf.aemeasurable,
    ← lintegral_indicator (exponentialSliceChart G τ).open_source.measurableSet]
  apply lintegral_congr
  intro x
  by_cases hs : x ∈ (exponentialSliceChart G τ).source
  · have hreg : (metricCoordinates (F.metric T) p x, τ) ∈
        G.toLExponentialFamily.regularDomain := by
      simpa only [exponentialSliceChart_source, mem_ofPred_eq] using hs
    by_cases hax : (exponentialSliceChart G τ x, τ) ∈ A
    · have ht : x ∈ restrictedRegularSource G A τ := ⟨hs, hax⟩
      have hb : exponentialSliceChart G τ x ∈ B := hax
      simp only [restrictedWeightedJacobian, indicator_of_mem hs, indicator_of_mem ht,
        indicator_of_mem hb]
      rw [weightedExponentialJacobian_eq_density_mul hL G x hreg,
        ENNReal.ofReal_mul reducedVolumeDensity_nonneg]
      exact mul_comm _ _
    · have ht : x ∉ restrictedRegularSource G A τ := fun h ↦ hax h.2
      have hb : exponentialSliceChart G τ x ∉ B := hax
      simp only [restrictedWeightedJacobian, indicator_of_mem hs, indicator_of_notMem ht,
        indicator_of_notMem hb, mul_zero, ENNReal.ofReal_zero]
  · have ht : x ∉ restrictedRegularSource G A τ := fun h ↦ hs h.1
    simp only [restrictedWeightedJacobian, indicator_of_notMem hs, indicator_of_notMem ht,
      ENNReal.ofReal_zero]


theorem reducedVolumeOn_eq_integral_restrictedWeight
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {A : Set (M × ℝ)} (hA : IsOpen A) {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax) :
    reducedVolumeOn F T p τ {q | (q, τ) ∈ A} =
      ∫ x, restrictedWeightedJacobian G A τ x := by
  have htarget := (reducedVolumeDensity_integrable hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax).restrict (s := {q | (q, τ) ∈ A})
  have hsource := restrictedWeightedJacobian_integrable hL hDifferential G hmax hT hwindow
    hcurvature hA hτ hτmax
  calc
    _ = ENNReal.toReal (∫⁻ q in {q | (q, τ) ∈ A},
        ENNReal.ofReal (reducedVolumeDensity F T p τ q)
          ∂calibratedMetricVolume (F.metric (T - τ))) :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ ↦ reducedVolumeDensity_nonneg))
        htarget.aestronglyMeasurable
    _ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (restrictedWeightedJacobian G A τ x)) :=
      congrArg ENNReal.toReal
        (lintegral_reducedVolumeDensityOn_eq_restrictedWeight hL hDifferential hwindow G hA
          hτ hτmax)
    _ = _ := (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (restrictedWeightedJacobian_nonneg G A hτ)) hsource.aestronglyMeasurable).symm


theorem reducedVolumeOn_antitoneOn
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {A : Set (M × ℝ)} (hA : IsBackwardLStarShaped F T τmax p A) :
    AntitoneOn (fun τ ↦ reducedVolumeOn F T p τ {q | (q, τ) ∈ A}) (Ioo 0 τmax) := by
  intro a ha b hb hab
  dsimp only
  rw [reducedVolumeOn_eq_integral_restrictedWeight hL hDifferential G hmax hT hwindow
      hcurvature hA.1 hb.1 hb.2,
    reducedVolumeOn_eq_integral_restrictedWeight hL hDifferential G hmax hT hwindow
      hcurvature hA.1 ha.1 ha.2]
  exact integral_mono
    (restrictedWeightedJacobian_integrable hL hDifferential G hmax hT hwindow
      hcurvature hA.1 hb.1 hb.2)
    (restrictedWeightedJacobian_integrable hL hDifferential G hmax hT hwindow
      hcurvature hA.1 ha.1 ha.2)
    (fun x ↦ restrictedWeightedJacobian_antitoneOn hwindow hL hDifferential G hA x ha hb hab)

end PoincareConjecture.M10
