import PoincareConjecture.Proofs.M14.Sec6_7_GaussianBound
import PoincareConjecture.Proofs.M14.Sec6_7_DensityIntegrability
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingMeasureBasis










set_option autoImplicit false

open Set MeasureTheory

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}



noncomputable def stableSourceDensity (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) : G.Horizontal x → ℝ :=
  H.carrier.indicator (fun Z => exponentialWeightedJacobian E b Z (Real.sqrt τ))



theorem stableSourceDensity_nonneg (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) (Z : G.Horizontal x) :
    0 ≤ stableSourceDensity H b Z :=
  indicator_nonneg (fun Z _ => exponentialWeightedJacobian_nonneg E b Z (Real.sqrt_nonneg τ)) Z



theorem stableSourceDensity_measurable
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) : Measurable (stableSourceDensity H b) := by
  classical
  let D := rescalingMeasureDataWithBasis H b hb
  have hw : ContinuousOn (fun Z => exponentialWeightedJacobian E b Z (Real.sqrt τ))
      H.carrier := (stableDensity_jacobian_continuousOn hM04 hM12 H D).congr
        (fun _ hZ => (stableDensity_mul_jacobian_eq_weighted E H D hZ).symm)
  exact hw.measurable_piecewise continuousOn_const H.carrier_open.measurableSet




theorem stableSourceDensity_le_gaussian
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) (Z : G.Horizontal x) :
    stableSourceDensity H b Z ≤
      Real.rpow (2 : ℝ) (n : ℝ) * Real.exp (-G.spacetime.horizontalMetric.inner x Z Z) := by
  classical
  by_cases hZ : Z ∈ H.carrier
  · rw [stableSourceDensity, indicator_of_mem hZ]
    exact exponentialWeightedJacobian_le_gaussian hCoordinates hM04 hM12 E b hb H hZ
  · rw [stableSourceDensity, indicator_of_notMem hZ]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le



theorem integral_stableSourceDensity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) :
    (∫ Z, stableSourceDensity H b Z ∂M14HorizontalCoordinateVolume G b) =
      M14ReducedVolumeOnStable G T x τ H := by
  let D := rescalingMeasureDataWithBasis H b hb
  have hi := stableDensity_integrable_of_gaussian hM04 hM12 H D
    (fun _ hZ => stableDensity_mul_jacobian_le_gaussian hCoordinates hM04 hM12 E H D hZ)
  rw [stableSourceDensity, integral_indicator H.carrier_open.measurableSet]
  calc
    _ = ∫ Z in H.carrier, stableReducedVolumeDensity H (H.endpoint_slice_map Z) * D.jacobian Z
        ∂D.sourceMeasure := by
      apply setIntegral_congr_fun H.carrier_open.measurableSet
      exact fun _ hZ => (stableDensity_mul_jacobian_eq_weighted E H D hZ).symm
    _ = ∫ q in H.endpoint_slice_map '' H.carrier, stableReducedVolumeDensity H q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := hi.2.2
    _ = M14ReducedVolumeOnStable G T x τ H := by
      apply setIntegral_congr_fun D.image_measurable
      exact fun _ hq => stableReducedVolumeDensity_eq H hq

end PoincareConjecture.M14
