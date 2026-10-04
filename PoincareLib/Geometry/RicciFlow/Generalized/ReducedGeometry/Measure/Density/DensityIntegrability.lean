import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Density.StableDensity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.JacobianContinuity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Density.SourceGaussian

/-!
# Integrability from actual Gaussian domination

Continuity is required only on the stable carrier. The source metric
Gaussian is integrable for the same selected basis measure, and the
supplied calibrated identity transfers integrability and the integral
to the actual image. Morgan-Tian Proposition 6.81, pp. 145-146.
-/

set_option autoImplicit false

open Set Filter MeasureTheory

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

/-- The actual stable density times any supplied metric Jacobian
is continuous on the source carrier, Lemma 6.71, p. 141. -/
theorem stableDensity_jacobian_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) (D : M14MeasureJacobianData G T τ x E H) :
    ContinuousOn (fun Z => stableReducedVolumeDensity H (H.endpoint_slice_map Z) *
      D.jacobian Z) H.carrier :=
  ((stableReducedVolumeDensity_continuousOn hM04 hM12 H).comp H.endpoint_slice_continuous
    (fun Z hZ => ⟨Z, hZ, rfl⟩)).mul (measureData_jacobian_continuousOn D)

/-- A pointwise Gaussian bound gives both actual source and image
integrability and their exact calibrated integral equality,
Proposition 6.81, pp. 145-146. -/
theorem stableDensity_integrable_of_gaussian
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) (D : M14MeasureJacobianData G T τ x E H)
    (hbound : ∀ Z ∈ H.carrier,
      stableReducedVolumeDensity H (H.endpoint_slice_map Z) * D.jacobian Z ≤
        Real.rpow (2 : ℝ) (n : ℝ) *
          Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) :
    IntegrableOn (fun Z => stableReducedVolumeDensity H (H.endpoint_slice_map Z) *
      D.jacobian Z) H.carrier D.sourceMeasure ∧
    IntegrableOn (stableReducedVolumeDensity H) (H.endpoint_slice_map '' H.carrier)
      (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) ∧
    (∫ Z in H.carrier, stableReducedVolumeDensity H (H.endpoint_slice_map Z) *
      D.jacobian Z ∂D.sourceMeasure) =
      ∫ q in H.endpoint_slice_map '' H.carrier, stableReducedVolumeDensity H q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := by
  have hsource : IntegrableOn (fun Z => stableReducedVolumeDensity H (H.endpoint_slice_map Z) *
      D.jacobian Z) H.carrier D.sourceMeasure := by
    apply (measureData_sourceGaussian_integrable D).integrableOn.mono_nonneg
      ((stableDensity_jacobian_continuousOn hM04 hM12 H D).aestronglyMeasurable
        D.carrier_measurable)
    · exact Eventually.of_forall (fun Z => mul_nonneg
        (stableReducedVolumeDensity_nonneg H _) (D.jacobian_nonnegative Z))
    · filter_upwards [ae_restrict_mem D.carrier_measurable] with Z hZ
      exact hbound Z hZ
  have htransport := D.change_of_variables (stableReducedVolumeDensity H)
    (stableReducedVolumeDensity_measurable hM04 hM12 H)
  exact ⟨hsource, htransport.1.mp hsource, htransport.2⟩

end PoincareMT.M14
