import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Transport.DisjointImages
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Density.SourceGaussian

/-!
# Bounds for a supplied analytic reduced-volume density

Nonnegativity, image integrability and Gaussian domination are fields
of the same analytic witness. They give subset monotonicity and the
Euclidean mass bound without assumptions away from its stable image.
Morgan-Tian Theorem 6.80 and Corollary 6.82, pp. 144-147.
-/

set_option autoImplicit false

open Set Filter MeasureTheory

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

/-- Reduced volume on a stable source subset is nonnegative,
Definition 6.70, p. 140. -/
theorem analyticCarrier_nonneg (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hm : MeasurableSet W) :
    0 ≤ M14ReducedVolumeOnAnalyticCarrier A W := by
  apply setIntegral_nonneg (stable_slice_image_measurable H hW hm)
  exact fun q hq => A.density_nonnegative q (image_mono hW hq)

/-- Integrable nonnegative analytic density is monotone under
measurable source inclusion, Corollary 6.82, pp. 146-147. -/
theorem analyticCarrier_mono (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W V : Set (G.Horizontal x)} (hWV : W ⊆ V) (hV : V ⊆ H.carrier)
    (hm : MeasurableSet V) :
    M14ReducedVolumeOnAnalyticCarrier A W ≤ M14ReducedVolumeOnAnalyticCarrier A V := by
  apply setIntegral_mono_set (A.density_integrable.mono_set (image_mono hV))
  · filter_upwards [ae_restrict_mem (stable_slice_image_measurable H hV hm)] with q hq
    exact A.density_nonnegative q (image_mono hV hq)
  · exact Eventually.of_forall (fun q hq => image_mono hWV hq)

/-- The full analytic reduced volume is bounded by the exact source
Gaussian mass, Corollary 6.82, pp. 146-147. -/
theorem analyticCarrier_le_euclidean (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H) :
    M14ReducedVolumeOnAnalyticCarrier A H.carrier ≤ euclideanReducedVolume n := by
  rw [M14ReducedVolumeOnAnalyticCarrier, ← A.density_change_of_variables_on_image,
    ← measureData_integral_sourceGaussian A.measure_data]
  have hgauss := measureData_sourceGaussian_integrable A.measure_data
  refine (setIntegral_mono_on A.density_integrable_on_source hgauss.integrableOn
    A.measure_data.carrier_measurable ?_).trans ?_
  · intro Z hZ
    exact (A.gaussian_bound Z hZ).trans_eq (A.initial_density_eq Z)
  · apply setIntegral_le_integral hgauss
    exact Eventually.of_forall (fun Z => mul_nonneg
      (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le)

end PoincareMT.M14
