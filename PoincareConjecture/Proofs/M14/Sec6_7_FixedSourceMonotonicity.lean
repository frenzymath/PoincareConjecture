import PoincareConjecture.Proofs.M14.Sec6_7_GaussianBound
import PoincareConjecture.Proofs.M14.Sec6_7_IntegralComparison
import PoincareConjecture.Proofs.M14.Sec6_7_BackwardStable

set_option autoImplicit false

open Set MeasureTheory

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}

theorem stableDensity_fixed_source_mono
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hm : MeasurableSet W)
    {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ τ) :
    ∃ Hσ : M14StableSet G T σ x E, W ⊆ Hσ.carrier ∧
      (∫ q in H.endpoint_slice_map '' W, stableReducedVolumeDensity H q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) ≤
      (∫ q in Hσ.endpoint_slice_map '' W, Real.rpow σ (-(n : ℝ) / 2) *
        Real.exp (-M14ReducedLengthValue G T 0 σ x q.val)
        ∂calibratedMetricVolume (G.slices (T - σ)).metricOnPoints) := by
  obtain ⟨Hσ, hsub⟩ := exists_stableSet_backward hCoordinates hM04 hM12 E H hσ hle
  let D := rescalingMeasureDataWithBasis H b hb
  let Dσ := rescalingMeasureDataWithBasis Hσ b hb
  have hi := stableDensity_integrable_of_gaussian hM04 hM12 H D
    (fun _ hZ => stableDensity_mul_jacobian_le_gaussian hCoordinates hM04 hM12 E H D hZ)
  have hiσ := stableDensity_integrable_of_gaussian hM04 hM12 Hσ Dσ
    (fun _ hZ => stableDensity_mul_jacobian_le_gaussian hCoordinates hM04 hM12 E Hσ Dσ hZ)
  have hWσ : W ⊆ Hσ.carrier := hW.trans hsub
  have hpoint (Z : G.Horizontal x) (hZ : Z ∈ W) :
      stableReducedVolumeDensity H (H.endpoint_slice_map Z) * D.jacobian Z ≤
        stableReducedVolumeDensity Hσ (Hσ.endpoint_slice_map Z) * Dσ.jacobian Z := by
    rw [stableDensity_mul_jacobian_eq_weighted E H D (hW hZ),
      stableDensity_mul_jacobian_eq_weighted E Hσ Dσ (hWσ hZ)]
    change exponentialWeightedJacobian E b Z (Real.sqrt τ) ≤
      exponentialWeightedJacobian E b Z (Real.sqrt σ)
    have hsqrt := Real.sqrt_le_sqrt hle
    exact exponentialWeightedJacobian_antitoneOn hCoordinates hM04 hM12 E b H (hW hZ)
      ⟨Real.sqrt_pos.mpr hσ, hsqrt⟩ ⟨Real.sqrt_pos.mpr H.tau_pos, le_rfl⟩ hsqrt
  have hcompare := stableDensity_integral_mono hM04 hM12 H Hσ D Dσ rfl hW hWσ hm
    (hi.1.mono_set hW) (hiσ.1.mono_set hWσ) hpoint
  refine ⟨Hσ, hWσ, hcompare.trans_eq ?_⟩
  apply setIntegral_congr_fun (stable_slice_image_measurable Hσ hWσ hm)
  exact fun q hq => stableReducedVolumeDensity_eq Hσ (image_mono hWσ hq)

end PoincareConjecture.M14
