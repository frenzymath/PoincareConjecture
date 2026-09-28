import PoincareConjecture.Proofs.M14.Sec6_7_DensityIntegrability
import PoincareConjecture.Proofs.M14.Sec6_7_SubsetTransport
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingMeasureBasis










set_option autoImplicit false

open Set MeasureTheory

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ σ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}



theorem prescribedBasis_sourceMeasure_eq (H : M14StableSet G T τ x E)
    (Hσ : M14StableSet G T σ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner x (b i) (b j) =
      if i = j then 1 else 0) :
    (rescalingMeasureDataWithBasis H b hb).sourceMeasure =
      (rescalingMeasureDataWithBasis Hσ b hb).sourceMeasure := rfl




theorem stableDensity_integral_mono
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) (Hσ : M14StableSet G T σ x E)
    (D : M14MeasureJacobianData G T τ x E H)
    (Dσ : M14MeasureJacobianData G T σ x E Hσ)
    (hμ : D.sourceMeasure = Dσ.sourceMeasure)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hWσ : W ⊆ Hσ.carrier)
    (hm : MeasurableSet W)
    (hi : IntegrableOn (fun Z => stableReducedVolumeDensity H (H.endpoint_slice_map Z) *
      D.jacobian Z) W D.sourceMeasure)
    (hiσ : IntegrableOn (fun Z => stableReducedVolumeDensity Hσ (Hσ.endpoint_slice_map Z) *
      Dσ.jacobian Z) W Dσ.sourceMeasure)
    (hle : ∀ Z ∈ W,
      stableReducedVolumeDensity H (H.endpoint_slice_map Z) * D.jacobian Z ≤
        stableReducedVolumeDensity Hσ (Hσ.endpoint_slice_map Z) * Dσ.jacobian Z) :
    (∫ q in H.endpoint_slice_map '' W, stableReducedVolumeDensity H q
      ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) ≤
    (∫ q in Hσ.endpoint_slice_map '' W, stableReducedVolumeDensity Hσ q
      ∂calibratedMetricVolume (G.slices (T - σ)).metricOnPoints) := by
  rw [← (measureData_change_of_variables_subset D hW hm _
    (stableReducedVolumeDensity_measurable hM04 hM12 H)).2,
    ← (measureData_change_of_variables_subset Dσ hWσ hm _
      (stableReducedVolumeDensity_measurable hM04 hM12 Hσ)).2]
  rw [hμ] at hi ⊢
  exact setIntegral_mono_on hi hiσ hm hle

end PoincareConjecture.M14
