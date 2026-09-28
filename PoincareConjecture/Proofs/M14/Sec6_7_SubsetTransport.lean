import PoincareConjecture.Proofs.M14.Sec6_7_DisjointImages
import Mathlib.MeasureTheory.Integral.IntegrableOn










set_option autoImplicit false

open Set MeasureTheory

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  {H : M14StableSet G T τ x E}




theorem measureData_change_of_variables_subset (D : M14MeasureJacobianData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hm : MeasurableSet W)
    (φ : (G.slices (T - τ)).Point → ℝ) (hφ : Measurable φ) :
    (IntegrableOn (fun Z => φ (H.endpoint_slice_map Z) * D.jacobian Z) W D.sourceMeasure ↔
      IntegrableOn φ (H.endpoint_slice_map '' W)
        (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints)) ∧
    (∫ Z in W, φ (H.endpoint_slice_map Z) * D.jacobian Z ∂D.sourceMeasure) =
      ∫ q in H.endpoint_slice_map '' W, φ q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := by
  classical
  let V := H.endpoint_slice_map '' W
  have hV : MeasurableSet V := stable_slice_image_measurable H hW hm
  have hVsub : V ⊆ H.endpoint_slice_map '' H.carrier := image_mono hW
  let f := fun Z => φ (H.endpoint_slice_map Z) * D.jacobian Z
  have heq : EqOn (fun Z => V.indicator φ (H.endpoint_slice_map Z) * D.jacobian Z)
      (W.indicator f) H.carrier := by
    intro Z hZ
    change V.indicator φ (H.endpoint_slice_map Z) * D.jacobian Z = W.indicator f Z
    by_cases hZW : Z ∈ W
    · rw [indicator_of_mem (show H.endpoint_slice_map Z ∈ V from ⟨Z, hZW, rfl⟩),
        indicator_of_mem hZW]
    · have hZV : H.endpoint_slice_map Z ∉ V := by
        rintro ⟨Y, hYW, hYZ⟩
        exact hZW ((stable_slice_endpoint_injective H (hW hYW) hZ hYZ) ▸ hYW)
      rw [indicator_of_notMem hZV, indicator_of_notMem hZW, zero_mul]
  have hsource : IntegrableOn (fun Z => V.indicator φ (H.endpoint_slice_map Z) * D.jacobian Z)
      H.carrier D.sourceMeasure ↔ IntegrableOn f W D.sourceMeasure := by
    rw [integrableOn_congr_fun heq D.carrier_measurable, integrableOn_indicator_iff hm,
      inter_eq_left.mpr hW]
  have htarget : IntegrableOn (V.indicator φ) (H.endpoint_slice_map '' H.carrier)
      (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) ↔
      IntegrableOn φ V (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) := by
    rw [integrableOn_indicator_iff hV, inter_eq_left.mpr hVsub]
  have hsourceIntegral :
      (∫ Z in H.carrier, V.indicator φ (H.endpoint_slice_map Z) * D.jacobian Z
        ∂D.sourceMeasure) = ∫ Z in W, f Z ∂D.sourceMeasure := by
    rw [setIntegral_congr_fun D.carrier_measurable heq, setIntegral_indicator hm,
      inter_eq_right.mpr hW]
  have htargetIntegral :
      (∫ q in H.endpoint_slice_map '' H.carrier, V.indicator φ q
        ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints) =
      ∫ q in V, φ q ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := by
    rw [setIntegral_indicator hV, inter_eq_right.mpr hVsub]
  obtain ⟨hint, heqIntegral⟩ := D.change_of_variables (V.indicator φ) (hφ.indicator hV)
  exact ⟨hsource.symm.trans (hint.trans htarget),
    hsourceIntegral.symm.trans (heqIntegral.trans htargetIntegral)⟩

end PoincareConjecture.M14
