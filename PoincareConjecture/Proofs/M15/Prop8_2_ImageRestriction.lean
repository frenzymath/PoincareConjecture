import PoincareConjecture.Statements.M15Noncollapsing
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  {H : M14StableSet G T τ x E}

theorem stable_image_measurable (S : M14ReducedVolumeSourceCoverageData G)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : MeasurableSet W) (hWH : W ⊆ H.carrier) :
    MeasurableSet (H.endpoint_slice_map '' W) :=
  ((S.disjoint_image_additivity T τ x E H A).2 W ∅ hWH
    (Set.empty_subset _) hW MeasurableSet.empty (by simp)).1

theorem reducedVolumeOn_subset_eq_source
    (S : M14ReducedVolumeSourceCoverageData G)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : MeasurableSet W) (hWH : W ⊆ H.carrier) :
    M14ReducedVolumeOnAnalyticCarrier A W =
      ∫ Z in W, A.density (H.endpoint_slice_map Z) * A.measure_data.jacobian Z
        ∂A.measure_data.sourceMeasure := by
  classical
  have himage := stable_image_measurable S A hW hWH
  have hinj := (S.disjoint_image_additivity T τ x E H A).1
  have hemb := MeasurableEmbedding.subtype_coe A.measure_data.image_measurable
  obtain ⟨ρ, hρ, hρeq⟩ :=
    hemb.exists_measurable_extend A.density_measurable_on_image (fun _ => inferInstance)
  have hρon (q : (G.slices (T - τ)).Point)
      (hq : q ∈ H.endpoint_slice_map '' H.carrier) : ρ q = A.density q :=
    congrFun hρeq ⟨q, hq⟩
  have hmem (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) :
      H.endpoint_slice_map Z ∈ H.endpoint_slice_map '' W ↔ Z ∈ W := by
    constructor
    · rintro ⟨Y, hY, hYZ⟩
      exact (hinj (hWH hY) hZ hYZ) ▸ hY
    · intro hZ'
      exact ⟨Z, hZ', rfl⟩
  have hcv := (A.measure_data.change_of_variables
    ((H.endpoint_slice_map '' W).indicator ρ) (hρ.indicator himage)).2
  calc
    M14ReducedVolumeOnAnalyticCarrier A W =
        ∫ q in H.endpoint_slice_map '' W, ρ q
          ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := by
      apply setIntegral_congr_fun himage
      intro q hq
      exact (hρon q (Set.image_mono hWH hq)).symm
    _ = ∫ q in H.endpoint_slice_map '' H.carrier,
        (H.endpoint_slice_map '' W).indicator ρ q
          ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := by
      rw [setIntegral_indicator himage,
        Set.inter_eq_right.mpr (Set.image_mono hWH)]
    _ = ∫ Z in H.carrier,
        (H.endpoint_slice_map '' W).indicator ρ (H.endpoint_slice_map Z) *
          A.measure_data.jacobian Z ∂A.measure_data.sourceMeasure := hcv.symm
    _ = ∫ Z in H.carrier,
        W.indicator (fun Z => A.density (H.endpoint_slice_map Z) *
          A.measure_data.jacobian Z) Z ∂A.measure_data.sourceMeasure := by
      apply setIntegral_congr_fun A.measure_data.carrier_measurable
      intro Z hZ
      dsimp only
      by_cases hZW : Z ∈ W
      · rw [Set.indicator_of_mem ((hmem Z hZ).2 hZW), Set.indicator_of_mem hZW,
          hρon _ ⟨Z, hZ, rfl⟩]
      · rw [Set.indicator_of_notMem (mt (hmem Z hZ).1 hZW),
          Set.indicator_of_notMem hZW, zero_mul]
    _ = ∫ Z in W,
        A.density (H.endpoint_slice_map Z) * A.measure_data.jacobian Z
          ∂A.measure_data.sourceMeasure := by
      rw [setIntegral_indicator hW, Set.inter_eq_right.mpr hWH]

theorem reducedVolumeOn_le_initial_density
    (S : M14ReducedVolumeSourceCoverageData G)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : MeasurableSet W) (hWH : W ⊆ H.carrier)
    (hinitial : IntegrableOn A.initial_density W A.measure_data.sourceMeasure) :
    M14ReducedVolumeOnAnalyticCarrier A W ≤
      ∫ Z in W, A.initial_density Z ∂A.measure_data.sourceMeasure := by
  rw [reducedVolumeOn_subset_eq_source S A hW hWH]
  exact setIntegral_mono_on (A.density_integrable_on_source.mono_set hWH)
    hinitial hW (fun Z hZ => A.gaussian_bound Z (hWH hZ))

end PoincareConjecture.Proofs.M15
