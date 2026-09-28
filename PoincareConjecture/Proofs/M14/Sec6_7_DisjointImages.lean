import PoincareConjecture.Proofs.M14.Sec6_3_StableInjectivity
import PoincareConjecture.Statements.M14GeneralizedLGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set










set_option autoImplicit false

open scoped MeasureTheory Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}



theorem stable_slice_image_measurable (H : M14StableSet G T τ x E)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hm : MeasurableSet W) :
    MeasurableSet (H.endpoint_slice_map '' W) := by
  let e := FiberBundle.homeomorphAt (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let : PolishSpace (G.Horizontal x) := e.isClosedEmbedding.polishSpace
  exact hm.image_of_continuousOn_injOn (H.endpoint_slice_continuous.mono hW)
    ((stable_slice_endpoint_injective H).mono hW)



theorem analyticCarrier_eq_densityIntegral (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : W ⊆ H.carrier) (hm : MeasurableSet W) :
    M14ReducedVolumeOnAnalyticCarrier A W =
      ∫ q in H.endpoint_slice_map '' W,
        Real.rpow τ (-(n : ℝ) / 2) *
          Real.exp (-M14ReducedLengthValue G T 0 τ x q.val)
          ∂calibratedMetricVolume (G.slices (T - τ)).metricOnPoints := by
  apply MeasureTheory.setIntegral_congr_fun (stable_slice_image_measurable H hW hm)
  intro q hq
  exact A.density_eq q ((Set.image_mono hW) hq)



theorem analyticCarrier_eq_stableVolume (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H) :
    M14ReducedVolumeOnAnalyticCarrier A H.carrier =
      M14ReducedVolumeOnStable G T x τ H :=
  analyticCarrier_eq_densityIntegral H A Set.Subset.rfl H.carrier_open.measurableSet



theorem disjointImageAdditivity (H : M14StableSet G T τ x E)
    (A : M14ReducedVolumeAnalyticData G T τ x E H) :
    Set.InjOn H.endpoint_slice_map H.carrier ∧
      ∀ W₁ W₂ : Set (G.Horizontal x),
        W₁ ⊆ H.carrier → W₂ ⊆ H.carrier →
        MeasurableSet W₁ → MeasurableSet W₂ → Disjoint W₁ W₂ →
          MeasurableSet (H.endpoint_slice_map '' W₁) ∧
          MeasurableSet (H.endpoint_slice_map '' W₂) ∧
          MeasurableSet (H.endpoint_slice_map '' (W₁ ∪ W₂)) ∧
          Disjoint (H.endpoint_slice_map '' W₁) (H.endpoint_slice_map '' W₂) ∧
          M14ReducedVolumeOnAnalyticCarrier A (W₁ ∪ W₂) =
            M14ReducedVolumeOnAnalyticCarrier A W₁ +
              M14ReducedVolumeOnAnalyticCarrier A W₂ := by
  have hinj := stable_slice_endpoint_injective H
  refine ⟨hinj, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hm₁ hm₂ hd
  have him₁ := stable_slice_image_measurable H hW₁ hm₁
  have him₂ := stable_slice_image_measurable H hW₂ hm₂
  have hid := hd.image hinj hW₁ hW₂
  refine ⟨him₁, him₂, ?_, hid, ?_⟩
  · rw [Set.image_union]
    exact him₁.union him₂
  · unfold M14ReducedVolumeOnAnalyticCarrier
    rw [Set.image_union]
    exact MeasureTheory.setIntegral_union hid him₂
      (A.density_integrable.mono_set (Set.image_mono hW₁))
      (A.density_integrable.mono_set (Set.image_mono hW₂))

end PoincareConjecture.M14
