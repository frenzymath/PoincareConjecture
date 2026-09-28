import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryStableLength
import PoincareConjecture.Proofs.M34.Mathlib.FullMeasureOpenImage










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}




theorem ordinaryProduct_stable_open_volume
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T taumax tau l0 : ℝ} (hT : T ∈ I.domain)
    (out : M14OrdinaryCaptureOutput (ordinaryProductLGeometry R hRicci) M I
      R.product.productCylinder R.product.productMetric F T taumax
      (ordinaryProductCaptureData (I := I) (F := F) R hRicci hT taumax))
    {x : (ordinaryProductLGeometry R hRicci).Point}
    (E : M14ExponentialFamily (ordinaryProductLGeometry R hRicci) T x)
    (H : M14StableSet (ordinaryProductLGeometry R hRicci) T tau x E)
    (hmax : tau < taumax) (hmem : T - tau ∈ I.domain)
    {Omega : Set M} (hOmega : IsOpen Omega)
    (hbound : ∀ y ∈ Omega,
      reducedLength F T (ordinaryProductProjection R.product x) y tau ≤ l0) :
    ∃ W : Set ((ordinaryProductLGeometry R hRicci).Horizontal x),
      IsOpen W ∧ W ⊆ H.carrier ∧
      (∀ Z ∈ W, E.reduced_length Z (Real.sqrt tau) ≤ l0) ∧
      calibratedMetricVolume ((ordinaryProductLGeometry R hRicci).slices
        (T - tau)).metricOnPoints (H.endpoint_slice_map '' W) =
        calibratedMetricVolume (F.metric (T - tau)) Omega := by
  let iota := R.product.sliceIdentification ⟨T - tau, hmem⟩
  let B := iota '' Omega
  have hB : IsOpen B := iota.toHomeomorph.isOpenMap _ hOmega
  have hx : x ∈ range R.product.productCylinder.toSpacetime := by
    rw [ordinaryProductCylinder_range]; trivial
  have hfull : calibratedMetricVolume
      ((ordinaryProductLGeometry R hRicci).slices (T - tau)).metricOnPoints
      (H.endpoint_slice_map '' H.carrier)ᶜ = 0 := by
    have h := out.captured_stable_image_full_measure tau x E H hmax hx
    simpa only [ordinaryProductCylinder_range, mem_univ, ofPred_true,
      compl_eq_univ_sdiff] using h
  obtain ⟨W, hW, hWH, hWB, hvol⟩ := exists_open_image_measure_eq H.carrier_open
    H.endpoint_slice_continuous _ hfull hB
  have hproj : ordinaryProductProjection R.product '' ((fun q => q.val) '' B) = Omega := by
    change ordinaryProductProjection R.product ''
      ((fun q => q.val) '' (iota '' Omega)) = Omega
    rw [image_image, image_image]
    have heq : (fun z => ordinaryProductProjection R.product (iota z).val) = id := by
      funext z
      rw [ordinaryProductProjection_eq, R.product.sliceIdentification_eq]
      rfl
    rw [heq, image_id]
  have hBvol : calibratedMetricVolume
      ((ordinaryProductLGeometry R hRicci).slices (T - tau)).metricOnPoints B =
      calibratedMetricVolume (F.metric (T - tau)) Omega := by
    have hc : (fun q => q.val) '' B ⊆ range R.product.productCylinder.toSpacetime := by
      rw [ordinaryProductCylinder_range]
      exact subset_univ _
    have h := out.captured_slice_measure_transport tau H.tau_pos hmax B hB.measurableSet hc
    change calibratedMetricVolume
      ((ordinaryProductLGeometry R hRicci).slices (T - tau)).metricOnPoints B =
      calibratedMetricVolume (F.metric (T - tau))
        (ordinaryProductProjection R.product '' ((fun q => q.val) '' B)) at h
    exact h.trans (congrArg _ hproj)
  refine ⟨W, hW, hWH, ?_, hvol.trans hBvol⟩
  intro Z hZ
  obtain ⟨y, hy, hey⟩ := hWB (mem_image_of_mem H.endpoint_slice_map hZ)
  rw [ordinaryProduct_stable_reduced_length R hRicci hT out E H hmax.le Z (hWH hZ)]
  have hp : ordinaryProductProjection R.product (H.endpoint_map Z) = y := by
    rw [← H.endpoint_slice_map_val Z (hWH hZ), ← hey,
      ordinaryProductProjection_eq, R.product.sliceIdentification_eq]
  rw [hp]
  exact hbound y hy

end PoincareConjecture.M34
