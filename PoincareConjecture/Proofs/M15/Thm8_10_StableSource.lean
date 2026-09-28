import PoincareConjecture.Proofs.M15.Thm8_10_OrdinaryCapture
import PoincareConjecture.Proofs.M15.Thm8_10_StableAction











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ConnectedSpace M] [SecondCountableTopology M] {I : SpacetimeInterval}



theorem ordinaryProduct_stable_source
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    {T tau taumax l0 V : ℝ}
    (capture : M14OrdinaryCaptureData (ordinaryProductTransport F P) M I
      P.product.productCylinder (ordinaryProductCylinderMetric F P) F T taumax)
    (out : M14OrdinaryCaptureOutput (ordinaryProductTransport F P) M I
      P.product.productCylinder (ordinaryProductCylinderMetric F P) F T taumax capture)
    (htau : tau < taumax) (htime : T - tau ∈ I.domain)
    {x : (ordinaryProductTransport F P).Point}
    (hbase : (ordinaryProductTransport F P).spacetime.timeFunction x = T)
    {E : M14ExponentialFamily (ordinaryProductTransport F P) T x}
    (H : M14StableSet (ordinaryProductTransport F P) T tau x E)
    (U : Set M) (hU : IsOpen U)
    (hlength : ∀ q ∈ U, reducedLength F T (capture.point_map x) q tau ≤ l0)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (T - tau)) U) :
    ∃ W : Set ((ordinaryProductTransport F P).Horizontal x),
      IsOpen W ∧ W ⊆ H.carrier ∧
      (∀ Z ∈ W, E.reduced_length Z (Real.sqrt tau) ≤ l0) ∧
      ENNReal.ofReal V ≤
        calibratedMetricVolume ((ordinaryProductTransport F P).slices (T - tau)).metricOnPoints
          (H.endpoint_slice_map '' W) := by
  let G := ordinaryProductTransport F P
  let f : (G.slices (T - tau)).Point → M := fun q => capture.point_map q.val
  let A : Set (G.slices (T - tau)).Point := f ⁻¹' U
  let W : Set (G.Horizontal x) := H.carrier ∩ H.endpoint_slice_map ⁻¹' A
  have hpoint : Continuous capture.point_map := by
    apply continuousOn_univ.mp
    simpa only [ordinaryProductCylinder_range F P] using capture.point_map_continuous
  have hf : Continuous f := hpoint.comp continuous_subtype_val
  have hA : IsOpen A := hU.preimage hf
  have hsurj : Function.Surjective f := by
    intro q
    refine ⟨P.product.sliceIdentification ⟨T - tau, htime⟩ q, ?_⟩
    change capture.point_map (P.product.sliceIdentification ⟨T - tau, htime⟩ q).val = q
    rw [P.product.sliceIdentification_eq]
    have h := capture.point_map_on_cylinder ⟨T - tau, htime⟩ q
    rwa [P.product.productCylinder_eq] at h
  have hAcap : (fun q => q.val) '' A ⊆ range P.product.productCylinder.toSpacetime := by
    rw [ordinaryProductCylinder_range F P]
    exact subset_univ _
  have hmeasure := out.captured_slice_measure_transport tau H.tau_pos htau A
    hA.measurableSet hAcap
  rw [image_image] at hmeasure
  change calibratedMetricVolume (G.slices (T - tau)).metricOnPoints A =
    calibratedMetricVolume (F.metric (T - tau)) (f '' A) at hmeasure
  have himageA : f '' A = U := image_preimage_eq U hsurj
  rw [himageA] at hmeasure
  have hxcap : x ∈ range P.product.productCylinder.toSpacetime := by
    rw [ordinaryProductCylinder_range F P]
    exact mem_univ _
  have hnull : calibratedMetricVolume (G.slices (T - tau)).metricOnPoints
      (H.endpoint_slice_map '' H.carrier)ᶜ = 0 := by
    have h := out.captured_stable_image_full_measure tau x E H htau hxcap
    simp only [ordinaryProductCylinder_range F P, mem_univ, ofPred_true] at h
    convert! h using 2
    ext q
    simp only [mem_compl_iff, mem_sdiff, mem_univ, true_and]
  have himage : H.endpoint_slice_map '' W = A \ (H.endpoint_slice_map '' H.carrier)ᶜ := by
    ext q
    constructor
    · rintro ⟨Z, ⟨hZ, hZA⟩, rfl⟩
      exact ⟨hZA, by simpa only [mem_compl_iff, not_not] using
        (show H.endpoint_slice_map Z ∈ H.endpoint_slice_map '' H.carrier from ⟨Z, hZ, rfl⟩)⟩
    · rintro ⟨hqA, hq⟩
      have hqin : q ∈ H.endpoint_slice_map '' H.carrier := by
        simpa only [mem_compl_iff, not_not] using hq
      obtain ⟨Z, hZ, rfl⟩ := hqin
      exact ⟨Z, ⟨hZ, hqA⟩, rfl⟩
  refine ⟨W, H.endpoint_slice_continuous.isOpen_inter_preimage H.carrier_open hA,
    inter_subset_left, ?_, ?_⟩
  · intro Z hZ
    rw [ordinaryProduct_stable_reducedLength_eq hM12 F P H hZ.1]
    have hycap : H.endpoint_map Z ∈ range P.product.productCylinder.toSpacetime := by
      rw [ordinaryProductCylinder_range F P]
      exact mem_univ _
    rw [out.reduced_length_transport tau x (H.endpoint_map Z) H.tau_pos htau.le
      hbase (H.endpoint_time Z hZ.1) hxcap hycap]
    apply hlength
    have hzA : capture.point_map (H.endpoint_slice_map Z).val ∈ U := hZ.2
    rwa [H.endpoint_slice_map_val Z hZ.1] at hzA
  · rw [himage, measure_sdiff_null hnull, hmeasure]
    exact hvolume

end PoincareConjecture.Proofs.M15
