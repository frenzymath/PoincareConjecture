import PoincareConjecture.Proofs.M10.CalibratedTransport
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M14

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  (g : RiemannianMetric n M) (h : RiemannianMetric n N)
  (f : OpenPartialHomeomorph M N)
  (hsource : f.source = univ)
  (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
  (hfi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f.symm f.target)
  (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
    h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) =
      g.inner x v w)

include hf hmetric in
omit [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [T3Space N] [MeasurableSpace N] [BorelSpace N] in
private theorem captureChart_jacobian
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ c.source) :
    M10.pullbackJacobian h (c.trans f) z = M10.pullbackJacobian g c z := by
  have hd := mfderiv_comp z ((hf (c z)).mdifferentiableAt (by simp))
    ((hc.contMDiffAt (c.open_source.mem_nhds hz)).mdifferentiableAt (by simp))
  unfold M10.pullbackJacobian
  congr 1
  congr 1
  funext i j
  change h.inner (f (c z))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c) z (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c) z (EuclideanSpace.basisFun (Fin n) ℝ j)) =
    g.inner (c z)
      (mfderiv (𝓡 n) (𝓡 n) c z (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) c z (EuclideanSpace.basisFun (Fin n) ℝ j))
  rw [hd]
  exact hmetric (c z) _ _

include hsource hf hfi hmetric

private theorem captureChart_volume_local
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target)
    {B : Set M} (hB : MeasurableSet B) (hBc : B ⊆ c.target) :
    calibratedMetricVolume h (f '' B) = calibratedMetricVolume g B := by
  let A := c ⁻¹' B ∩ c.source
  have hsub : MeasurableSet ((Subtype.val : c.source → EuclideanSpace ℝ (Fin n)) ⁻¹'
      (c ⁻¹' B)) := hB.preimage c.continuousOn.domRestrict.measurable
  have hA : MeasurableSet A := by
    simpa only [A, Subtype.range_coe] using
      (MeasurableEmbedding.subtype_coe c.open_source.measurableSet).measurableSet_preimage.mp hsub
  have hAc : A ⊆ c.source := inter_subset_right
  have hcA : c '' A = B := by
    change c '' (c ⁻¹' B ∩ c.source) = B
    rw [image_preimage_inter, c.image_source_eq_target, inter_eq_left.mpr hBc]
  have hAf : A ⊆ (c.trans f).source := by
    intro z hz
    exact ⟨hAc hz, by rw [hsource]; exact mem_univ _⟩
  have hcf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (c.trans f) (c.trans f).source :=
    hf.comp_contMDiffOn (hc.mono inter_subset_left)
  have hcfi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (c.trans f).symm (c.trans f).target :=
    hci.comp (hfi.mono inter_subset_left) inter_subset_right
  have hcfA : (c.trans f) '' A = f '' B := by
    change (f ∘ c) '' A = f '' B
    exact (image_image f c A).symm.trans (congrArg (fun S => f '' S) hcA)
  rw [← hcfA, M10.calibratedMetricVolume_image_eq_lintegral h (c.trans f)
    (hcf.of_le (by simp)) (hcfi.of_le (by simp)) hA hAf,
    ← hcA, M10.calibratedMetricVolume_image_eq_lintegral g c
      (hc.of_le (by simp)) (hci.of_le (by simp)) hA hAc]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hA] with z hz
  rw [captureChart_jacobian g h f hf hmetric c hc (hAc hz)]

variable [SecondCountableTopology M]

theorem ordinaryCaptureChart_inverse_measure :
    ((calibratedMetricVolume h).restrict f.target).map f.symm = calibratedMetricVolume g := by
  let μ := ((calibratedMetricVolume h).restrict f.target).map f.symm
  let ν := calibratedMetricVolume g
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ A : Set M, MeasurableSet A → A ⊆ U → μ A = ν A := by
    let c := (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
    have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := contMDiffOn_chart_symm
    have hci : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target := contMDiffOn_chart
    refine ⟨c.target, c.open_target, mem_chart_source _ x, ?_⟩
    intro A hA hAU
    change ((calibratedMetricVolume h).restrict f.target).map f.symm A =
      calibratedMetricVolume g A
    rw [M10.map_inverse_restrict_apply f (calibratedMetricVolume h) hA
      (by rw [hsource]; exact subset_univ _)]
    exact captureChart_volume_local g h f hsource hf hfi hmetric c hc hci hA hAU
  ext A hA
  apply M10.measure_eq_of_local_comparisons (U := univ) (fun _ => (1 : ℝ≥0∞))
    tendsto_const_nhds ?_ ?_ hA (subset_univ A)
  · intro _ x _
    obtain ⟨U, hU, hx, heq⟩ := hlocal x
    exact ⟨U, hU, hx, fun B hB hBU => by rw [one_mul, heq B hB hBU]⟩
  · intro _ x _
    obtain ⟨U, hU, hx, heq⟩ := hlocal x
    exact ⟨U, hU, hx, fun B hB hBU => by rw [one_mul, heq B hB hBU]⟩

theorem ordinaryCaptureChart_volume_image {A : Set M} (hA : MeasurableSet A) :
    calibratedMetricVolume h (f '' A) = calibratedMetricVolume g A := by
  rw [← M10.map_inverse_restrict_apply f (calibratedMetricVolume h) hA
    (by rw [hsource]; exact subset_univ _),
    ordinaryCaptureChart_inverse_measure g h f hsource hf hfi hmetric]

theorem ordinaryCaptureChart_measure_map :
    (calibratedMetricVolume g).map f = (calibratedMetricVolume h).restrict f.target := by
  have hrange : range f = f.target := by
    rw [← image_univ, ← hsource, f.image_source_eq_target]
  ext A hA
  rw [Measure.map_apply hf.continuous.measurable hA,
    ← ordinaryCaptureChart_volume_image g h f hsource hf hfi hmetric
      (hA.preimage hf.continuous.measurable),
    image_preimage_eq_inter_range, hrange, Measure.restrict_apply hA]

theorem ordinaryCaptureChart_restrict_map {A : Set N}
    (hA : MeasurableSet A) (hAtarget : A ⊆ f.target) :
    ((calibratedMetricVolume g).restrict (f ⁻¹' A)).map f =
      (calibratedMetricVolume h).restrict A := by
  rw [← Measure.restrict_map hf.continuous.measurable hA,
    ordinaryCaptureChart_measure_map g h f hsource hf hfi hmetric,
    Measure.restrict_restrict hA, inter_eq_left.mpr hAtarget]

theorem ordinaryCaptureChart_integral {A : Set N}
    (hA : MeasurableSet A) (hAtarget : A ⊆ f.target) (φ : N → ℝ) :
    (∫ q in A, φ q ∂calibratedMetricVolume h) =
      ∫ c in f ⁻¹' A, φ (f c) ∂calibratedMetricVolume g := by
  rw [← ordinaryCaptureChart_restrict_map g h f hsource hf hfi hmetric hA hAtarget]
  exact (f.isOpenEmbedding hsource).measurableEmbedding.integral_map φ

end PoincareConjecture.M14
