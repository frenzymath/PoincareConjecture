import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Fubini
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Poincare.Coarea Poincare.EuclideanSpace
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

private theorem measurableSet_chart_symm_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (c : OpenPartialHomeomorph X Y) {s : Set Y}
    (hs : MeasurableSet s) (hsc : s ⊆ c.target) :
    MeasurableSet (c.symm '' s) := by
  have h := c.open_source.measurableSet.subtype_image
    (c.continuousOn.domRestrict.measurable hs)
  convert h using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨c.symm y, c.map_target (hsc hy)⟩, by
      simpa only [mem_preimage, domRestrict_apply, c.right_inv (hsc hy)] using hy, rfl⟩
  · rintro ⟨⟨x, hx⟩, hy, rfl⟩
    exact ⟨c x, hy, c.left_inv hx⟩

variable {n : ℕ} {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
  [T3Space N] [T3Space M] [MeasurableSpace N] [BorelSpace N]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 (n + 1)) ∞ M]
  (h : RiemannianMetric n N) (g : RiemannianMetric (n + 1) M)
  (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
  (hmetric : ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
    g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
        h.inner z.1 v.1 w.1 + v.2 * w.2)

include hmetric

theorem volumeMeasure_productIsometry_chart_rectangle
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target)
    {s : Set N} {t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : s ⊆ c.target) :
    g.volumeMeasure (e '' (s ×ˢ t)) = h.volumeMeasure s * volume t := by
  let a := c.symm '' s
  have ha : MeasurableSet a := measurableSet_chart_symm_image c hs hsc
  have hac : a ⊆ c.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_target (hsc hy)
  have hca : c '' a = s := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [c.right_inv (hsc hz)] using hz
    · intro hy
      exact ⟨c.symm y, ⟨y, hy, rfl⟩, c.right_inv (hsc hy)⟩
  let b := euclideanConsEquiv n '' (t ×ˢ a)
  have hb : MeasurableSet b := (euclideanConsEquiv n).measurableSet_image.mpr (ht.prod ha)
  have hbc : b ⊆ (productVolumeChart e c).source := by
    rintro _ ⟨⟨t', y⟩, hy, rfl⟩
    simpa using hac hy.2
  have hdb : productVolumeChart e c '' b = e '' (s ×ˢ t) := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨t', y⟩, hy, rfl⟩, rfl⟩
      refine ⟨(c y, t'), ⟨?_, hy.1⟩, ?_⟩
      · rw [← hca]
        exact mem_image_of_mem c hy.2
      · simp
    · rintro ⟨⟨y, t'⟩, hy, rfl⟩
      refine ⟨euclideanConsEquiv n (t', c.symm y),
        ⟨(t', c.symm y), ⟨hy.2, ⟨y, hy.1, rfl⟩⟩, rfl⟩, ?_⟩
      simp [c.right_inv (hsc hy.1)]
  rw [← hdb, g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    (productVolumeChart e c) (contMDiffOn_productVolumeChart e c hc)
    (contMDiffOn_productVolumeChart_symm e c hci) hb hbc]
  have hdensity : (∫⁻ x in b, ENNReal.ofReal (g.pullbackVolumeDensity (productVolumeChart e c) x)) =
      ∫⁻ x in b, ENNReal.ofReal (h.pullbackVolumeDensity c (euclideanTail x)) := by
    apply setLIntegral_congr_fun hb
    intro x hx
    exact congrArg ENNReal.ofReal
      (pullbackVolumeDensity_productVolumeChart h g e hmetric c hc (hbc hx))
  rw [hdensity]
  have hρ : AEMeasurable (fun y => ENNReal.ofReal (h.pullbackVolumeDensity c y))
      (volume.restrict a) := by
    apply ContinuousOn.aemeasurable _ ha
    intro y hy
    apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
    exact (h.contDiffAt_pullbackVolumeDensity
      (hc.contMDiffAt (c.open_source.mem_nhds (hac hy)))
      (OpenPartialHomeomorph.MDifferentiable.mfderiv_injective
        ⟨hc.mdifferentiableOn (by simp), hci.mdifferentiableOn (by simp)⟩ (hac hy))).1.continuousAt.continuousWithinAt
  rw [lintegral_euclideanCons_image_tail hρ,
    ← h.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity c hc hci ha hac, hca]

theorem measurePreserving_productIsometry [SecondCountableTopology N] :
    MeasurePreserving e (h.volumeMeasure.prod volume) g.volumeMeasure := by
  have hmap : g.volumeMeasure.map e.symm = h.volumeMeasure.prod volume := by
    apply measure_eq_prod_of_local_rectangles _ _ _
      (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) y).source)
      (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) y).open_source)
      (fun y => mem_chart_source _ y)
    intro y s t hs ht hsc
    rw [Measure.map_apply e.symm.contMDiff.continuous.measurable (hs.prod ht)]
    have heq : e.symm ⁻¹' (s ×ˢ t) = e '' (s ×ˢ t) := by
      ext x
      constructor
      · exact fun hx => ⟨e.symm x, hx, e.apply_symm_apply x⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    rw [heq]
    exact volumeMeasure_productIsometry_chart_rectangle h g e hmetric
      (chartAt (EuclideanSpace ℝ (Fin n)) y).symm
      contMDiffOn_chart_symm contMDiffOn_chart hs ht hsc
  refine ⟨e.contMDiff.continuous.measurable, ?_⟩
  rw [← hmap, Measure.map_map e.contMDiff.continuous.measurable
    e.symm.contMDiff.continuous.measurable]
  have heq : (e ∘ e.symm : M → M) = id := funext e.apply_symm_apply
  rw [heq, Measure.map_id]

end PoincareConjecture.RiemannianMetric
