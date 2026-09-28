import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalFormula

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

set_option backward.isDefEq.respectTransparency false in

theorem volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hse : s ⊆ e.source) :
    g.volumeMeasure (e '' s) =
      ∫⁻ x in s, ENNReal.ofReal (g.pullbackVolumeDensity e x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have heDiff : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  change Measure.euclideanHausdorffMeasure n (e '' s) = _
  apply Poincare.HausdorffDensity.hausdorffMeasure_image_eq_lintegral_of_locally_linear_comparison
    e ?_ ?_ hs hse
  · intro x hx
    have h := g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx)) (heDiff.mfderiv_injective hx)
    exact ⟨h.1.continuousAt, h.2⟩
  · intro x hx K hK
    obtain ⟨A, hA, hdet⟩ := g.exists_frozenPullbackEquiv (heDiff.mfderiv_injective hx)
    obtain ⟨U, hU, hxU, hUe, hcomp⟩ :=
      g.exists_open_distortion_of_tangentNorm_comparison e he hei hx A hK
        (g.eventually_pullbackNorm_comparison
          (he.contMDiffAt (e.open_source.mem_nhds hx)) A hA hK)
    exact ⟨A, hdet, U, hU, hxU, hUe,
      fun z hz w hw ↦ (hcomp z hz w hw).1,
      fun z hz w hw ↦ (hcomp z hz w hw).2⟩

theorem map_restrict_volumeMeasure_symm
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    ((g.volumeMeasure.restrict e.target).map e.symm) =
      (volume.withDensity (fun x ↦ ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict
        e.source := by
  ext s hs
  have hm : AEMeasurable e.symm (g.volumeMeasure.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hset : e.symm ⁻¹' s ∩ e.target = e '' (s ∩ e.source) := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, ⟨hy.1, e.map_target hy.2⟩, e.right_inv hy.2⟩
    · rintro ⟨x, ⟨hxs, hxe⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, e.left_inv hxe], e.map_source hxe⟩
  rw [Measure.map_apply_of_aemeasurable hm hs,
    Measure.restrict_apply' e.open_target.measurableSet, hset,
    g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei
      (hs.inter e.open_source.measurableSet) inter_subset_right,
    Measure.restrict_apply hs, withDensity_apply _ (hs.inter e.open_source.measurableSet)]

end PoincareConjecture.RiemannianMetric
