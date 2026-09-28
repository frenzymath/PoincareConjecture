import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ChartSegment
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_lipschitz_chart_ball (g : RiemannianMetric n M) (p : M) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      Metric.ball (extChartAt (𝓡 n) p p) r ⊆ (extChartAt (𝓡 n) p).target ∧
      ∀ z ∈ Metric.ball (extChartAt (𝓡 n) p p) r,
      ∀ w ∈ Metric.ball (extChartAt (𝓡 n) p p) r,
        g.edist ((extChartAt (𝓡 n) p).symm z) ((extChartAt (𝓡 n) p).symm w) ≤
          (C : ℝ≥0∞) * EDist.edist z w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  obtain ⟨C, _, hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt (𝓡 n) p
  have hbound : ∀ᶠ z in 𝓝 (extChartAt (𝓡 n) p p),
      ‖mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm z‖ₑ < C := by
    simpa only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ,
      mfderivWithin_univ] using hC
  have htarget : (extChartAt (𝓡 n) p).target ∈ 𝓝 (extChartAt (𝓡 n) p p) := by
    simpa only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓡 n) p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hbound)
  refine ⟨C, r, hr, fun z hz ↦ (hball hz).1, fun z hz w hw ↦ ?_⟩
  apply Poincare.riemannianEDist_le_mul_edist_of_convex (convex_ball _ _) ?_ ?_ hz hw
  · intro y hy
    simpa only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ] using
      contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := 1) p (hball hy).1
  · exact fun y hy ↦ (hball hy).2.le

set_option backward.isDefEq.respectTransparency false in

theorem volumeMeasure_isLocallyFinite (g : RiemannianMetric n M) :
    IsLocallyFiniteMeasure (volumeMeasure g) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have : IsLocallyFiniteMeasure (Measure.hausdorffMeasure (n : ℝ) : Measure M) := by
    refine ⟨fun p ↦ ?_⟩
    obtain ⟨C, r, hr, _, hdist⟩ := exists_lipschitz_chart_ball g p
    let e := extChartAt (𝓡 n) p
    let B := Metric.ball (e p) r
    let U := e.source ∩ e ⁻¹' B
    have hU : U ∈ 𝓝 p := inter_mem
      (by simpa only [e, extChartAt_source] using
        chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) p)
      ((continuousAt_extChartAt p).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
    have hsub : U ⊆ e.symm '' B := by
      intro y hy
      exact ⟨e y, hy.2, e.left_inv hy.1⟩
    have hLip : LipschitzOnWith C e.symm B := hdist
    have hB : (Measure.hausdorffMeasure (n : ℝ) :
        Measure (EuclideanSpace ℝ (Fin n))) B < ⊤ :=
      (measure_mono Metric.ball_subset_closedBall).trans_lt
        (isCompact_closedBall _ _).measure_lt_top
    refine ⟨U, hU, lt_of_le_of_lt (measure_mono hsub) ?_⟩
    apply lt_of_le_of_lt (hLip.hausdorffMeasure_image_le (by positivity))
    exact ENNReal.mul_lt_top (by finiteness) hB
  change IsLocallyFiniteMeasure (Measure.euclideanHausdorffMeasure n : Measure M)
  rw [Measure.euclideanHausdorffMeasure_def]
  infer_instance

attribute [instance] volumeMeasure_isLocallyFinite

theorem volumeMeasure_lt_top_of_isCompact (g : RiemannianMetric n M)
    {s : Set M} (hs : IsCompact s) : volumeMeasure g s < ⊤ :=
  hs.measure_lt_top

theorem integrable_volumeMeasure_of_hasCompactSupport (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : Continuous f) (hcompact : HasCompactSupport f) :
    Integrable f (volumeMeasure g) :=
  hf.integrable_of_hasCompactSupport hcompact

instance volumeMeasure_sigmaFinite [SecondCountableTopology M]
    (g : RiemannianMetric n M) : SigmaFinite (volumeMeasure g) := by
  infer_instance

end PoincareConjecture.RiemannianMetric
