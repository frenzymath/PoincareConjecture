import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.Topology.MetricSpace.HausdorffDimension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S]

private theorem volumeMeasure_curve_image_eq_zero_in_chart
    (g : RiemannianMetric 2 S) {γ : ℝ → S} {s : Set ℝ}
    (hs : IsCompact s) (hconv : Convex ℝ s)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ s)
    (p : S) (hchart : MapsTo γ s (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    g.volumeMeasure (γ '' s) = 0 := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
  let F := e ∘ γ
  have hF : ContDiffOn ℝ ∞ F s :=
    ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := p)).comp hγ hchart).contDiffOn
  have hdim : dimH (F '' s) < (2 : ℝ≥0∞) := by
    calc
      dimH (F '' s) ≤ dimH s := (hF.of_le (by simp)).dimH_image_le hconv Subset.rfl
      _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
      _ = 1 := Real.dimH_univ
      _ < 2 := by norm_num
  have hnull : volume (F '' s) = 0 := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2,
      Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    have hH : Measure.hausdorffMeasure 2 (F '' s) = 0 := by
      simpa using hausdorffMeasure_of_dimH_lt (d := (2 : ℝ≥0)) (by simpa using hdim)
    simp [hH]
  have himg : e.symm '' (F '' s) = γ '' s := by
    rw [← image_comp]
    exact image_congr fun t ht => e.left_inv (hchart ht)
  rw [← himg, g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e.symm
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := p))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := p))
    (hs.image_of_continuousOn hF.continuousOn).measurableSet
    (by rintro _ ⟨t, ht, rfl⟩; exact e.map_source (hchart ht)),
    Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]



theorem volumeMeasure_image_curve_eq_zero
    (g : RiemannianMetric 2 S) {γ : ℝ → S} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ (Icc a b)) :
    g.volumeMeasure (γ '' Icc a b) = 0 := by
  classical
  have hlocal (t : Icc a b) : ∃ r > 0,
      g.volumeMeasure (γ '' (Icc a b ∩ Metric.ball (t : ℝ) r)) = 0 := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) (γ t)
    have hn : γ ⁻¹' e.source ∈ 𝓝[Icc a b] (t : ℝ) :=
      (hγ.continuousOn t t.property).preimage_mem_nhdsWithin
        (e.open_source.mem_nhds (mem_chart_source _ _))
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hn
    refine ⟨r / 2, half_pos hr, ?_⟩
    apply measure_mono_null (image_mono (inter_subset_inter_right _
      Metric.ball_subset_closedBall))
    apply g.volumeMeasure_curve_image_eq_zero_in_chart
      (isCompact_Icc.inter_right Metric.isClosed_closedBall)
      ((convex_Icc a b).inter (convex_closedBall (t : ℝ) (r / 2)))
      (hγ.mono inter_subset_left) (γ t)
    intro x hx
    apply hsub
    exact ⟨lt_of_le_of_lt hx.2 (half_lt_self hr), hx.1⟩
  choose r hr hzero using hlocal
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : Icc a b => Metric.ball (t : ℝ) (r t)) (fun _ => Metric.isOpen_ball)
    (by intro t ht; exact mem_iUnion.mpr ⟨⟨t, ht⟩, Metric.mem_ball_self (hr ⟨t, ht⟩)⟩)
  apply measure_mono_null (t := ⋃ t ∈ T, γ '' (Icc a b ∩ Metric.ball (t : ℝ) (r t)))
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu, htu⟩ := mem_iUnion₂.mp (hT ht)
    exact mem_iUnion₂.mpr ⟨u, hu, ⟨t, ⟨ht, htu⟩, rfl⟩⟩
  · exact (measure_biUnion_null_iff T.countable_toSet).mpr fun t _ => hzero t


theorem volumeMeasure_singleton_eq_zero (g : RiemannianMetric 2 S) (p : S) :
    g.volumeMeasure {p} = 0 := by
  simpa using g.volumeMeasure_image_curve_eq_zero
    (γ := fun _ => p) (a := 0) (b := 1) contMDiffOn_const

end PoincareConjecture.RiemannianMetric
