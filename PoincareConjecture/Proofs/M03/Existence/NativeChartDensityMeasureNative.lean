import PoincareConjecture.Proofs.M03.Existence.NativeChartDensitySmoothNative
import PoincareConjecture.Proofs.M03.Existence.ChartPushforwardLpNative









set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative

open ChartPushforwardLpNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)


theorem weightedChartMeasure_apply_chart_image (e : OpenPartialHomeomorph M E) (φ : C(M, ℝ))
    {S : Set M} (hS : MeasurableSet S) :
    weightedChartMeasure e φ S =
      ∫⁻ z in e '' (S ∩ e.source), ENNReal.ofReal (φ (e.symm z)) := by
  rw [weightedChartMeasure, Measure.map_apply_of_aemeasurable (chartInverse_aemeasurable e φ) hS,
    weightedSourceMeasure, withDensity_apply',
    Measure.restrict_restrict' e.open_target.measurableSet]
  have hset : e.symm ⁻¹' S ∩ e.target = e '' (S ∩ e.source) := by
    ext z
    constructor
    · rintro ⟨hzS, hzt⟩
      exact ⟨e.symm z, ⟨hzS, e.map_target hzt⟩, e.right_inv hzt⟩
    · rintro ⟨x, ⟨hxS, hxs⟩, rfl⟩
      refine ⟨?_, e.map_source hxs⟩
      change e.symm (e x) ∈ S
      rwa [e.left_inv hxs]
  rw [hset]

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chartWeightDensity_measure_apply (p q : M) {φ : M → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) {B : Set E} (hB : MeasurableSet B) :
    ((volume.restrict (chartAt E p).target).withDensity
      (fun z => ENNReal.ofReal (chartWeightDensity p q φ z))) B =
      ∫⁻ z in B ∩ (chartTransition p q).source,
        ENNReal.ofReal (φ ((chartAt E p).symm z)) *
          ENNReal.ofReal (chartTransitionJacobian p q z) := by
  have heq : (fun z => ENNReal.ofReal (chartWeightDensity p q φ z)) =
      (chartTransition p q).source.indicator (fun z =>
        ENNReal.ofReal (φ ((chartAt E p).symm z)) *
          ENNReal.ofReal (chartTransitionJacobian p q z)) := by
    funext z
    by_cases hz : z ∈ (chartTransition p q).source
    · rw [chartWeightDensity_of_mem p q φ hz, indicator_of_mem hz,
        ENNReal.ofReal_mul (hφ _)]
    · rw [chartWeightDensity_of_notMem p q φ hz, ENNReal.ofReal_zero, indicator_of_notMem hz]
  rw [withDensity_apply _ hB, heq, Measure.restrict_restrict hB,
    lintegral_indicator (chartTransition p q).open_source.measurableSet,
    Measure.restrict_restrict (chartTransition p q).open_source.measurableSet]
  have hset : (chartTransition p q).source ∩ (B ∩ (chartAt E p).target) =
      B ∩ (chartTransition p q).source := by
    ext z
    constructor
    · rintro ⟨hzU, hzB, _⟩
      exact ⟨hzB, hzU⟩
    · rintro ⟨hzB, hzU⟩
      exact ⟨hzU, hzB, hzU.1⟩
  rw [hset]


theorem map_restrict_weightedChartMeasure_eq_density (p q : M) (φ : C(M, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) :
    ((weightedChartMeasure (chartAt E q) φ).restrict (chartAt E p).source).map
      (measurableChart (chartAt E p)) =
      (volume.restrict (chartAt E p).target).withDensity
        (fun z => ENNReal.ofReal (chartWeightDensity p q φ z)) := by
  let e : OpenPartialHomeomorph M E := chartAt E p
  let f : OpenPartialHomeomorph M E := chartAt E q
  let T : OpenPartialHomeomorph E E := chartTransition p q
  apply Measure.ext
  intro B hB
  have hpre : MeasurableSet (measurableChart e ⁻¹' B) := hB.preimage (measurable_measurableChart e)
  rw [Measure.map_apply (measurable_measurableChart e) hB, Measure.restrict_apply hpre,
    weightedChartMeasure_apply_chart_image f φ (hpre.inter e.open_source.measurableSet),
    chartWeightDensity_measure_apply p q hφ hB]
  have himage : f '' ((measurableChart e ⁻¹' B ∩ e.source) ∩ f.source) =
      T '' (B ∩ T.source) := by
    ext y
    constructor
    · rintro ⟨x, ⟨⟨hxB, hxe⟩, hxf⟩, rfl⟩
      refine ⟨e x, ⟨?_, e.map_source hxe, ?_⟩, ?_⟩
      · change measurableChart e x ∈ B at hxB
        rwa [measurableChart_of_mem e hxe] at hxB
      · change e.symm (e x) ∈ f.source
        rwa [e.left_inv hxe]
      · change f (e.symm (e x)) = f x
        rw [e.left_inv hxe]
    · rintro ⟨z, ⟨hzB, hzt, hzq⟩, rfl⟩
      refine ⟨e.symm z, ⟨⟨?_, e.map_target hzt⟩, hzq⟩, rfl⟩
      change measurableChart e (e.symm z) ∈ B
      rwa [measurableChart_of_mem e (e.map_target hzt), e.right_inv hzt]
  rw [himage]
  have hBT : MeasurableSet (B ∩ T.source) := hB.inter T.open_source.measurableSet
  have hderiv (z : E) (hz : z ∈ B ∩ T.source) :
      HasFDerivWithinAt T (fderiv ℝ T z) (B ∩ T.source) z :=
    (((chartTransition_contDiffOn p q).contDiffAt (T.open_source.mem_nhds hz.2)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBT hderiv
    (T.injOn.mono inter_subset_right)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hBT] with z hz
  change ENNReal.ofReal (chartTransitionJacobian p q z) *
      ENNReal.ofReal (φ (f.symm (f (e.symm z)))) =
    ENNReal.ofReal (φ (e.symm z)) * ENNReal.ofReal (chartTransitionJacobian p q z)
  have hzq : e.symm z ∈ f.source := hz.2.2
  have hback : f.symm (f (e.symm z)) = e.symm z := f.left_inv hzq
  rw [hback, mul_comm]

namespace FiniteChartData

variable (d : FiniteChartData (n := n) (M := M))


theorem map_measurableChart_eq_density (p : M) :
    (d.measure.restrict (chartAt E p).source).map (measurableChart (chartAt E p)) =
      (volume.restrict (chartAt E p).target).withDensity
        (fun z => ENNReal.ofReal (d.chartDensity p z)) := by
  classical
  let e : OpenPartialHomeomorph M E := chartAt E p
  apply Measure.ext
  intro B hB
  have hpre : MeasurableSet (measurableChart e ⁻¹' B) := hB.preimage (measurable_measurableChart e)
  rw [Measure.map_apply (measurable_measurableChart e) hB, Measure.restrict_apply hpre,
    measure, Measure.sum_apply _ (hpre.inter e.open_source.measurableSet), tsum_fintype]
  have hi (i : d.centers) :
      weightedChartMeasure (d.chart i) (d.weight i) (measurableChart e ⁻¹' B ∩ e.source) =
        ((volume.restrict e.target).withDensity
          (fun z => ENNReal.ofReal (chartWeightDensity p i.val (d.weight i) z))) B := by
    have h := congrArg (fun μ : Measure E => μ B)
      (map_restrict_weightedChartMeasure_eq_density p i.val (d.weight i) (d.weight_nonneg i))
    change (Measure.map (measurableChart e)
      ((weightedChartMeasure (d.chart i) (d.weight i)).restrict e.source)) B = _ at h
    rw [Measure.map_apply (measurable_measurableChart e) hB,
      Measure.restrict_apply hpre] at h
    exact h
  simp_rw [hi, withDensity_apply _ hB]
  have hsum : (fun z => ENNReal.ofReal (d.chartDensity p z)) =
      (fun z => ∑ i : d.centers, ENNReal.ofReal (chartWeightDensity p i.val (d.weight i) z)) := by
    funext z
    exact ENNReal.ofReal_sum_of_nonneg
      (fun i _ => chartWeightDensity_nonneg p i.val (d.weight_nonneg i) z)
  rw [hsum]
  symm
  apply lintegral_finsetSum'
  intro i _
  exact ((chartWeightDensity_contDiffOn p i.val (d.weight_smooth i)
    (d.weight_support_subset i)).continuousOn.aemeasurable e.open_target.measurableSet).ennreal_ofReal.restrict


theorem map_chart_eq_density (p : M) :
    (d.measure.restrict (chartAt E p).source).map (chartAt E p) =
      (volume.restrict (chartAt E p).target).withDensity
        (fun z => ENNReal.ofReal (d.chartDensity p z)) := by
  apply (Measure.map_congr ?_).trans (d.map_measurableChart_eq_density p)
  filter_upwards [ae_restrict_mem (chartAt E p).open_source.measurableSet] with x hx
  exact (measurableChart_of_mem (chartAt E p) hx).symm

end FiniteChartData

end PoincareConjecture.ChartMeasureNative
