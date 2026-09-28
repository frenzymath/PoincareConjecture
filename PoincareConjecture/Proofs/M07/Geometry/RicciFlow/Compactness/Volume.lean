import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Basic

set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff Bundle NNReal ENNReal Topology

namespace PoincareConjecture

theorem FlowCarrier.volumeMeasure_eq_smul_metricHausdorffVolume
    {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : T3Space C.carrier := C.t3Space
    RiemannianMetric.volumeMeasure g =
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)) • C.metricHausdorffVolume g := by
  rfl

theorem PointedRicciFlowCompactnessHypotheses.normalized_noncollapsing
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    ∃ r₀ κ : ℝ, 0 < r₀ ∧ 0 < κ ∧ ∀ᶠ k : ℕ in atTop,
      let C := H.sequence.carrier k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : MeasurableSpace C.carrier := C.measurableSpace
      letI : BorelSpace C.carrier := C.borelSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      letI : T3Space C.carrier := C.t3Space
      ENNReal.ofReal (κ * r₀ ^ n) ≤
        RiemannianMetric.volumeMeasure ((H.sequence.flow k).metricAt 0)
          ((H.sequence.flow k).zeroBall r₀) := by
  let c : ℝ≥0 := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Measure.hausdorffMeasure (n : ℝ))
  have hc : 0 < c := pos_iff_ne_zero.mpr
    (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  obtain ⟨r₀, κ, hr₀, hκ, hbound⟩ := H.noncollapsing
  refine ⟨r₀, (c : ℝ) * κ, hr₀, mul_pos (by exact_mod_cast hc) hκ, ?_⟩
  filter_upwards [hbound] with k hk
  let C := H.sequence.carrier k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : MeasurableSpace C.carrier := C.measurableSpace
  let : BorelSpace C.carrier := C.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : T3Space C.carrier := C.t3Space
  change ENNReal.ofReal ((c : ℝ) * κ * r₀ ^ n) ≤
    RiemannianMetric.volumeMeasure ((H.sequence.flow k).metricAt 0)
      ((H.sequence.flow k).zeroBall r₀)
  rw [C.volumeMeasure_eq_smul_metricHausdorffVolume]
  change ENNReal.ofReal ((c : ℝ) * κ * r₀ ^ n) ≤
    (c : ℝ≥0∞) * C.metricHausdorffVolume ((H.sequence.flow k).metricAt 0)
      ((H.sequence.flow k).zeroBall r₀)
  rw [mul_assoc, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  gcongr
  have hvolume : (H.sequence.flow k).volumeMeasure =
      C.metricHausdorffVolume ((H.sequence.flow k).metricAt 0) :=
    H.volume_compatibility k
  simpa only [BasedFlow.zeroBallVolume, hvolume] using hk

end PoincareConjecture
