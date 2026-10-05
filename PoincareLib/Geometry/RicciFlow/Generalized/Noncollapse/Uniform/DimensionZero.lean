import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.Calibration
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Combined

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Thm8_1_DimensionZero.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# The zero-dimensional generalized conclusion

The dimension-zero extension of Morgan-Tian Theorem 8.1, p. 169, in the
frozen M15 contract. Nonempty sets have calibrated volume at least one,
so the uniform noncollapsing constant is one. See
`references/ricci-flow/mapher/noncollapse/derivations/2026-09-20-dimension-zero.md`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [IsManifold (𝓡 0) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- Nonempty sets have at least unit calibrated volume in dimension zero.
This handles the zero-dimensional extension of Theorem 8.1, p. 169. -/
theorem one_le_calibratedMetricVolume_zero (g : RiemannianMetric 0 M)
    {A : Set M} (hA : A.Nonempty) : 1 ≤ calibratedMetricVolume g A := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 0) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 0))
      (TangentSpace (𝓡 0) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 0) M
  rw [calibratedMetricVolume_eq_euclideanHausdorff,
    Measure.euclideanHausdorffMeasure_zero]
  exact Measure.one_le_hausdorffMeasure_zero_of_nonempty hA

/-- A positive-radius ball has at least unit calibrated volume in
dimension zero. Source: Theorem 8.1, p. 169, in the frozen all-dimension form. -/
theorem one_le_calibratedMetricVolume_ball_zero (g : RiemannianMetric 0 M)
    (x : M) {r : ℝ} (hr : 0 < r) : 1 ≤ calibratedMetricVolume g (g.ball x r) := by
  apply one_le_calibratedMetricVolume_zero g
  refine ⟨x, ?_⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 0) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 0))
      (TangentSpace (𝓡 0) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 0) M
  change edist x x < ENNReal.ofReal r
  rw [edist_self]
  exact ENNReal.ofReal_pos.mpr hr

/-- The generalized clause of Theorem 8.1, p. 169, has uniform constant
one in dimension zero. No predecessor theorem is needed for this branch. -/
theorem generalizedUniformTheorem_zero : M15GeneralizedUniformTheorem.{u} 0 := by
  intro taubar l₀ V htaubar hl₀ hV
  refine ⟨{
    taubar_pos := htaubar
    l₀_pos := hl₀
    V_pos := hV
    kappa := 1
    kappa_pos := zero_lt_one
    estimate := ?_
  }⟩
  intro X instX time I G T x E r K C instC instChart instManifold instT2 instCount B D
  simpa only [M15Theorem81Estimate, pow_zero, mul_one, ENNReal.ofReal_one] using
    one_le_calibratedMetricVolume_ball_zero (G.slices T).metricOnPoints x B.radius_pos

end PoincareMT.Generalized.Noncollapse
