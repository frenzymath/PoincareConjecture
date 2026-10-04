import PoincareLib.Geometry.Riemannian.Surface.Integrability

/-!
# Positive and negative parts of the scalar integral

Compactness gives integrability without orientability or curvature-sign
assumptions. The decomposition here identifies the two formulations of the
closed-surface bound used in Petrunin, Section 4.4, author manuscript p. 8.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Scalar curvature integrates as its positive part minus its negative part. -/
theorem integral_scalarCurvature_eq_posPart_sub_negPart (D : LeviCivitaData g) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) -
        ∫ x, max 0 (-D.scalarCurvature x) ∂g.volumeMeasure := by
  calc
    _ = ∫ x, max 0 (D.scalarCurvature x) - max 0 (-D.scalarCurvature x)
        ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : 0 ≤ D.scalarCurvature x
      · simp [max_eq_right hx, max_eq_left (neg_nonpos.mpr hx)]
      · simp [max_eq_left (le_of_not_ge hx),
          max_eq_right (neg_nonneg.mpr (le_of_not_ge hx))]
    _ = _ := integral_sub D.integrable_scalarCurvature_posPart
      D.integrable_scalarCurvature_negPart

/-- A signed scalar integral bound is equivalent to the positive-part bound. -/
theorem integral_scalarCurvature_le_iff_posPart (D : LeviCivitaData g) (C : ℝ) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ C ↔
      (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        C + ∫ x, max 0 (-D.scalarCurvature x) ∂g.volumeMeasure := by
  rw [D.integral_scalarCurvature_eq_posPart_sub_negPart, sub_le_iff_le_add]

end PoincareMT.LeviCivitaData
