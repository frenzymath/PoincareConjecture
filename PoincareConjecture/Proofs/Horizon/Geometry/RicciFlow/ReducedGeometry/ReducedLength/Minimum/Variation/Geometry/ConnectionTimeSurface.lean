import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ConnectionTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Surface









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

theorem chartConnectionBilinear_time_pairing_surface
    {J : Set ℝ} (F : RicciFlow 2 M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v w z : EuclideanSpace ℝ (Fin 2)) :
    chartActionMetric F T x (s, extChartAt (𝓡 2) x y)
        (fderiv ℝ (chartConnectionBilinear (chartActionMetric F T x))
          (s, extChartAt (𝓡 2) x y) (1, 0) v w) z =
      s * (mvfderiv (𝓡 2) (F.connection (T - s ^ 2)).scalarCurvature y
          (chartFrame x v y) * (F.metric (T - s ^ 2)).inner y
            (chartFrame x w y) (chartFrame x z y) +
        mvfderiv (𝓡 2) (F.connection (T - s ^ 2)).scalarCurvature y
          (chartFrame x w y) * (F.metric (T - s ^ 2)).inner y
            (chartFrame x v y) (chartFrame x z y) -
        mvfderiv (𝓡 2) (F.connection (T - s ^ 2)).scalarCurvature y
          (chartFrame x z y) * (F.metric (T - s ^ 2)).inner y
            (chartFrame x v y) (chartFrame x w y)) := by
  rw [chartConnectionBilinear_time_pairing F T s x y hy ht]
  simp only [backwardConnectionVariationPairing,
    LeviCivitaData.ricciDerivativePairing_surface]
  ring

theorem weighted_ricciDerivativePairing_chart_surface
    {J : Set ℝ} (F : RicciFlow 2 M J) (T s : ℝ) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
    (ht : T - s ^ 2 ∈ interior J) (v w z : EuclideanSpace ℝ (Fin 2)) :
    4 * s * ricciDerivativePairing (F.connection (T - s ^ 2)) y
        (chartFrame x v y) (chartFrame x w y) (chartFrame x z y) =
      chartActionMetric F T x (s, extChartAt (𝓡 2) x y)
          (fderiv ℝ (chartConnectionBilinear (chartActionMetric F T x))
            (s, extChartAt (𝓡 2) x y) (1, 0) v w) z +
        chartActionMetric F T x (s, extChartAt (𝓡 2) x y)
          (fderiv ℝ (chartConnectionBilinear (chartActionMetric F T x))
            (s, extChartAt (𝓡 2) x y) (1, 0) v z) w := by
  rw [chartConnectionBilinear_time_pairing F T s x y hy ht,
    chartConnectionBilinear_time_pairing F T s x y hy ht]
  simp only [backwardConnectionVariationPairing,
    LeviCivitaData.ricciDerivativePairing_surface]
  rw [(F.metric (T - s ^ 2)).symm y (chartFrame x z y) (chartFrame x w y)]
  ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
