import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Finite

/-!
# Local coordinate action

The action uses the actual metric and scalar potential. Adapted from Mapher
`Proofs/M08/LocalMinimality.lean`, commit
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareMT.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def chartH1Action {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (a b : ℝ) (γ : ℝ → M) (w : IntervalL2 (EuclideanSpace ℝ (Fin n)) a b) : ℝ :=
  (∫ s in a..b, regularizedChartMetric F T x (s, γ s) (w s) (w s)) +
    ∫ s in a..b, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s)

end PoincareMT.ReducedLengthMinimum.Variational
