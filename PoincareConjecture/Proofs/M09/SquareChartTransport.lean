import PoincareConjecture.Proofs.M09.CoordinateTransport
import PoincareConjecture.Proofs.M09.SquareChartConnection








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareChartTransport_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (a v w : E) :
    let x := (chartAt E p).symm y
    (F.metric (T - s ^ 2)).inner x
      (chartVectorField p (coordinateTransportOperator (squareChartMetric F T p) (s, y) a v) x +
        (F.connection (T - s ^ 2)).connection (chartVectorField p v) x (chartVectorField p a x))
      (chartVectorField p w x) =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci x
          (chartVectorField p v x) (chartVectorField p w x) := by
  dsimp only
  have h := coordinateTransportOperator_pairing (squareChartMetric F T p) (s, y)
    (fun z hz ↦ squareChartMetric_pos F T p (s, y) hy z hz) a v w
  rw [squareChartMetric_time_pairing F T b hb hwindow p s hs y v w hy] at h
  have hsum :
      squareChartMetric F T p (s, y)
          (coordinateTransportOperator (squareChartMetric F T p) (s, y) a v) w +
        squareChartMetric F T p (s, y)
          (coordinateConnection (squareChartMetric F T p) (s, y) a v) w =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci ((chartAt E p).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) := by
    rw [h]
    ring
  rw [← squareChartConnection_eq F T b hb hwindow p s hs y hy a v]
  simp only [map_add, add_apply, chartVectorField_at_inverse p _ y hy]
  exact hsum

end PoincareConjecture.Proofs.M09
