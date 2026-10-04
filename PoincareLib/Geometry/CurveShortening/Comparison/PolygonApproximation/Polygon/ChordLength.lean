import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Polygon.Length
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Sampled.PolygonLength

/-!
# Sampled chord form of the polygon length

The side records in an actual sampled polygon are minimizing geodesics.
Consequently the derivative-integral length of the unsmoothed polygon is
exactly the sum of the intrinsic distances between adjacent sampled values.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}

/-- The actual polygon length is the sum of the sampled intrinsic chords. The periodicity
assumption is retained because this is the form used for sampled loops; the proof itself
only uses the vertex sampling equations. Source: Auxiliary step for MT Definition 19.18 and
Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64PolygonLength_eq_sampled_chord_sum
    (polygon : M63GeodesicPolygon g D N) (hN : 0 < N)
    (gamma : ℝ → M)
    (_hperiodic : Function.Periodic gamma curvePeriod)
    (_hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hvertices : ∀ j : Fin N,
      polygon.vertices j = gamma (m63CellLeft N j)) :
    m64PolygonLength polygon =
      ∑ j : Fin N,
        (g.edist (gamma (m63CellLeft N j))
          (gamma (m63CellLeft N (finRotate N j)))).toReal := by
  rw [m64PolygonLength_eq_sum polygon hN]
  apply Finset.sum_congr rfl
  intro j hj
  let ell : ℝ := m63CellLength N
  have hell : 0 ≤ ell := (m63CellLength_pos hN).le
  have hspeed : 0 ≤ (polygon.side j).speed :=
    (polygon.side j).speed_nonnegative
  have hdist := (polygon.side j).edist_eq_length hell
  have hdist' : g.edist (gamma (m63CellLeft N j))
      (gamma (m63CellLeft N (finRotate N j))) =
      ENNReal.ofReal (m63CellLength N * (polygon.side j).speed) := by
    calc
      g.edist (gamma (m63CellLeft N j))
          (gamma (m63CellLeft N (finRotate N j))) =
          g.edist (polygon.vertices j) (polygon.vertices (finRotate N j)) := by
            rw [hvertices j, hvertices (finRotate N j)]
      _ = ENNReal.ofReal (m63CellLength N * (polygon.side j).speed) := hdist
  have hnon : 0 ≤ ell * (polygon.side j).speed :=
    mul_nonneg hell hspeed
  symm
  rw [hdist', ENNReal.toReal_ofReal hnon]

end PoincareMT
