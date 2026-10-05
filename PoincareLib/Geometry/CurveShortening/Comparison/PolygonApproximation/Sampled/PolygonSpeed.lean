import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Sampled.PolygonCloseness

/-!
# Uniform speed of sampled minimizing sides

The distance of adjacent sampled vertices is bounded by the source arc.
Since a minimizing side has length equal to its parameter-cell length times
its constant speed, the source loop's speed bound also bounds every side.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Every sampled minimizing side inherits the source loop's uniform speed bound. Source:
Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_sampled_polygon_side_speed_le
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N) (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiodic : Function.Periodic gamma curvePeriod)
    (hvertices : ∀ j : Fin N, polygon.vertices j = gamma (m63CellLeft N j))
    {S : ℝ} (hS : 0 ≤ S)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (gamma x) (curveVelocity gamma x) ≤ S) :
    ∀ j : Fin N, (polygon.side j).speed ≤ S := by
  intro j
  have hell : 0 < m63CellLength N := m63CellLength_pos hN
  have hleft : 0 ≤ m63CellLeft N j :=
    mul_nonneg (Nat.cast_nonneg _) hell.le
  have hj : (j.val : ℝ) + 1 ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hright : m63CellLeft N j + m63CellLength N ≤ curvePeriod := by
    calc
      _ = ((j.val : ℝ) + 1) * m63CellLength N := by
        dsimp only [m63CellLeft]
        ring
      _ ≤ (N : ℝ) * m63CellLength N :=
        mul_le_mul_of_nonneg_right hj hell.le
      _ = curvePeriod := m63_count_mul_cellLength hN
  have hadj : g.edist (polygon.vertices j) (polygon.vertices (finRotate N j)) ≤
      ENNReal.ofReal (S * m63CellLength N) := by
    rw [hvertices j, hvertices (finRotate N j),
      m63PeriodicLoop_cell_finish hperiodic hN j]
    simpa only [add_sub_cancel_left] using
      m64_c1_subarc_edist_le_speed g hgamma hleft
        (le_add_of_nonneg_right hell.le) hright hbound
  rw [(polygon.side j).edist_eq_length hell.le] at hadj
  have hlength : m63CellLength N * (polygon.side j).speed ≤
      S * m63CellLength N :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hS hell.le)).mp hadj
  nlinarith only [hlength, hell]

end PoincareMT
