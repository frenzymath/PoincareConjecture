import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Flattened.PolygonGeometry
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.Energy

/-!
# Exact length of the actual flattened polygon

The actual speed is continuous and equals side speed times the normalized
profile on each closed cell. Periodicity and finite adjacent integration
therefore recover the exact sum of side lengths. Claim 19.22, MT2007
pp. 452-453; see `2026-09-21-flattened-polygon-length.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b))

/-- Flattening preserves the sum of the actual side lengths, with the
calibrated cell length multiplying side speed. Claim 19.22, pp. 452-453. -/
theorem m63FlattenedPolygon_length (t : ℝ) {N : ℕ}
    (polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N) (hN : 0 < N) :
    m62Length F (fun x _ => m63FlattenedPolygon polygon x) t =
      ∑ j : Fin N, m63CellLength N * (polygon.side j).speed := by
  let ell := m63CellLength N
  let v : ℝ → ℝ := fun x => curveSpeed F (fun y _ => m63FlattenedPolygon polygon y) t x
  have hell : 0 < ell := m63CellLength_pos hN
  have hv : Continuous v := M04.continuous_pathSpeed (F.metric t)
    ((m63FlattenedPolygon_smooth polygon hN).of_le (by simp))
  have hcell (j : Fin N) :
      (∫ x in m63CellLeft N j..(m63CellLeft N j + ell), v x) = ell * (polygon.side j).speed := by
    have hab : m63CellLeft N j ≤ m63CellLeft N j + ell := le_add_of_nonneg_right hell.le
    have heq : (∫ x in m63CellLeft N j..(m63CellLeft N j + ell), v x) =
        ∫ x in m63CellLeft N j..(m63CellLeft N j + ell),
          (polygon.side j).speed * m63Profile N x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      have hs : x - m63CellLeft N j ∈ Icc 0 ell := by constructor <;> linarith [hx.1, hx.2]
      have h := m63FlattenedPolygon_cell_speed polygon hN j hs
      change v (m63CellLeft N j + (x - m63CellLeft N j)) =
        (polygon.side j).speed * m63Profile N (m63CellLeft N j + (x - m63CellLeft N j)) at h
      have hxsum : m63CellLeft N j + (x - m63CellLeft N j) = x := by ring
      simpa only [hxsum] using h
    rw [heq, intervalIntegral.integral_const_mul]
    have hprofile : (∫ x in m63CellLeft N j..(m63CellLeft N j + ell), m63Profile N x) = ell := by
      have h := (m63Profile_periodic hN).intervalIntegral_add_eq (m63CellLeft N j) 0
      simpa only [zero_add, m63Profile_cell_integral hN] using h
    rw [hprofile, mul_comm]
  have hsum : (∑ j : Fin N, ∫ x in m63CellLeft N j..(m63CellLeft N j + ell), v x) =
      ∫ x in (0 : ℝ)..curvePeriod, v x := by
    have htel := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * ell) (n := N) (μ := MeasureTheory.volume)
      (fun _ _ => hv.intervalIntegrable _ _)
    rw [← Fin.sum_univ_eq_sum_range] at htel
    simpa only [ell, m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Nat.cast_zero, zero_mul, m63_count_mul_cellLength hN, curvePeriod] using htel
  change (∫ x in (0 : ℝ)..curvePeriod, v x) = ∑ j : Fin N, ell * (polygon.side j).speed
  rw [← hsum]
  exact Finset.sum_congr rfl (fun j _ => hcell j)

end PoincareMT
