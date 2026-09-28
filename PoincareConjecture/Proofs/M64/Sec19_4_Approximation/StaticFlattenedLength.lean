import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonGeometry
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonLength













set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}



theorem m64FlattenedPolygon_length {N : ℕ}
    (polygon : M63GeodesicPolygon g D N) (hN : 0 < N) :
    (∫ x in (0 : ℝ)..curvePeriod,
      g.tangentNorm (m63FlattenedPolygon polygon x)
        (curveVelocity (n := n) (m63FlattenedPolygon polygon) x)) =
      ∑ j : Fin N, m63CellLength N * (polygon.side j).speed := by
  let ell := m63CellLength N
  let v : ℝ → ℝ := fun x => g.tangentNorm (m63FlattenedPolygon polygon x)
    (curveVelocity (n := n) (m63FlattenedPolygon polygon) x)
  have hell : 0 < ell := m63CellLength_pos hN
  have hv : Continuous v := M04.continuous_pathSpeed g
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




theorem m64_freeLoopLength_eq_polygonLength
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N) (polygon : M63GeodesicPolygon g D N)
    (gamma : C1FreeLoopSpace (M := M))
    (heq : ∀ x : ℝ, periodicFreeLoop gamma x = m63FlattenedPolygon polygon x) :
    freeLoopLength g gamma = m64PolygonLength polygon := by
  unfold freeLoopLength
  rw [show periodicFreeLoop gamma = m63FlattenedPolygon polygon from funext heq]
  rw [show rampPeriod = curvePeriod from rfl]
  rw [m64FlattenedPolygon_length polygon hN, m64PolygonLength_eq_sum polygon hN]

end PoincareConjecture
