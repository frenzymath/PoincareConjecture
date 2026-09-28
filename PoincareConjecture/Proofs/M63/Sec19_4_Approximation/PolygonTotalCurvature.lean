import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.PolygonCellCurvature
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfileTurning










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem m63FlattenedPolygon_graph_cell_integral (P : M62.CircleProductData F circumference)
    (t : ℝ) {N : ℕ} (polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N)
    (hN : 0 < N) (j : Fin N) :
    let gamma := m63CanonicalRamp P (m63FlattenedPolygon polygon)
    let density := fun x => m62Curvature P.flow (fun s _ => gamma s) t x *
      curveSpeed P.flow (fun s _ => gamma s) t x
    IntervalIntegrable density volume (m63CellLeft N j)
        (m63CellLeft N j + m63CellLength N) ∧
      (∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N), density x) ≤
        Real.pi := by
  let A := (polygon.side j).speed
  let B := circumference / curvePeriod
  let density := fun x =>
    m62Curvature P.flow (fun s _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) s) t x *
      curveSpeed P.flow (fun s _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) s) t x
  let q := fun x => A * B * |deriv (m63Profile N) x| /
    (A ^ 2 * m63Profile N x ^ 2 + B ^ 2)
  have hB : 0 < B := div_pos P.circle.positive Real.two_pi_pos
  have hD (x : ℝ) : 0 < A ^ 2 * m63Profile N x ^ 2 + B ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg A) (sq_nonneg (m63Profile N x)))
      (sq_pos_of_pos hB)
  have hf : Continuous (m63Profile N) := (m63Profile_smooth N).continuous
  have hdf : Continuous (deriv (m63Profile N)) :=
    ((m63Profile_smooth N).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).continuous_deriv_one
  have hq : Continuous q := (continuous_const.mul hdf.abs).div
    ((continuous_const.mul (hf.pow 2)).add continuous_const) (fun x => (hD x).ne')
  have hab : m63CellLeft N j ≤ m63CellLeft N j + m63CellLength N :=
    le_add_of_nonneg_right (m63CellLength_pos hN).le
  have heq : EqOn density q (Ioo (m63CellLeft N j)
      (m63CellLeft N j + m63CellLength N)) := fun _ hx =>
    m63FlattenedPolygon_graph_cell_density P t polygon hN j hx
  constructor
  · apply (hq.intervalIntegrable _ _).congr_uIoo
    rw [uIoo_of_le hab]
    exact heq.symm
  · change (∫ x in m63CellLeft N j..(m63CellLeft N j + m63CellLength N), density x) ≤ _
    rw [intervalIntegral.integral_congr_Ioo_of_le hab heq]
    exact m63Profile_turning_integral_le_pi hN (polygon.side j).speed_nonnegative hB _




theorem m63FlattenedPolygon_graph_totalCurvature (P : M62.CircleProductData F circumference)
    (t : ℝ) {N : ℕ} (polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N)
    (hN : 0 < N) :
    m62TotalCurvature P.flow
      (fun x _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) x) t ≤
        (N : ℝ) * Real.pi := by
  let ell := m63CellLength N
  let density := fun x =>
    m62Curvature P.flow (fun s _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) s) t x *
      curveSpeed P.flow (fun s _ => m63CanonicalRamp P (m63FlattenedPolygon polygon) s) t x
  have hcell := m63FlattenedPolygon_graph_cell_integral P t polygon hN
  have hint (k : ℕ) (hk : k < N) :
      IntervalIntegrable density volume ((k : ℝ) * ell) (((k + 1 : ℕ) : ℝ) * ell) := by
    simpa only [m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
      (hcell ⟨k, hk⟩).1
  have hsum : (∑ j : Fin N,
      ∫ x in m63CellLeft N j..(m63CellLeft N j + ell), density x) =
        ∫ x in (0 : ℝ)..curvePeriod, density x := by
    have htel := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * ell) (n := N) (μ := volume) hint
    rw [← Fin.sum_univ_eq_sum_range] at htel
    simpa only [ell, m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Nat.cast_zero, zero_mul, m63_count_mul_cellLength hN, curvePeriod] using htel
  change (∫ x in (0 : ℝ)..curvePeriod, density x) ≤ (N : ℝ) * Real.pi
  rw [← hsum]
  calc
    _ ≤ ∑ _j : Fin N, Real.pi := Finset.sum_le_sum (fun j _ => (hcell j).2)
    _ = (N : ℝ) * Real.pi := by simp

end PoincareConjecture
