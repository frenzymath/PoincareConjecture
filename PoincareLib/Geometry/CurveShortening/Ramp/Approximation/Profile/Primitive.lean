import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Profile.Base
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Circle.Homeomorph
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The flattening primitive and its circle homeomorphism

Morgan--Tian, pp. 451-452: the integral of the normalized flat profile is
smooth and strictly increasing, commutes with the angular period, and
induces the actual homeomorphism used to smooth the polygon.
-/

set_option autoImplicit false

open scoped ContDiff intervalIntegral

namespace PoincareMT

/-- The flattening primitive has the prescribed derivative; Morgan--Tian, p. 451. -/
theorem m63Flattening_hasDerivAt (N : ℕ) (x : ℝ) :
    HasDerivAt (m63Flattening N) (m63Profile N x) x := by
  have hc := (m63Profile_smooth N).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Smoothness of the flattening primitive; Morgan--Tian, p. 452. -/
theorem m63Flattening_smooth (N : ℕ) : ContDiff ℝ ∞ (m63Flattening N) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (m63Flattening_hasDerivAt N x).differentiableAt, ?_⟩
  have hderiv : deriv (m63Flattening N) = m63Profile N :=
    funext fun x => (m63Flattening_hasDerivAt N x).deriv
  rw [hderiv]
  exact m63Profile_smooth N

/-- The primitive starts at zero; Morgan--Tian, p. 451. -/
theorem m63Flattening_zero (N : ℕ) : m63Flattening N 0 = 0 := by
  simp only [m63Flattening, intervalIntegral.integral_same]

/-- Positivity away from the integer vertices; Morgan--Tian, p. 451,
properties (2)-(3). -/
theorem m63Profile_pos_of_not_vertex {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∉ Set.range (fun j : ℤ => (j : ℝ) * m63CellLength N)) :
    0 < m63Profile N x := by
  have harg : 0 < 1 - Real.cos ((N : ℝ) * x) := by
    apply sub_pos.mpr
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro h
    obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).mp h
    apply hx
    refine ⟨j, ?_⟩
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hN.ne' : (N : ℝ) ≠ 0)
    rw [mul_left_comm, m63_count_mul_cellLength hN]
    exact hj
  exact div_pos (mul_pos (m63CellLength_pos hN) (expNegInvGlue.pos_of_pos harg))
    (m63ProfileBase_integral_pos hN)

/-- Flat vertices do not prevent strict increase of the primitive;
Morgan--Tian, p. 452. -/
theorem m63Flattening_strictMono {N : ℕ} (hN : 0 < N) :
    StrictMono (m63Flattening N) := by
  intro x y hxy
  have hc := (m63Profile_smooth N).continuous
  have hdense := (Set.countable_range (fun j : ℤ => (j : ℝ) * m63CellLength N)).dense_compl ℝ
  obtain ⟨z, hz, hxz, hzy⟩ := hdense.exists_between hxy
  have hpos : 0 < ∫ s in x..y, m63Profile N s := by
    apply intervalIntegral.integral_pos hxy hc.continuousOn
      (fun s _ => m63Profile_nonneg hN s)
    exact ⟨z, ⟨hxz.le, hzy.le⟩, m63Profile_pos_of_not_vertex hN hz⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x y)
  change (∫ s in (0 : ℝ)..x, m63Profile N s) < ∫ s in (0 : ℝ)..y, m63Profile N s
  linarith

/-- Shifting by one cell shifts the primitive by one cell;
Morgan--Tian, pp. 451-452, normalization property (4). -/
theorem m63Flattening_cell_shift {N : ℕ} (hN : 0 < N) (x : ℝ) :
    m63Flattening N (x + m63CellLength N) = m63Flattening N x + m63CellLength N := by
  unfold m63Flattening
  rw [(m63Profile_periodic hN).intervalIntegral_add_eq_add 0 x
    (fun s t => (m63Profile_smooth N).continuous.intervalIntegrable s t)]
  rw [zero_add, m63Profile_cell_integral hN]

/-- Shifting by the full angular period shifts the primitive by that period;
Morgan--Tian, pp. 451-452. -/
theorem m63Flattening_period_shift {N : ℕ} (hN : 0 < N) (x : ℝ) :
    m63Flattening N (x + curvePeriod) = m63Flattening N x + curvePeriod := by
  have hiter (k : ℕ) : m63Flattening N (x + (k : ℝ) * m63CellLength N) =
      m63Flattening N x + (k : ℝ) * m63CellLength N := by
    induction k with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, m63Flattening_cell_shift hN, ih]
      ring
  simpa only [m63_count_mul_cellLength hN, curvePeriod] using hiter N

/-- The actual circle homeomorphism induced by the flattening primitive;
Morgan--Tian, p. 452. -/
theorem m63Flattening_circle_homeomorph {N : ℕ} (hN : 0 < N) :
    ∃ e : AddCircle curvePeriod ≃ₜ AddCircle curvePeriod,
      ∀ x : ℝ, e (x : AddCircle curvePeriod) = (m63Flattening N x : AddCircle curvePeriod) := by
  exact AddCircle.exists_homeomorph_of_strictMono Real.two_pi_pos
    (m63Flattening_smooth N).continuous (m63Flattening_strictMono hN)
    (m63Flattening_period_shift hN)

end PoincareMT
