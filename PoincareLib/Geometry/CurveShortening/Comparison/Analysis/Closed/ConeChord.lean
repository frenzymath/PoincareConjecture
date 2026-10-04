import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.Compact.StrictChord
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Strict chord bounds in a closed cone containing no line

Compactness of the unit-ball section gives a uniform strict bound, and
positive dilation transfers it to every radius. This is the corner estimate
in the minimal-contact-regularity derivation for MT Claim 19.40.
-/

set_option autoImplicit false

open Set Metric

/-- A closed salient cone in a proper real inner-product space has a uniform chord bound
strictly below the diameter of the containing ball. Here salient means that the cone
contains no nonzero opposite pair. Source: MT Claim 19.40, pp. 470-471;
derivations/2026-09-27-minimal-contact-regularity.md, Sections 2-3. -/
theorem m64ClosedCone_exists_scaled_strict_chord_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (C : ConvexCone ℝ E) (hC : IsClosed (C : Set E)) (hzero : (0 : E) ∈ C)
    (hsalient : C.Salient) :
    ∃ d : ℝ, 0 ≤ d ∧ d < 2 ∧
      ∀ r : ℝ, 0 < r → ∀ v ∈ C, ∀ w ∈ C,
        ‖v‖ ≤ r → ‖w‖ ≤ r → ‖w - v‖ ≤ r * d := by
  let S : Set E := (C : Set E) ∩ closedBall 0 1
  have hS : IsCompact S := (isCompact_closedBall (0 : E) 1).inter_left hC
  have hne : S.Nonempty := ⟨0, hzero, by simp⟩
  have hnorm (v : E) (hv : v ∈ S) : ‖v‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using hv.2
  obtain ⟨d, hd, hd2, hbound⟩ := m64Compact_exists_uniform_strict_chord_bound
    hS hS hne hne hnorm hnorm (by
      intro v hv w hw hvunit _ heq
      apply hsalient v hv.1 (by intro h; simp only [h, norm_zero] at hvunit; norm_num at hvunit)
      exact heq ▸ hw.1)
  refine ⟨d, hd, hd2, ?_⟩
  intro r hr v hv w hw hvr hwr
  have hscaled (z : E) (hz : z ∈ C) (hzr : ‖z‖ ≤ r) : r⁻¹ • z ∈ S := by
    refine ⟨C.smul_mem (inv_pos.mpr hr) hz, ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hzr)
  have hh := mul_le_mul_of_nonneg_left
    (hbound _ (hscaled v hv hvr) _ (hscaled w hw hwr)) hr.le
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
    ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hh
  exact hh

/-- If the opposite of a vector in the unit ball is outside a closed cone, the cone's unit
section has a uniform strict chord bound to that vector. Positive dilation gives the
estimate at every positive radius. Source: MT Claim 19.40, pp. 470-471;
derivations/2026-09-27-minimal-contact-regularity.md, Sections 2-3. -/
theorem m64ClosedCone_exists_scaled_chord_bound_to_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (C : ConvexCone ℝ E) (hC : IsClosed (C : Set E)) (hzero : (0 : E) ∈ C)
    {w : E} (hw : ‖w‖ ≤ 1) (hopp : -w ∉ C) :
    ∃ d : ℝ, 0 ≤ d ∧ d < 2 ∧
      ∀ r : ℝ, 0 < r → ∀ v ∈ C, ‖v‖ ≤ r → ‖r • w - v‖ ≤ r * d := by
  let S : Set E := (C : Set E) ∩ closedBall 0 1
  have hS : IsCompact S := (isCompact_closedBall (0 : E) 1).inter_left hC
  obtain ⟨d, hd, hd2, hbound⟩ := m64Compact_exists_uniform_strict_chord_bound
    hS (isCompact_singleton (x := w)) ⟨0, hzero, by simp⟩ (singleton_nonempty w)
    (fun v hv => by simpa only [mem_closedBall, dist_zero_right] using hv.2)
    (fun z hz => by simpa only [mem_singleton_iff.mp hz] using hw) (by
      intro v hv z hz _ _ heq
      have hvw : v = -w := by
        rw [mem_singleton_iff.mp hz] at heq
        simpa using congrArg Neg.neg heq.symm
      exact hopp (hvw ▸ hv.1))
  refine ⟨d, hd, hd2, ?_⟩
  intro r hr v hv hvr
  have hscaled : r⁻¹ • v ∈ S := by
    refine ⟨C.smul_mem (inv_pos.mpr hr) hv, ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hvr)
  have hh := mul_le_mul_of_nonneg_left (hbound _ hscaled w (mem_singleton w)) hr.le
  have heq : r • (w - r⁻¹ • v) = r • w - v := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  calc
    ‖r • w - v‖ = r * ‖w - r⁻¹ • v‖ := by
      rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    _ ≤ r * d := hh
