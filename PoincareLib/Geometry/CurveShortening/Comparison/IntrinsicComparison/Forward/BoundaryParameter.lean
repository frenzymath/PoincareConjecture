import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Boundary.Parameters

/-! A forward circle parameter for a distinct return endpoint.
Source: MT Lemma 19.46, pp. 474-478; central-regional-descent derivation,
Section 7. The actual curve keeps its original initial normal orientation. -/

noncomputable section
set_option autoImplicit false

open Set

namespace PoincareMT

/-- A distinct inner-circle endpoint has an actual parameter strictly after a given label in
the standard period and less than one period away. Source: MT Lemma 19.46;
central-regional-descent derivation, Section 7. Source/construction:
proof-work/tasks/M64/derivations/2026-09-27-central-regional-descent.md, Section 7. -/
theorem m64Intrinsic_exists_forward_boundary_parameter
    {a : ℝ} (ha : a ∈ Ico (0 : ℝ) rampPeriod) {x : AnnulusCoordinates}
    (hx : ‖x‖ = 1) (hne : x ≠ intrinsicAnnulusBoundary 1 a) :
    ∃ b : ℝ, a < b ∧ b - a < rampPeriod ∧ x = intrinsicAnnulusBoundary 1 b := by
  obtain ⟨b, hb, hpoint⟩ := m64Intrinsic_exists_boundary_parameter hx
  have hba : b ≠ a := fun heq => hne (heq ▸ hpoint)
  by_cases hab : a < b
  · exact ⟨b, hab, by linarith only [ha.1, hb.2], hpoint⟩
  · have hblt : b < a := lt_of_le_of_ne (le_of_not_gt hab) hba
    refine ⟨b + rampPeriod, by linarith only [hb.1, ha.2],
      by linarith only [hblt], ?_⟩
    simpa only [m64Intrinsic_boundary_periodic 1 b] using hpoint

end PoincareMT
