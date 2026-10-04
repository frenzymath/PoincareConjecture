import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Finite.CornerCapData

/-! Parameter bounds and actual axis membership for retained finite caps.
Source: MT Claim 19.40; normal-collision-transversality derivation, Sections 4-5. -/

noncomputable section
set_option autoImplicit false

open Set

namespace PoincareMT.M64IntrinsicFiniteCornerCaps

variable {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
  {U : Set AnnulusCoordinates} (C : M64IntrinsicFiniteCornerCaps alpha beta A B U)

/-- The retained radius is at most a third of the first original axis length. Source: MT
Claim 19.40; normal-collision-transversality, Section 4. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 4. -/
theorem radius_le_left_third (j : J) : C.radius j ≤ A j / 3 :=
  (C.radius_bound j).trans
    (div_le_div_of_nonneg_right (min_le_left (A j) (B j)) (by norm_num))

/-- The retained radius is at most a third of the second original axis length. Source: MT
Claim 19.40; normal-collision-transversality, Section 4. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 4. -/
theorem radius_le_right_third (j : J) : C.radius j ≤ B j / 3 :=
  (C.radius_bound j).trans
    (div_le_div_of_nonneg_right (min_le_right (A j) (B j)) (by norm_num))

/-- A positive cap radius is strictly smaller than the first original axis length. Source:
MT Claim 19.40; normal-collision-transversality, Section 4. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 4. -/
theorem radius_lt_left (j : J) : C.radius j < A j := by
  linarith only [C.radius_pos j, C.radius_le_left_third j]

/-- A positive cap radius is strictly smaller than the second original axis length. Source:
MT Claim 19.40; normal-collision-transversality, Section 4. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 4. -/
theorem radius_lt_right (j : J) : C.radius j < B j := by
  linarith only [C.radius_pos j, C.radius_le_right_third j]

/-- The complete retained first-axis segment belongs to its actual occupied cap union.
Source: MT Claim 19.40; normal-collision-transversality derivation, Section 4. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 4. -/
theorem first_axis_mem (j : J) (s : ℝ) (hs : s ∈ Icc 0 (C.radius j)) :
    alpha j s ∈ C.carrier j := by
  have h : alpha j s ∈ C.carrier j ∩ frontier U := by
    rw [C.frontier_contact]
    exact Or.inl ⟨s, hs, rfl⟩
  exact h.1

/-- The complete retained second-axis segment belongs to its actual occupied cap union.
Source: MT Claim 19.40; normal-collision-transversality derivation, Section 4. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 4. -/
theorem second_axis_mem (j : J) (s : ℝ) (hs : s ∈ Icc 0 (C.radius j)) :
    beta j s ∈ C.carrier j := by
  have h : beta j s ∈ C.carrier j ∩ frontier U := by
    rw [C.frontier_contact]
    exact Or.inr ⟨s, hs, rfl⟩
  exact h.1

end PoincareMT.M64IntrinsicFiniteCornerCaps
