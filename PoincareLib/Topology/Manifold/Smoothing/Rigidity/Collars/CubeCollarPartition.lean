import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Collars.HamiltonUnitCubePLCollar

/-!
# Complete source pieces for cube collar attachment

The closed inner cube and whole outer shell cover the original cube
with exactly their full common sphere. See rigidity047, section3.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "B" => closedBall (0 : V3) 1
local notation "B0" => closedBall (0 : V3) (7 / 8)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

/-- The two complete closed cube pieces have exactly their full
inner sphere as overlap, and contain the whole outer sphere in the
shell. See rigidity047, section3. -/
theorem cube_collar_partition : B0 ∪ T = B ∧ B0 ∩ T = Q0 ∧ Q ⊆ T := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    change (x ∈ B0 ∨ (7 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 1)) ↔ x ∈ B
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff]
    constructor
    · rintro (hx | hx)
      · linarith
      · exact hx.2
    · intro hx
      by_cases hxr : ‖x‖ ≤ 7 / 8
      · exact Or.inl hxr
      · exact Or.inr ⟨(not_le.mp hxr).le, hx⟩
  · ext x
    change (x ∈ B0 ∧ (7 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 1)) ↔ x ∈ Q0
    rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    constructor
    · exact fun hx => le_antisymm hx.1 hx.2.1
    · intro hx
      rw [hx]
      norm_num
  · intro x hx
    change 7 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 1
    rw [mem_sphere_zero_iff_norm.mp hx]
    norm_num

end PoincareMT.M76
