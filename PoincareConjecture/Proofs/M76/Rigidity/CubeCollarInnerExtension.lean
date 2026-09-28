import PoincareConjecture.Proofs.M76.Rigidity.CubeCollarInnerBoundary
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ScaledCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "B" => closedBall (0 : V3) 1
local notation "B0" => closedBall (0 : V3) (7 / 8)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "J" => Icc (0 : ℝ) (1 / 8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

theorem exists_finitePL_cube_collar_inner_extension
    (h : (Q ×ˢ J : Set (V3 × ℝ)) ≃ₜ T) (hh : h.IsFinitePL)
    (hnorm : ∀ z : (Q ×ˢ J : Set (V3 × ℝ)),
      ‖(h z : V3)‖ = 1 - (z : V3 × ℝ).2) :
    ∃ (b : Q ≃ₜ Q0) (A : B0 ≃ₜ B), b.IsFinitePL ∧ A.IsFinitePL ∧
      (∀ z : Q, (b z : V3) =
        (h ⟨((z : V3), 1 / 8), ⟨z.property, by norm_num⟩⟩ : V3)) ∧
      (∀ z : Q, (A ⟨b z, sphere_subset_closedBall (b z).property⟩ : V3) = z) ∧
      ∀ x : B0, (A x : V3) ∈ Q ↔ (x : V3) ∈ Q0 := by
  obtain ⟨b, hb, hbval⟩ := exists_finitePL_cube_collar_inner_boundary h hh hnorm
  have hB0 : IsFinitePLBallPair V3 B0 Q0 :=
    isFinitePLBallPair_coordinate_cube (by norm_num : (0 : ℝ) < 7 / 8)
  have hB : IsFinitePLBallPair V3 B Q := isFinitePLBallPair_unit_cube
  obtain ⟨A, hA, hAb, hAmem⟩ := hB0.exists_extension hB b.symm hb.symm
  refine ⟨b, A, hb, hA, hbval, ?_, fun x => (hAmem x).symm⟩
  intro z
  have hv := congrArg Subtype.val (hAb (b z))
  simpa only [b.symm_apply_apply] using hv

end PoincareConjecture.M76
