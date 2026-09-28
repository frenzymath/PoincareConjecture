import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapData




noncomputable section
set_option autoImplicit false

open Set

namespace PoincareConjecture.M64IntrinsicFiniteCornerCaps

variable {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
  {U : Set AnnulusCoordinates} (C : M64IntrinsicFiniteCornerCaps alpha beta A B U)




theorem radius_le_left_third (j : J) : C.radius j ≤ A j / 3 :=
  (C.radius_bound j).trans
    (div_le_div_of_nonneg_right (min_le_left (A j) (B j)) (by norm_num))




theorem radius_le_right_third (j : J) : C.radius j ≤ B j / 3 :=
  (C.radius_bound j).trans
    (div_le_div_of_nonneg_right (min_le_right (A j) (B j)) (by norm_num))




theorem radius_lt_left (j : J) : C.radius j < A j := by
  linarith only [C.radius_pos j, C.radius_le_left_third j]




theorem radius_lt_right (j : J) : C.radius j < B j := by
  linarith only [C.radius_pos j, C.radius_le_right_third j]




theorem first_axis_mem (j : J) (s : ℝ) (hs : s ∈ Icc 0 (C.radius j)) :
    alpha j s ∈ C.carrier j := by
  have h : alpha j s ∈ C.carrier j ∩ frontier U := by
    rw [C.frontier_contact]
    exact Or.inl ⟨s, hs, rfl⟩
  exact h.1




theorem second_axis_mem (j : J) (s : ℝ) (hs : s ∈ Icc 0 (C.radius j)) :
    beta j s ∈ C.carrier j := by
  have h : beta j s ∈ C.carrier j ∩ frontier U := by
    rw [C.frontier_contact]
    exact Or.inr ⟨s, hs, rfl⟩
  exact h.1

end PoincareConjecture.M64IntrinsicFiniteCornerCaps
