import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoTargetPlacement
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedParameterLift

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "W" => ((Fin 2 ⊕ Fin 1) → ℝ)
local notation "V" => (Fin 3 → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 2 ↪ Fin 2 ⊕ Fin 1)

private def coverLinear : W ≃ₗ[ℝ] V where
  toFun x := ![x (Sum.inl 0), x (Sum.inl 1), x (Sum.inr 0)]
  invFun y := Sum.elim (fun i => y (Fin.castAdd 1 i)) (fun _ => y 2)
  left_inv x := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  right_inv y := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' r x := by funext i; fin_cases i <;> rfl

noncomputable def coverCoordinates : W ≃ᴬ[ℝ] V :=
  coverLinear.toContinuousLinearEquiv.toContinuousAffineEquiv

theorem coverCoordinates_apply (x : W) :
    coverCoordinates x = ![x (Sum.inl 0), x (Sum.inl 1), x (Sum.inr 0)] := rfl

theorem coverCoordinates_norm (x : W) : ‖coverCoordinates x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm x (Sum.inl 0)
    · exact norm_le_pi_norm x (Sum.inl 1)
    · exact norm_le_pi_norm x (Sum.inr 0)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (coverCoordinates x))).mpr
    intro i
    rcases i with i | i
    · fin_cases i
      · exact norm_le_pi_norm (coverCoordinates x) 0
      · exact norm_le_pi_norm (coverCoordinates x) 1
    · fin_cases i
      exact norm_le_pi_norm (coverCoordinates x) 2

theorem coverCoordinates_mem_cylinder (x : W) :
    x ∈ coordinateCylinder J ↔
      coverCoordinates x ∈ coordinateCylinder ({0, 1} : Finset (Fin 3)) := by
  constructor
  · intro hx i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hx (Sum.inl 0) (Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact hx (Sum.inl 1) (Finset.mem_map.mpr ⟨1, Finset.mem_univ _, rfl⟩)
  · intro hx i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    fin_cases j
    · exact hx 0 (by simp)
    · exact hx 1 (by simp)

theorem coverCoordinates_closedBall (r : ℝ) :
    coverCoordinates '' closedBall (0 : W) r = closedBall (0 : V) r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_closedBall_zero_iff, coverCoordinates_norm] using hx
  · intro hy
    refine ⟨coverCoordinates.symm y, ?_, coverCoordinates.apply_symm_apply y⟩
    have hn := coverCoordinates_norm (coverCoordinates.symm y)
    rw [coverCoordinates.apply_symm_apply] at hn
    exact mem_closedBall_zero_iff.mpr (hn.symm ▸ mem_closedBall_zero_iff.mp hy)

end PoincareConjecture.M76.HamiltonIndexTwoStandard
