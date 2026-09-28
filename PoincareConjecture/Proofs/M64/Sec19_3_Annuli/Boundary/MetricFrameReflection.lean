import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.MetricRowFrame










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Complex
open scoped ContDiff

namespace PoincareConjecture.M64

open M65Branch

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)





def metricBoundaryReflection (j : Fin n) : (Fin n → ℂ) ≃ₗᵢ[ℝ] (Fin n → ℂ) := by
  let e (k : Fin n) : ℂ ≃ₗᵢ[ℝ] ℂ :=
    if k = j then conjLIE else conjLIE.trans (LinearIsometryEquiv.neg ℝ)
  exact {
    toLinearEquiv := LinearEquiv.piCongrRight fun k => (e k).toLinearEquiv
    norm_map' := fun v => by
      simp only [Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map] }





theorem metricBoundaryReflection_apply (j : Fin n) (v : Fin n → ℂ) (k : Fin n) :
    metricBoundaryReflection j v k = if k = j then star (v k) else -star (v k) := by
  simp only [metricBoundaryReflection, LinearIsometryEquiv.coe_mk,
    LinearEquiv.piCongrRight_apply]
  split_ifs <;> rfl





theorem metricBoundaryReflection_smul (j : Fin n) (c : ℂ) (v : Fin n → ℂ) :
    metricBoundaryReflection j (c • v) = star c • metricBoundaryReflection j v := by
  ext k
  simp only [metricBoundaryReflection_apply, Pi.smul_apply, smul_eq_mul, star_mul]
  split_ifs <;> ring





theorem metricBoundaryReflection_involutive (j : Fin n) :
    Function.Involutive (metricBoundaryReflection j) := by
  intro v
  ext k
  simp only [metricBoundaryReflection_apply]
  split_ifs <;> simp





theorem metricRowFrame_boundary_columns
    (G : E →L[ℝ] E →L[ℝ] ℝ) (V X Y : E) (j : Fin n) (hV : V j ≠ 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < G W W) (hX : ∃ a : ℝ, X = a • V)
    (hdiag : G X X = G Y Y) (hmixed : G X Y = 0) :
    metricRowFrame G V j Y j = 0 ∧ ∀ k, k ≠ j → metricRowFrame G V j X k = 0 := by
  obtain ⟨a, rfl⟩ := hX
  constructor
  · rw [metricRowFrame_apply, if_pos rfl]
    by_cases ha : a = 0
    · have hYY : G Y Y = 0 := by
        simpa only [ha, zero_smul, map_zero, zero_apply] using hdiag.symm
      have hY : Y = 0 := by
        by_contra hn
        exact (hpos Y hn).ne' hYY
      rw [hY, map_zero]
    · have hh : a * G V Y = 0 := by
        simpa only [map_smul, smul_apply, smul_eq_mul] using hmixed
      exact (mul_eq_zero.mp hh).resolve_left ha
  · intro k hk
    rw [metricRowFrame_apply, if_neg hk]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring





theorem metricBoundaryReflection_of_rows (j : Fin n) (X Y : E)
    (hY : Y j = 0) (hX : ∀ k, k ≠ j → X k = 0) :
    metricBoundaryReflection j (coordinateComplexification X - I • coordinateComplexification Y) =
      coordinateComplexification X - I • coordinateComplexification Y := by
  ext k
  rw [metricBoundaryReflection_apply]
  change (if k = j then star ((X k : ℂ) - I * (Y k : ℂ)) else
    -star ((X k : ℂ) - I * (Y k : ℂ))) = (X k : ℂ) - I * (Y k : ℂ)
  by_cases hk : k = j
  · subst k
    simp [hY]
  · simp [hk, hX k hk]





theorem metricRowFrame_boundary_reflection
    (G : E →L[ℝ] E →L[ℝ] ℝ) (V X Y : E) (j : Fin n) (hV : V j ≠ 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < G W W) (hX : ∃ a : ℝ, X = a • V)
    (hdiag : G X X = G Y Y) (hmixed : G X Y = 0) :
    metricBoundaryReflection j (complexifyOperator (metricRowFrame G V j)
      (coordinateComplexification X - I • coordinateComplexification Y)) =
      complexifyOperator (metricRowFrame G V j)
        (coordinateComplexification X - I • coordinateComplexification Y) := by
  obtain ⟨hY, hX⟩ := metricRowFrame_boundary_columns G V X Y j hV hpos hX hdiag hmixed
  simpa only [map_sub, map_smul, complexifyOperator_real] using
    metricBoundaryReflection_of_rows j (metricRowFrame G V j X) (metricRowFrame G V j Y) hY hX

end PoincareConjecture.M64
