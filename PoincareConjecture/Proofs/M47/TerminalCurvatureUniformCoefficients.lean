import PoincareConjecture.Proofs.M47.CanonicalNeckCoefficientBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

open M34 PoincareConjecture.Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)



theorem terminalCurvature_exists_uniform_neck_coefficient_bound (epsilon : ℝ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ D : RoundCylinderTwoTensor,
      RoundCylinderClose epsilon 0 D → ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, z)‖ ≤ L := by
  let m := Nat.floor epsilon⁻¹
  obtain ⟨A, _, herror⟩ := capPersistence_exists_coordinate_error_jet_bound m
  obtain ⟨G, _, hGram⟩ := capNeckNormalization_exists_modelGram_center_jet_bound 0 m
  let L0 := A * Real.sqrt (epsilon ^ 2 / (1 / 2 : ℝ) ^ (2 + m)) + G
  refine ⟨max 1 L0, le_max_left _ _, ?_⟩
  intro D hD q z hz j hj a b
  have hcenter : (0, z) ∈ (chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  have hsD := (hD.1 q a b).contDiffAt
    (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  have hsG : ContDiffAt ℝ ∞ (fun y => roundCylinderGram 0 (chartAt E₂ q) y a b) (0, z) :=
    (capPersistence_modelGram_contDiff 0 q a b).contDiffAt
  have h := herror epsilon D hD le_rfl q z hz j hj a b
  rw [sphere_chart_center_zero, fun_iteratedFDeriv_sub_apply
    (hsD.of_le (by exact_mod_cast le_top)) (hsG.of_le (by exact_mod_cast le_top))] at h
  exact ((norm_le_norm_sub_add _ _).trans (add_le_add h (hGram q z j hj a b))).trans
    (le_max_right _ _)

end PoincareConjecture.M47
