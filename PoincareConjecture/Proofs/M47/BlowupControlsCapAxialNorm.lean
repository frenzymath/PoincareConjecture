import PoincareConjecture.Proofs.M47.CanonicalNeckAxialNorm
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelNative

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem cap_native_axial_weight_norm_le
    {lambda u : ℝ} (hlambda : 0 ≤ lambda) (hu : u < 1)
    (beta : ℝ) (q : UnitTwoSphere) (z : ℝ) {r : ℕ}
    (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt E2 q) (chartAt E2 q q, z)
        (fun a => beta * (∏ i, neckAxialWeight lambda (a i)) * T a) ≤
      beta ^ 2 * (max 1 lambda) ^ (2 * r) *
        roundCylinderTensorNormSquared u (chartAt E2 q) (chartAt E2 q q, z) T := by
  have hweight (i : Fin 3) : 0 ≤ neckAxialWeight lambda i ∧
      neckAxialWeight lambda i ≤ max 1 lambda := by
    unfold neckAxialWeight
    split_ifs
    · exact ⟨hlambda, le_max_right _ _⟩
    · exact ⟨zero_le_one, le_max_left _ _⟩
  simp only [M35.roundCylinderTensorNormSquared_center hu, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hprod0 : 0 ≤ ∏ i, neckAxialWeight lambda (a i) :=
    Finset.prod_nonneg fun i _ => (hweight (a i)).1
  have hprod : (∏ i, neckAxialWeight lambda (a i)) ≤ (max 1 lambda) ^ r := by
    calc
      _ ≤ ∏ _i : Fin r, max 1 lambda :=
        Finset.prod_le_prod (fun i _ => (hweight (a i)).1) (fun i _ => (hweight (a i)).2)
      _ = _ := by simp
  have hmax0 : 0 ≤ max 1 lambda := zero_le_one.trans (le_max_left _ _)
  have hsquare := (sq_le_sq₀ hprod0 (pow_nonneg hmax0 r)).mpr hprod
  have hsquare' : (∏ i, neckAxialWeight lambda (a i)) ^ 2 ≤ (max 1 lambda) ^ (2 * r) := by
    simpa only [← pow_mul, Nat.mul_comm] using hsquare
  have hweights0 : 0 ≤ ∏ i : Fin r,
      (![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i) : ℝ) :=
    Finset.prod_nonneg fun i _ => (M35.roundCylinderInverseWeight_pos hu (a i)).le
  have h := mul_le_mul_of_nonneg_left hsquare'
    (mul_nonneg (mul_nonneg hweights0 (sq_nonneg beta)) (sq_nonneg (T a)))
  nlinarith only [h]

theorem cap_native_sphere_error_norm_sq (q : UnitTwoSphere) (z d : ℝ) :
    roundCylinderTensorNormSquared 0 (chartAt E2 q) (chartAt E2 q q, z)
      (fun a : Fin 2 → Fin 3 => d *
        (roundCylinderGram 0 (chartAt E2 q) (chartAt E2 q q, z) (a 0) (a 1) -
          neckAxialConstantArray 1 a)) = 2 * d ^ 2 := by
  rw [M35.roundCylinderTensorNormSquared_center zero_lt_one]
  let f : (Fin 2 → Fin 3) → ℝ := fun a =>
    (∏ i, ![(2 * (1 - (0 : ℝ)))⁻¹, (2 * (1 - (0 : ℝ)))⁻¹, 1] (a i)) *
      (d * (roundCylinderGram 0 (chartAt E2 q) (chartAt E2 q q, z) (a 0) (a 1) -
        neckAxialConstantArray 1 a)) ^ 2
  change (∑ a : Fin 2 → Fin 3, f a) = _
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp f, Fintype.sum_prod_type]
  simp only [f, M35.roundCylinderGram_center, neckAxialConstantArray]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, Matrix.diagonal,
    Fin.forall_fin_two, h02, h12, h21]
  ring

end PoincareConjecture.M47
