import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Jets.CylinderJetNorm

/-!
# Exact inverse-Gram bounds across the longer cylinder time window

At nonpositive times the literal model's inverse angular weights decrease.
The two retained comparison times zero and minus one half therefore control
every covariant slot over the longer window, with the explicit factor `2^r`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35

/-- Earlier literal-cylinder time decreases the intrinsic norm of any
fixed covariant tensor, because each inverse-Gram slot weight decreases. -/
theorem roundCylinderTensorNormSquared_mono_time {u v : ℝ}
    (huv : u ≤ v) (hv : v < 1) (q : UnitTwoSphere) (s : ℝ)
    {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T ≤
      roundCylinderTensorNormSquared v (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T := by
  have hu : u < 1 := huv.trans_lt hv
  have hw (a : Fin 3) :
      ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] a ≤
        ![(2 * (1 - v))⁻¹, (2 * (1 - v))⁻¹, 1] a := by
    have h := inv_anti₀ (show 0 < 2 * (1 - v) by linarith)
      (show 2 * (1 - v) ≤ 2 * (1 - u) by linarith)
    fin_cases a
    · simpa using h
    · simpa using h
    · exact le_rfl
  rw [roundCylinderTensorNormSquared_center hu, roundCylinderTensorNormSquared_center hv]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg (T a))
  exact Finset.prod_le_prod (fun i _ => (roundCylinderInverseWeight_pos hu (a i)).le)
    (fun i _ => hw (a i))

/-- Comparing the two retained times costs at most a factor two in each
covariant slot, including all derivative slots. -/
theorem roundCylinderTensorNormSquared_zero_le_half (q : UnitTwoSphere) (s : ℝ)
    {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T ≤
      2 ^ r * roundCylinderTensorNormSquared (-1 / 2)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T := by
  have hw (a : Fin 3) :
      ![(2 * (1 - (0 : ℝ)))⁻¹, (2 * (1 - (0 : ℝ)))⁻¹, 1] a ≤
        2 * ![(2 * (1 - (-1 / 2 : ℝ)))⁻¹, (2 * (1 - (-1 / 2 : ℝ)))⁻¹, 1] a := by
    fin_cases a <;> norm_num
  rw [roundCylinderTensorNormSquared_center zero_lt_one,
    roundCylinderTensorNormSquared_center (by norm_num : (-1 / 2 : ℝ) < 1),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset (Fin r)))
    (fun i _ => (roundCylinderInverseWeight_pos zero_lt_one (a i)).le)
    (fun i _ => hw (a i))
  have hprod' : (∏ i : Fin r, ![(2 * (1 - (0 : ℝ)))⁻¹,
      (2 * (1 - (0 : ℝ)))⁻¹, 1] (a i)) ≤
      2 ^ r * ∏ i : Fin r, ![(2 * (1 - (-1 / 2 : ℝ)))⁻¹,
        (2 * (1 - (-1 / 2 : ℝ)))⁻¹, 1] (a i) := by
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hprod
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprod' (sq_nonneg (T a))

/-- The actual squared tensor norm obeys the elementary two-term
estimate, retaining its positive weights in every covariant slot. -/
theorem roundCylinderTensorNormSquared_linear_le {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s A B : ℝ) {r : ℕ} (T S : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (fun a => A * T a + B * S a) ≤
      2 * A ^ 2 * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T +
      2 * B ^ 2 * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) S := by
  simp only [roundCylinderTensorNormSquared_center hu, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i) :=
    Finset.prod_nonneg (fun i _ => (roundCylinderInverseWeight_pos hu (a i)).le)
  have hsquare : (A * T a + B * S a) ^ 2 ≤
      2 * A ^ 2 * T a ^ 2 + 2 * B ^ 2 * S a ^ 2 := by
    nlinarith only [sq_nonneg (A * T a - B * S a)]
  convert mul_le_mul_of_nonneg_left hsquare hw using 1
  ring

end PoincareMT.M35
