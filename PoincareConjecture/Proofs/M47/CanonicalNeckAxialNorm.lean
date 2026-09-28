import PoincareConjecture.Proofs.M47.CanonicalNeckAxialJets
import PoincareConjecture.Proofs.M47.CanonicalNeckStrictMargin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem roundCylinderTensorNormSquared_neckAxialWeight_le
    {lambda u : ℝ} (hlambda : lambda ∈ Icc (0 : ℝ) 1) (hu : u ≤ 0)
    (q : UnitTwoSphere) (z : ℝ) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, z)
        (fun a => (∏ i, neckAxialWeight lambda (a i)) * T a) ≤
      roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, z) T := by
  have hweight (i : Fin 3) : 0 ≤ neckAxialWeight lambda i ∧ neckAxialWeight lambda i ≤ 1 := by
    unfold neckAxialWeight
    split_ifs
    · exact hlambda
    · exact ⟨zero_le_one, le_rfl⟩
  have hgram (i : Fin 3) : 0 ≤ (![ (2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] i : ℝ) := by
    fin_cases i
    · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (by linarith))
    · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (by linarith))
    · exact zero_le_one
  unfold roundCylinderTensorNormSquared
  simp only [roundCylinderGram_chart_center_inv (hu.trans_lt zero_lt_one).ne,
    diagonal_tensor_contraction]
  apply Finset.sum_le_sum
  intro a _
  have hprod0 : 0 ≤ ∏ i, neckAxialWeight lambda (a i) :=
    Finset.prod_nonneg fun i _ => (hweight (a i)).1
  have hprod1 : (∏ i, neckAxialWeight lambda (a i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hweight (a i)).1) (fun i _ => (hweight (a i)).2)
  have hsq : (∏ i, neckAxialWeight lambda (a i)) ^ 2 ≤ 1 := by nlinarith
  apply mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => hgram (a i))
  simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (T a))

theorem roundCylinderTensorNormSquared_neckAxialConstantArray
    {u : ℝ} (hu : u ≠ 1) (q : UnitTwoSphere) (z v : ℝ) (r : ℕ) :
    roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, z)
      (neckAxialConstantArray v (r := r)) = v ^ 2 := by
  classical
  unfold roundCylinderTensorNormSquared
  simp only [roundCylinderGram_chart_center_inv hu, diagonal_tensor_contraction]
  rw [Finset.sum_eq_single (fun _ : Fin r => (2 : Fin 3))]
  · simp [neckAxialConstantArray]
  · intro a _ hne
    have hnot : ¬ ∀ i, a i = 2 := fun h => hne (funext h)
    simp [neckAxialConstantArray, hnot]
  · simp

end PoincareConjecture.Proofs.M47
