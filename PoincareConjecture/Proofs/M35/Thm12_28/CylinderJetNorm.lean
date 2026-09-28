import PoincareConjecture.Proofs.M35.Thm12_28.CylinderGeometry










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35



theorem roundCylinderTensorNormSquared_center {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T =
      ∑ a : Fin r → Fin 3,
        (∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i)) * (T a) ^ 2 := by
  classical
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_inv_center hu]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
    ring
  · intro b _ hba
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (Ne.symm hba)
    have hz : (∏ j : Fin r,
        Matrix.diagonal ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a j) (b j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Matrix.diagonal_apply_ne _ hi
    rw [hz]
    simp
  · simp



theorem roundCylinderInverseWeight_pos {u : ℝ} (hu : u < 1) (a : Fin 3) :
    0 < ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] a := by
  fin_cases a <;> norm_num <;> linarith



theorem roundCylinderTensorNormSquared_nonneg {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T := by
  rw [roundCylinderTensorNormSquared_center hu]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg
    (Finset.prod_nonneg (fun i _ => (roundCylinderInverseWeight_pos hu (a i)).le))
    (sq_nonneg _))



theorem roundCylinder_component_sq_le {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T : (Fin r → Fin 3) → ℝ)
    (a : Fin r → Fin 3) :
    (∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i)) * (T a) ^ 2 ≤
      roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T := by
  rw [roundCylinderTensorNormSquared_center hu]
  exact Finset.single_le_sum (fun b _ => mul_nonneg
    (Finset.prod_nonneg (fun i _ => (roundCylinderInverseWeight_pos hu (b i)).le))
    (sq_nonneg _)) (Finset.mem_univ a)



theorem roundCylinder_derivative_norm_le_jet {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) {k order : ℕ}
    (hk : k ≤ order) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
    let p : RoundCylinderCoordinates := (c z.1, z.2)
    roundCylinderTensorNormSquared u c p (roundCylinderIteratedDerivative u c B k p) ≤
      roundCylinderJetErrorSquared u B order z := by
  dsimp only [roundCylinderJetErrorSquared]
  refine Finset.single_le_sum (f := fun j =>
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        B j (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2))) ?_ ?_
  · intro j _
    exact roundCylinderTensorNormSquared_nonneg hu z.1 z.2 _
  · exact Finset.mem_range.mpr (by omega)

end PoincareConjecture.M35

namespace PoincareConjecture.RoundCylinderClose



theorem component_sq_lt {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (hu : u < 1)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊) (a : Fin (2 + k) → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
    let p : RoundCylinderCoordinates := (c z.1, z.2)
    (∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i)) *
      (roundCylinderIteratedDerivative u c B k p a) ^ 2 < epsilon ^ 2 := by
  obtain ⟨bound, hbound, hjet⟩ := h.2
  exact (M35.roundCylinder_component_sq_le hu z.1 z.2 _ a).trans_lt
    ((M35.roundCylinder_derivative_norm_le_jet hu B z hk).trans_lt
      ((hjet z hz).trans_lt hbound))

end PoincareConjecture.RoundCylinderClose
