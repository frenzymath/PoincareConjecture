import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.CylinderGeometry

/-!
# Positive component control in the literal cylinder norm

Morgan-Tian Definition 2.16 and Remark 2.17, p. 30, used in Theorem 12.28,
pp. 323-324. The exact inverse-Gram contraction is a positive weighted
sum of squares in the preferred central chart. Thus each actual covariant
metric-jet component is controlled by the frozen closeness certificate.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35

/-- Definition 2.16, p. 30: the full contraction, including derivative slots,
is the weighted sum of component squares in the actual central chart. -/
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

/-- Definition 2.16, p. 30: every inverse-Gram slot weight is strictly positive
at the preferred cylinder center as long as the model has not become singular. -/
theorem roundCylinderInverseWeight_pos {u : ℝ} (hu : u < 1) (a : Fin 3) :
    0 < ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] a := by
  fin_cases a <;> norm_num <;> linarith

/-- Definition 2.16, p. 30: the frozen cylinder tensor norm square is nonnegative
in its actual central chart, including rank zero. -/
theorem roundCylinderTensorNormSquared_nonneg {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T := by
  rw [roundCylinderTensorNormSquared_center hu]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg
    (Finset.prod_nonneg (fun i _ => (roundCylinderInverseWeight_pos hu (a i)).le))
    (sq_nonneg _))

/-- Definition 2.16, p. 30: each weighted component is bounded by the full
intrinsic tensor norm, with all covariant slots retained. -/
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

/-- Definition 2.16, p. 30: an individual covariant derivative norm is bounded
by the full metric-jet error sum through the retained order. -/
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

end PoincareMT.M35

namespace PoincareMT.RoundCylinderClose

/-- Definition 2.16, p. 30: literal cylindrical closeness controls every
covariant metric-jet component through floor(epsilon^-1), uniformly in its domain. -/
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

end PoincareMT.RoundCylinderClose
