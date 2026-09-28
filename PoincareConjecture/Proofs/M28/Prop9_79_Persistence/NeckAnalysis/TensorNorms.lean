import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.SphereGram

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

noncomputable def cylinderTensorWeight (u : ℝ) {r : ℕ} (a : Fin r → Fin 3) : ℝ :=
  ∏ i : Fin r, (cylinderGramDiagonal u (a i))⁻¹

theorem cylinderTensorWeight_pos {u : ℝ} (hu : u < 1) {r : ℕ}
    (a : Fin r → Fin 3) : 0 < cylinderTensorWeight u a := by
  apply Finset.prod_pos
  intro i _
  exact inv_pos.mpr (cylinderGramDiagonal_pos hu (a i))

theorem roundCylinderTensorNormSquared_eq_sum {u : ℝ} (hu : u < 1)
    (z : RoundCylinderSpace) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) T =
      ∑ a : Fin r → Fin 3, cylinderTensorWeight u a * (T a) ^ 2 := by
  classical
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_inverse_chosen_center hu]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp [Matrix.diagonal, cylinderTensorWeight, pow_two, mul_assoc]
  · intro b _ hba
    have hab : ¬ ∀ i, a i = b i := by
      intro h
      exact hba (funext h).symm
    change (∏ i, if a i = b i then (cylinderGramDiagonal u (a i))⁻¹ else 0) *
      T a * T b = 0
    simp only [Fintype.prod_ite_zero, if_neg hab, zero_mul]
  · simp

theorem roundCylinderTensorNormSquared_nonneg {u : ℝ} (hu : u < 1)
    (z : RoundCylinderSpace) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    0 ≤ roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) T := by
  rw [roundCylinderTensorNormSquared_eq_sum hu]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (cylinderTensorWeight_pos hu a).le (sq_nonneg _)

theorem square_le_weighted_square_sub {theta : ℝ} (htheta : 0 < theta)
    (x y : ℝ) : x ^ 2 ≤ (1 + theta) * y ^ 2 +
      (1 + theta⁻¹) * (x - y) ^ 2 := by
  have hs := sq_nonneg (theta * y - (x - y))
  have hid : ((1 + theta) * y ^ 2 + (1 + theta⁻¹) * (x - y) ^ 2) * theta -
      x ^ 2 * theta = (theta * y - (x - y)) ^ 2 := by
    field_simp [ne_of_gt htheta]
    ring
  exact (mul_le_mul_iff_right₀ htheta).mp (by nlinarith [hs, hid])

theorem roundCylinderTensorNormSquared_perturbation {u : ℝ} (hu : u < 1)
    (z : RoundCylinderSpace) {r : ℕ} (T S : (Fin r → Fin 3) → ℝ)
    {theta : ℝ} (htheta : 0 < theta) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
    let p : RoundCylinderCoordinates := (c z.1, z.2)
    roundCylinderTensorNormSquared u c p T ≤
      (1 + theta) * roundCylinderTensorNormSquared u c p S +
      (1 + theta⁻¹) * roundCylinderTensorNormSquared u c p (fun a => T a - S a) := by
  dsimp only
  simp only [roundCylinderTensorNormSquared_eq_sum hu]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_left
    (square_le_weighted_square_sub htheta (T a) (S a))
    (cylinderTensorWeight_pos hu a).le
  nlinarith [h]

theorem roundCylinderJetErrorSquared_nonneg {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) (order : ℕ) (z : RoundCylinderSpace) :
    0 ≤ roundCylinderJetErrorSquared u B order z := by
  apply Finset.sum_nonneg
  intro k _
  exact roundCylinderTensorNormSquared_nonneg hu z _

theorem roundCylinderJetErrorSquared_mono_order {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) {m n : ℕ} (hmn : m ≤ n)
    (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B m z ≤ roundCylinderJetErrorSquared u B n z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro k _ _
  exact roundCylinderTensorNormSquared_nonneg hu z _

noncomputable def cylinderJetDifferenceSquared (u : ℝ) (B C : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) : ℝ :=
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  ∑ k ∈ Finset.range (order + 1), roundCylinderTensorNormSquared u c p
    (fun a => roundCylinderIteratedDerivative u c B k p a -
      roundCylinderIteratedDerivative u c C k p a)

theorem roundCylinderJetErrorSquared_perturbation {u : ℝ} (hu : u < 1)
    (B C : RoundCylinderTwoTensor) (order : ℕ) (z : RoundCylinderSpace)
    {theta : ℝ} (htheta : 0 < theta) :
    roundCylinderJetErrorSquared u B order z ≤
      (1 + theta) * roundCylinderJetErrorSquared u C order z +
      (1 + theta⁻¹) * cylinderJetDifferenceSquared u B C order z := by
  unfold roundCylinderJetErrorSquared cylinderJetDifferenceSquared
  dsimp only
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  exact roundCylinderTensorNormSquared_perturbation hu z _ _ htheta

end PoincareConjecture.Proofs.M28.NeckAnalysis
