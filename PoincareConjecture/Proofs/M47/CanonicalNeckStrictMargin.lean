import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckPerturbation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47

open M34

private theorem weighted_square_le {theta : ℝ} (htheta : 0 < theta) (T S : ℝ) :
    T ^ 2 ≤ (1 + theta) * S ^ 2 + (1 + theta⁻¹) * (T - S) ^ 2 := by
  have hid : theta * ((1 + theta) * S ^ 2 + (1 + theta⁻¹) * (T - S) ^ 2 - T ^ 2) =
      (theta * S - (T - S)) ^ 2 := by
    field_simp
    ring
  have hnonneg := sq_nonneg (theta * S - (T - S))
  rw [← hid] at hnonneg
  have h := nonneg_of_mul_nonneg_right hnonneg htheta
  linarith



theorem diagonal_tensor_contraction_weighted_le
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]
    (d : kappa → ℝ) (hd : ∀ i, 0 ≤ d i)
    (T S : (iota → kappa) → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    (∑ a : iota → kappa, ∑ b : iota → kappa,
      (∏ i, Matrix.diagonal d (a i) (b i)) * T a * T b) ≤
      (1 + theta) * (∑ a : iota → kappa, ∑ b : iota → kappa,
        (∏ i, Matrix.diagonal d (a i) (b i)) * S a * S b) +
      (1 + theta⁻¹) * (∑ a : iota → kappa, ∑ b : iota → kappa,
        (∏ i, Matrix.diagonal d (a i) (b i)) * (T a - S a) * (T b - S b)) := by
  simp only [diagonal_tensor_contraction, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ i, d (a i) := Finset.prod_nonneg fun i _ => hd (a i)
  have h := mul_le_mul_of_nonneg_left (weighted_square_le htheta (T a) (S a)) hw
  nlinarith



theorem cylinder_tensor_norm_weighted_le
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (z : ℝ) {r : ℕ}
    (T S : (Fin r → Fin 3) → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, z) T ≤
      (1 + theta) * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, z) S +
      (1 + theta⁻¹) * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, z) (fun a => T a - S a) := by
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_chart_center_inv hu.ne q z]
  apply diagonal_tensor_contraction_weighted_le _ _ T S htheta
  intro i
  fin_cases i
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.le))
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hu.le))
  · norm_num



theorem cylinder_jet_error_weighted_le
    {u : ℝ} (hu : u ≤ 0) (B D : RoundCylinderTwoTensor) (m : ℕ)
    (z : RoundCylinderSpace) {theta eta : ℝ} (htheta : 0 < theta)
    (hjet : ∀ k ≤ m, ∀ a : Fin (2 + k) → Fin 3,
      |roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a -
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) D k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤ eta) :
    roundCylinderJetErrorSquared u B m z ≤
      (1 + theta) * roundCylinderJetErrorSquared u D m z +
      (1 + theta⁻¹) * (∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2) * eta ^ 2 := by
  let error (k : ℕ) := roundCylinderTensorNormSquared u
    (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
    (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
    (fun a =>
      roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a -
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) D k
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a)
  have hfirst : roundCylinderJetErrorSquared u B m z ≤
      (1 + theta) * roundCylinderJetErrorSquared u D m z +
        (1 + theta⁻¹) * ∑ k ∈ Finset.range (m + 1), error k := by
    unfold roundCylinderJetErrorSquared
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun _ _ =>
      cylinder_tensor_norm_weighted_le (hu.trans_lt zero_lt_one) _ _ _ _ htheta
  have hsum : (∑ k ∈ Finset.range (m + 1), error k) ≤
      (∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2) * eta ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    simpa only [one_pow, mul_one] using roundCylinderTensorNormSquared_le
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2)
      (fun a =>
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a -
          roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) D k
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a)
      (M := 1) zero_le_one (roundCylinderGram_chart_center_inv_le_one hu z.1 z.2)
      (hjet k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  apply hfirst.trans
  simpa only [mul_assoc] using add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 + theta⁻¹))




theorem exists_same_epsilon_neck_perturbation_tolerance
    {epsilon : ℝ} (_hepsilon : 0 < epsilon) (D : RoundCylinderTwoTensor)
    (hD : RoundCylinderClose epsilon 0 D) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ B : RoundCylinderTwoTensor,
      RoundCylinderTensorSmoothOn epsilon B →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ∀ k ≤ Nat.floor epsilon⁻¹, ∀ a : Fin (2 + k) → Fin 3,
          |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a -
            roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) D k
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤ eta) →
      RoundCylinderClose epsilon 0 B := by
  obtain ⟨_, b, hb, hbound⟩ := hD
  let theta := (epsilon ^ 2 - b) / (2 * (|b| + 1))
  have htheta : 0 < theta := div_pos (sub_pos.mpr hb) (by positivity)
  have hthetab : theta * (|b| + 1) = (epsilon ^ 2 - b) / 2 := by
    dsimp only [theta]
    field_simp
  have hscaled : theta * b ≤ (epsilon ^ 2 - b) / 2 := by
    calc
      _ ≤ theta * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) htheta.le
      _ ≤ theta * (|b| + 1) := mul_le_mul_of_nonneg_left (by linarith) htheta.le
      _ = _ := hthetab
  have hbase : (1 + theta) * b < epsilon ^ 2 := by nlinarith
  let W : ℝ := ∑ k ∈ Finset.range (Nat.floor epsilon⁻¹ + 1), ((3 : ℝ) ^ (2 + k)) ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let A := (1 + theta⁻¹) * W
  have hA : 0 ≤ A := mul_nonneg (by positivity) hW
  let gamma := epsilon ^ 2 - (1 + theta) * b
  have hgamma : 0 < gamma := sub_pos.mpr hbase
  let eta := min 1 (gamma / (2 * (A + 1)))
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hgamma (by positivity))
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hsmall : (A + 1) * eta ≤ gamma / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp
      (min_le_right (1 : ℝ) (gamma / (2 * (A + 1))))
    change eta * (2 * (A + 1)) ≤ gamma at h
    nlinarith
  have hetasq : eta ^ 2 ≤ eta := by nlinarith
  have hAeta : A * eta ^ 2 ≤ gamma / 2 := by
    calc
      _ ≤ A * eta := mul_le_mul_of_nonneg_left hetasq hA
      _ ≤ (A + 1) * eta := mul_le_mul_of_nonneg_right (by linarith) heta.le
      _ ≤ _ := hsmall
  refine ⟨eta, heta, ?_⟩
  intro B hs hjet
  refine ⟨hs, (1 + theta) * b + A * eta ^ 2, ?_, ?_⟩
  · dsimp only [gamma] at hAeta
    nlinarith
  · intro z hz
    apply (cylinder_jet_error_weighted_le (by norm_num : (0 : ℝ) ≤ 0)
      B D (Nat.floor epsilon⁻¹) z htheta (hjet z hz)).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hbound z hz) (by positivity)) le_rfl

end PoincareConjecture.Proofs.M47
