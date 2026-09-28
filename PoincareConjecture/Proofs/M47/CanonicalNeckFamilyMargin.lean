import PoincareConjecture.Proofs.M47.CanonicalNeckStrictMargin










set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47



theorem exists_same_epsilon_neck_family_perturbation_tolerance
    {epsilon : ℝ} (_hepsilon : 0 < epsilon) {I : Set ℝ}
    (hI : ∀ u ∈ I, u ≤ 0) (D : ℝ → RoundCylinderTwoTensor)
    (hD : RoundCylinderFamilyClose epsilon I D) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ B : ℝ → RoundCylinderTwoTensor,
      (∀ u ∈ I, RoundCylinderTensorSmoothOn epsilon (B u)) →
      (∀ u ∈ I, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ∀ k ≤ Nat.floor epsilon⁻¹, ∀ a : Fin (2 + k) → Fin 3,
          |roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
              (B u) k (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a -
            roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
              (D u) k (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤ eta) →
      RoundCylinderFamilyClose epsilon I B := by
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
  · intro u hu z hz
    apply (cylinder_jet_error_weighted_le (hI u hu)
      (B u) (D u) (Nat.floor epsilon⁻¹) z htheta (hjet u hu z hz)).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hbound u hu z hz) (by positivity)) le_rfl

end PoincareConjecture.Proofs.M47
