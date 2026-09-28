import PoincareConjecture.Proofs.M47.CanonicalNeckStrictMargin










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open M34 PoincareConjecture.Proofs.M47



theorem terminalCurvature_exists_double_neck_array_tolerance
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ D : RoundCylinderTwoTensor,
      RoundCylinderClose epsilon 0 D → ∀ B : RoundCylinderTwoTensor,
      RoundCylinderTensorSmoothOn (2 * epsilon) B →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ →
        ∀ k ≤ Nat.floor (2 * epsilon)⁻¹, ∀ a : Fin (2 + k) → Fin 3,
          |roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a -
            roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) D k
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a| ≤ eta) →
      RoundCylinderClose (2 * epsilon) 0 B := by
  let m := Nat.floor (2 * epsilon)⁻¹
  let S := ∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let eta := min 1 (epsilon ^ 2 / (4 * (S + 1)))
  have heta : 0 < eta := lt_min zero_lt_one (div_pos (sq_pos_of_pos hepsilon) (by positivity))
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hsmall : 4 * (S + 1) * eta ≤ epsilon ^ 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (S + 1))).mp
      (min_le_right (1 : ℝ) (epsilon ^ 2 / (4 * (S + 1))))
    nlinarith only [hh]
  have htail : 2 * S * eta ^ 2 ≤ epsilon ^ 2 := by
    have he2 : eta ^ 2 ≤ eta := by nlinarith only [heta.le, heta1]
    have hs := mul_le_mul_of_nonneg_left he2 hS
    nlinarith only [hs, hsmall, heta.le]
  refine ⟨eta, heta, ?_⟩
  intro D hD B hB hjet
  obtain ⟨_, b, hb, hbound⟩ := hD
  have hinv : (2 * epsilon)⁻¹ ≤ epsilon⁻¹ :=
    inv_anti₀ hepsilon (by linarith)
  refine ⟨hB, 3 * epsilon ^ 2, by nlinarith only [sq_pos_of_pos hepsilon], ?_⟩
  intro z hz
  have hzold : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨(neg_le_neg hinv).trans_lt hz.1, hz.2.trans_le hinv⟩
  have hold : roundCylinderJetErrorSquared 0 D m z ≤ epsilon ^ 2 :=
    ((roundCylinderJetErrorSquared_mono_order zero_lt_one D
      (Nat.floor_mono hinv) z).trans (hbound z hzold)).trans hb.le
  have h := cylinder_jet_error_weighted_le (u := 0) le_rfl B D m z
    (theta := 1) zero_lt_one (hjet z hz)
  norm_num only [one_div, inv_one] at h
  change roundCylinderJetErrorSquared 0 B m z ≤ 2 * roundCylinderJetErrorSquared 0 D m z +
    2 * S * eta ^ 2 at h
  exact h.trans (by linarith only [hold, htail])

end PoincareConjecture.M47
