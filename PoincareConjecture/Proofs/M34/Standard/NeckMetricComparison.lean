import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparisonCoordinates
import PoincareConjecture.Proofs.M34.Mathlib.WeightedMatrixPairing
import PoincareConjecture.Definitions.Ch09.NeckCapTopology










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates



noncomputable def roundCylinderMetricBilinear (z : RoundCylinderSpace) : V →L[ℝ] V →L[ℝ] ℝ :=
  let A : V →L[ℝ] E₃ :=
    (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => (q : E₃)) z.1).comp
      (ContinuousLinearMap.fst ℝ E₂ ℝ)
  (2 * (1 - (0 : ℝ))) • ContinuousLinearMap.bilinearComp (σ₁₃' := RingHom.id ℝ)
      (innerSL ℝ : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) A A +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ E₂ ℝ) (ContinuousLinearMap.snd ℝ E₂ ℝ)



theorem roundCylinderMetricBilinear_apply (z : RoundCylinderSpace) (v w : V) :
    roundCylinderMetricBilinear z v w = EvolvingRoundCylinderMetric 0 z v w := rfl

private theorem bilinear_apply_eq_sum (B : V →L[ℝ] V →L[ℝ] ℝ) (v : V) :
    B v v = ∑ i : Fin 3, ∑ j : Fin 3,
      B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) *
        (![v.1 0, v.1 1, v.2] i : ℝ) * (![v.1 0, v.1 1, v.2] j : ℝ) := by
  conv_lhs => rw [← sum_roundCylinderCoordinateBasis v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem roundCylinderMetricBilinear_apply_self (z : RoundCylinderSpace) (v : V) :
    roundCylinderMetricBilinear z v v =
      ∑ i : Fin 3, (![2, 2, 1] i : ℝ) * (![v.1 0, v.1 1, v.2] i : ℝ) ^ 2 := by
  have hgram (i j : Fin 3) :
      roundCylinderMetricBilinear z (roundCylinderCoordinateBasis i)
        (roundCylinderCoordinateBasis j) = Matrix.diagonal (![2, 2, 1] : Fin 3 → ℝ) i j := by
    rw [roundCylinderMetricBilinear_apply,
      ← roundCylinderTensorCoefficient_chart_center (EvolvingRoundCylinderMetric 0) z i j]
    change roundCylinderGram 0 (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2) i j = _
    rw [roundCylinderGram_chart_center]
    norm_num
  rw [bilinear_apply_eq_sum]
  simp [hgram, Matrix.diagonal_apply, pow_two, mul_assoc]

end PoincareConjecture.M34

namespace PoincareConjecture.EpsilonNeck

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)




theorem pullback_inner_error {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : RoundCylinderTangent z) :
    |N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v -
        EvolvingRoundCylinderMetric 0 z v v| ≤
      N.epsilon * EvolvingRoundCylinderMetric 0 z v v := by
  classical
  let L : RoundCylinderCoordinates →L[ℝ] EuclideanSpace ℝ (Fin 3) := by
    convert! mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z using 1
  let gB : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := by
    convert! g.inner (N.coordinate_map z) using 1
  let B : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
    (N.scale⁻¹ ^ 2) • gB.bilinearComp L L
  let D := roundCylinderMetricBilinear z
  let Bt : RoundCylinderTwoTensor := fun w a b =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map w a b
  have hd (i : Fin 3) : 0 < (![2, 2, 1] i : ℝ) := by fin_cases i <;> norm_num
  have hsq : (∑ i : Fin 3, ∑ j : Fin 3,
      (![2, 2, 1] i : ℝ)⁻¹ * (![2, 2, 1] j : ℝ)⁻¹ *
        ((B - D) (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2) ≤
      N.epsilon ^ 2 := by
    have hzero := roundCylinderJetErrorSquared_zero_eq Bt z
    change roundCylinderJetErrorSquared 0 Bt 0 z =
      (∑ i : Fin 3, ∑ j : Fin 3,
        (![2, 2, 1] i : ℝ)⁻¹ * (![2, 2, 1] j : ℝ)⁻¹ *
          ((B - D) (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2)
        at hzero
    rw [← hzero]
    obtain ⟨_, b, hb, hbound⟩ := N.metric_comparison.close
    exact (roundCylinderJetErrorSquared_mono_order (by norm_num : (0 : ℝ) < 1)
      Bt (Nat.zero_le _) z).trans ((hbound z hz).trans hb.le)
  have herr := abs_matrix_quadratic_le_of_weighted_sq ![2, 2, 1] hd
    (fun i j => (B - D) (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j))
    ![v.1 0, v.1 1, v.2] N.epsilon_pos.le hsq
  rw [← bilinear_apply_eq_sum, ← roundCylinderMetricBilinear_apply_self] at herr
  exact herr




theorem pullback_inner_comparison {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : RoundCylinderTangent z) :
    (1 / 2 : ℝ) * EvolvingRoundCylinderMetric 0 z v v ≤
        N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v ∧
      N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v ≤
        2 * EvolvingRoundCylinderMetric 0 z v v := by
  have herr := N.pullback_inner_error hz v
  have hD : 0 ≤ EvolvingRoundCylinderMetric 0 z v v := by
    rw [← roundCylinderMetricBilinear_apply]
    rw [roundCylinderMetricBilinear_apply_self]
    apply Finset.sum_nonneg
    intro i _
    have hi : 0 ≤ (![2, 2, 1] i : ℝ) := by fin_cases i <;> norm_num
    exact mul_nonneg hi (sq_nonneg _)
  have hsmall := mul_le_mul_of_nonneg_right N.epsilon_lt_half.le hD
  constructor <;> nlinarith [(abs_le.mp herr).1, (abs_le.mp herr).2]

end PoincareConjecture.EpsilonNeck
