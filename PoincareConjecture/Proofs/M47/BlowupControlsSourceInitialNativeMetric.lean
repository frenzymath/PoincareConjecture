import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

private noncomputable def initialNativeBilinear (u : ℝ) (z : RoundCylinderSpace) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  let A : V →L[ℝ] E₃ :=
    (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => (q : E₃)) z.1).comp
      (ContinuousLinearMap.fst ℝ E₂ ℝ)
  (2 * (1 - u)) • ContinuousLinearMap.bilinearComp (σ₁₃' := RingHom.id ℝ)
      (innerSL ℝ : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) A A +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ E₂ ℝ) (ContinuousLinearMap.snd ℝ E₂ ℝ)

private theorem initialNativeBilinear_apply (u : ℝ) (z : RoundCylinderSpace) (v w : V) :
    initialNativeBilinear u z v w = EvolvingRoundCylinderMetric u z v w := rfl

private theorem initialNativeBilinear_sum (B : V →L[ℝ] V →L[ℝ] ℝ) (v : V) :
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

private theorem initialNativeBilinear_self (u : ℝ) (z : RoundCylinderSpace) (v : V) :
    initialNativeBilinear u z v v =
      ∑ i : Fin 3, (![2 * (1 - u), 2 * (1 - u), 1] i : ℝ) *
        (![v.1 0, v.1 1, v.2] i : ℝ) ^ 2 := by
  have hgram (i j : Fin 3) :
      initialNativeBilinear u z (roundCylinderCoordinateBasis i)
        (roundCylinderCoordinateBasis j) =
      Matrix.diagonal (![2 * (1 - u), 2 * (1 - u), 1] : Fin 3 → ℝ) i j := by
    rw [initialNativeBilinear_apply,
      ← roundCylinderTensorCoefficient_chart_center (EvolvingRoundCylinderMetric u) z i j]
    change roundCylinderGram u (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2) i j = _
    rw [roundCylinderGram_chart_center]
  rw [initialNativeBilinear_sum]
  simp [hgram, Matrix.diagonal_apply, pow_two, mul_assoc]

private theorem initialNativeError_zero {u : ℝ} (hu : u < 1)
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B 0 z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (![2 * (1 - u), 2 * (1 - u), 1] i : ℝ)⁻¹ *
        (![2 * (1 - u), 2 * (1 - u), 1] j : ℝ)⁻¹ *
          (B z (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
            EvolvingRoundCylinderMetric u z
              (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2 := by
  simp only [roundCylinderJetErrorSquared, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_chart_center_inv hu.ne]
  have hvec : (![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] : Fin 3 → ℝ) =
      fun i => (![2 * (1 - u), 2 * (1 - u), 1] i : ℝ)⁻¹ := by
    ext i
    fin_cases i <;> norm_num
  rw [hvec, diagonal_tensor_contraction (ι := Fin 2) (κ := Fin 3)]
  simp only [Fin.prod_univ_two, roundCylinderIteratedDerivative,
    roundCylinderGram, roundCylinderTensorCoefficient_chart_center]
  exact ((finTwoArrowEquiv (Fin 3)).sum_comp (fun p : Fin 3 × Fin 3 =>
    (![2 * (1 - u), 2 * (1 - u), 1] p.1 : ℝ)⁻¹ *
    (![2 * (1 - u), 2 * (1 - u), 1] p.2 : ℝ)⁻¹ *
      (B z (roundCylinderCoordinateBasis p.1) (roundCylinderCoordinateBasis p.2) -
        EvolvingRoundCylinderMetric u z
          (roundCylinderCoordinateBasis p.1) (roundCylinderCoordinateBasis p.2)) ^ 2)).trans
    (Fintype.sum_prod_type _)

theorem source_initial_native_metric_error
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hu : u < 1)
    {B : RoundCylinderTwoTensor} (hclose : RoundCylinderClose epsilon u B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (L : V →L[ℝ] V →L[ℝ] ℝ) (hL : ∀ v w, L v w = B z v w) (v : V) :
    |B z v v - EvolvingRoundCylinderMetric u z v v| ≤
      epsilon * EvolvingRoundCylinderMetric u z v v := by
  classical
  let D := initialNativeBilinear u z
  let d : Fin 3 → ℝ := ![2 * (1 - u), 2 * (1 - u), 1]
  have hd (i : Fin 3) : 0 < d i := by
    fin_cases i <;> norm_num [d] <;> linarith only [hu]
  have hsq : (∑ i : Fin 3, ∑ j : Fin 3,
      (d i)⁻¹ * (d j)⁻¹ *
        ((L - D) (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2) ≤
      epsilon ^ 2 := by
    obtain ⟨_, bound, hbound, herror⟩ := hclose
    have hzero := (roundCylinderJetErrorSquared_mono_order hu B (Nat.zero_le _) z).trans
      ((herror z hz).trans hbound.le)
    rw [initialNativeError_zero hu] at hzero
    simpa only [d, D, sub_apply, hL, initialNativeBilinear_apply] using hzero
  have herr := abs_matrix_quadratic_le_of_weighted_sq d hd
    (fun i j => (L - D) (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j))
    ![v.1 0, v.1 1, v.2] hepsilon.le hsq
  rw [← initialNativeBilinear_sum, ← initialNativeBilinear_self] at herr
  simpa only [D, sub_apply, hL, initialNativeBilinear_apply] using herr

theorem source_initial_native_metric_bounds
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 2) (hu : u < 1)
    {B : RoundCylinderTwoTensor} (hclose : RoundCylinderClose epsilon u B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (L : V →L[ℝ] V →L[ℝ] ℝ) (hL : ∀ v w, L v w = B z v w) (v : V) :
    (1 / 2 : ℝ) * EvolvingRoundCylinderMetric u z v v ≤ B z v v ∧
      B z v v ≤ (3 / 2 : ℝ) * EvolvingRoundCylinderMetric u z v v := by
  have herr := source_initial_native_metric_error hepsilon hu hclose z hz L hL v
  have hnonneg : 0 ≤ EvolvingRoundCylinderMetric u z v v := by
    change 0 ≤ 2 * (1 - u) * inner ℝ (E := E₃) _ _ + v.2 * v.2
    exact add_nonneg (mul_nonneg (by linarith only [hu]) real_inner_self_nonneg)
      (mul_self_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hsmall hnonneg
  constructor <;> linarith only [(abs_le.mp herr).1, (abs_le.mp herr).2, hmul]

end PoincareConjecture.M47
