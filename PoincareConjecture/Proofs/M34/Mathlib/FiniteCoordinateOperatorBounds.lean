import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic











set_option autoImplicit false

open scoped BigOperators



theorem PiLp.norm_le_card_mul_of_coordinates
    {p : ENNReal} [Fact (1 ≤ p)] {𝕜 I : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] (v : PiLp p fun _ : I => 𝕜) {C : ℝ}
    (hC : ∀ i, ‖v i‖ ≤ C) : ‖v‖ ≤ Fintype.card I * C := by
  classical
  let b := PiLp.basisFun p 𝕜 I
  let e : I → PiLp p (fun _ : I => 𝕜) := fun i => PiLp.single p i 1
  have hv : v = ∑ i : I, v i • e i := by
    simpa [b, e, PiLp.basisFun_repr, PiLp.basisFun_apply] using (b.sum_repr v).symm
  calc
    ‖v‖ = ‖∑ i : I, v i • e i‖ := congrArg norm hv
    _ ≤ ∑ i : I, ‖v i • e i‖ := norm_sum_le _ _
    _ = ∑ i : I, ‖v i‖ := by simp only [e, norm_smul, PiLp.norm_single, norm_one, mul_one]
    _ ≤ ∑ _i : I, C := Finset.sum_le_sum (fun i _ => hC i)
    _ = Fintype.card I * C := by simp




theorem ContinuousLinearMap.opNorm_le_card_mul_of_coordinates
    {p : ENNReal} [Fact (1 ≤ p)] {𝕜 I F : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] [DecidableEq I] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : (PiLp p fun _ : I => 𝕜) →L[𝕜] F) {C : ℝ}
    (hC : ∀ i, ‖L (PiLp.single p i (1 : 𝕜))‖ ≤ C) :
    ‖L‖ ≤ Fintype.card I * C := by
  have hsum : (∑ i : I, ‖L (PiLp.single p i (1 : 𝕜))‖) ≤ Fintype.card I * C := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hC i)
  apply L.opNorm_le_bound ((Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hsum)
  intro v
  let b := PiLp.basisFun p 𝕜 I
  have hv : v = ∑ i : I, v i • PiLp.single p i (1 : 𝕜) := by
    simpa [b, PiLp.basisFun_repr, PiLp.basisFun_apply] using (b.sum_repr v).symm
  calc
    ‖L v‖ = ‖∑ i : I, v i • L (PiLp.single p i (1 : 𝕜))‖ := by
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i : I, ‖v i • L (PiLp.single p i (1 : 𝕜))‖ := norm_sum_le _ _
    _ = ∑ i : I, ‖v i‖ * ‖L (PiLp.single p i (1 : 𝕜))‖ := by simp only [norm_smul]
    _ ≤ ∑ i : I, ‖v‖ * ‖L (PiLp.single p i (1 : 𝕜))‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = ‖v‖ * ∑ i : I, ‖L (PiLp.single p i (1 : 𝕜))‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖v‖ * (Fintype.card I * C) := mul_le_mul_of_nonneg_left hsum (norm_nonneg v)
    _ = (Fintype.card I * C) * ‖v‖ := mul_comm _ _
