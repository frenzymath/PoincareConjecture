import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_EvolvingJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderCurvature
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_FiniteScalarBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.Proofs.M47

open M36 M44 M45 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem negativeCylinder_coefficient_error {epsilon t : ℝ} (hepsilon : 0 < epsilon)
    (ht : t ∈ Icc (-1 : ℝ) 0) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon t B) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ‖centeredCylinderMetric B z.1 z.2 0 - evolvingCylinderModelField t 0‖ ≤
      36 * epsilon := by
  let B0 := staticCylinderCorrection t B
  let V (i j : Fin 3) : E →L[ℝ] E →L[ℝ] ℝ :=
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)).smulRight
      (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ j))
  have hV (i j : Fin 3) : ‖V i j‖ = 1 := by simp [V]
  have hterm (i j : Fin 3) :
      ‖centeredCylinderComponent B0 z.1 z.2 0 ![i, j] 0 • V i j‖ ≤ 4 * epsilon := by
    rw [norm_smul, hV, mul_one]
    simpa only [Nat.add_zero, pow_two, show (2 : ℝ) * 2 = 4 by norm_num] using
      correctedCylinderComponent_bound hepsilon.le ht hB (Nat.zero_le _) z hz ![i, j]
  have heq : (fun p => centeredCylinderMetric B z.1 z.2 p - evolvingCylinderModelField t p) =
      fun p => ∑ i, ∑ j, centeredCylinderComponent B0 z.1 z.2 0 ![i, j] p • V i j := by
    rw [← staticCylinderCorrection_centered_error, centeredCylinderMetric_sub_model]
    rfl
  rw [congrFun heq 0]
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
        centeredCylinderComponent B0 z.1 z.2 0 ![i, j] 0 • V i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ‖centeredCylinderComponent B0 z.1 z.2 0 ![i, j] 0 • V i j‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * epsilon :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp; ring

theorem negativeCylinder_coefficient_lower {epsilon t : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 200) (ht : t ∈ Icc (-1 : ℝ) 0)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon t B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ centeredCylinderMetric B z.1 z.2 0 v v := by
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hmodel : ‖v‖ ^ 2 ≤ evolvingCylinderModelField t 0 v v := by
    rw [evolvingCylinderModelField_zero]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    nlinarith [ht.2]
  have herr : |centeredCylinderMetric B z.1 z.2 0 v v -
      evolvingCylinderModelField t 0 v v| ≤ 36 * epsilon * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖centeredCylinderMetric B z.1 z.2 0 - evolvingCylinderModelField t 0‖ *
          ‖v‖ * ‖v‖ :=
        (centeredCylinderMetric B z.1 z.2 0 - evolvingCylinderModelField t 0).le_opNorm₂ v v
      _ ≤ (36 * epsilon) * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (negativeCylinder_coefficient_error hepsilon ht hB z hz) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have hlo := (abs_le.mp herr).1
  have hsmall' : 36 * epsilon ≤ 1 / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hsmall' (sq_nonneg ‖v‖)]

theorem exists_negativeCylinder_twoJet_bound :
    ∃ H : ℝ, 0 < H ∧ ∀ {epsilon t : ℝ}, 0 < epsilon → epsilon ≤ 1 / 200 →
      t ∈ Icc (-1 : ℝ) 0 → ∀ {B : RoundCylinderTwoTensor},
      RoundCylinderClose epsilon t B → ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ‖metricTwoJet (centeredCylinderMetric B z.1 z.2) 0‖ ≤ H := by
  choose A hA hAbound using fun j : Fin 3 => exists_evolvingCylinderError_jet_bound j
  let A0 : ℝ := ∑ j : Fin 3, A j
  have hA0 : 0 ≤ A0 := Finset.sum_nonneg fun j _ => (hA j).le
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_evolvingCylinderModelJet.continuousOn :
      ContinuousOn evolvingCylinderModelJet (Icc (-1 : ℝ) 0))
  refine ⟨A0 + |C| + 1, by positivity, ?_⟩
  intro epsilon t hepsilon hsmall ht B hB z hz
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    rw [inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith
  let G := centeredCylinderMetric B z.1 z.2
  let D := fun p => G p - evolvingCylinderModelField t p
  have hG : ContDiffAt ℝ ∞ G 0 := evolving_centeredCylinderMetric_contDiffAt hB z hz
  have hD : ContDiffAt ℝ ∞ D 0 :=
    hG.sub (evolvingCylinderModelField_contDiff t).contDiffAt
  have hjets (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j D 0‖ ≤ A0 := by
    let k : Fin 3 := ⟨j, by omega⟩
    calc
      _ ≤ A k * epsilon := hAbound k hepsilon ht hB (hj.trans horder) z hz
      _ ≤ A k := by nlinarith [hA k]
      _ ≤ A0 := Finset.single_le_sum (fun l _ => (hA l).le) (Finset.mem_univ k)
  have hjet := norm_iteratedFDeriv_metricTwoJet_le (m := 0) hD hjets
  rw [norm_iteratedFDeriv_zero] at hjet
  have heq : metricTwoJet D 0 = metricTwoJet G 0 - evolvingCylinderModelJet t :=
    metricTwoJet_sub_of_contDiffAt hG (evolvingCylinderModelField_contDiff t).contDiffAt
  rw [heq] at hjet
  calc
    _ ≤ ‖metricTwoJet G 0 - evolvingCylinderModelJet t‖ +
        ‖evolvingCylinderModelJet t‖ := norm_le_norm_sub_add _ _
    _ ≤ A0 + C := add_le_add hjet (hC t ht)
    _ ≤ A0 + |C| + 1 := by linarith [le_abs_self C]

end PoincareConjecture.Proofs.M47
