import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Coefficients



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem exists_centeredNeck_initial_jet_bound (m : ℕ) :
    ∃ Z : ℝ, 0 < Z ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g),
        N.epsilon ≤ 1 → m ≤ ⌊N.epsilon⁻¹⌋₊ →
        ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j
            ((normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N z.1 z.2)) 0‖ ≤ Z := by
  obtain ⟨Z, hZ, hbound⟩ := exists_normalizedNeck_centered_coefficient_jet_bounds.{u} m
  refine ⟨Z, hZ, ?_⟩
  intro M _ _ _ g N _hε hm z hz j hj
  simpa only [RiemannianMetric.parametrizedCoefficients_eq_pullbackCoefficients] using
    hbound N j hj (hj.trans hm) z hz

theorem cylinderModelField_zero_upper (v : E) :
    cylinderModelField 0 v v ≤ 2 * ‖v‖ ^ 2 := by
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul] at hsplit
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  rw [cylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  nlinarith [sq_nonneg (cylinderHeightCovector v)]



theorem normalizedNeckMetric_centered_ellipticity
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 200) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        (normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N z.1 z.2) 0 v v ∧
      (normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N z.1 z.2) 0 v v ≤
        3 * ‖v‖ ^ 2 := by
  let B : RoundCylinderTwoTensor := fun z v w => normalizedNeckForm N z v w
  have horder : 2 ≤ ⌊N.epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    have h : (2 : ℝ) * N.epsilon ≤ 1 := by linarith
    rw [inv_eq_one_div]
    exact (le_div_iff₀ N.epsilon_pos).2 h
  have herr := (roundCylinderClose_error_operator_bounds N.epsilon_pos
    (show RoundCylinderClose N.epsilon 0 B from N.metric_comparison.close) horder z hz).1
  have hvalue := (centeredCylinderError B z.1 z.2 0).le_opNorm₂ v v
  rw [Real.norm_eq_abs] at hvalue
  have hsmall := mul_le_mul_of_nonneg_right herr (sq_nonneg ‖v‖)
  have hdiff : |centeredCylinderMetric B z.1 z.2 0 v v - cylinderModelField 0 v v| ≤
      18 * N.epsilon * ‖v‖ ^ 2 := by
    have heq := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v)
      (congrFun (centeredCylinderMetric_sub_model B z.1 z.2) 0)
    change centeredCylinderMetric B z.1 z.2 0 v v - cylinderModelField 0 v v =
      centeredCylinderError B z.1 z.2 0 v v at heq
    rw [heq]
    exact hvalue.trans (by nlinarith only [hsmall])
  rw [normalizedNeckMetric_pullbackCoefficients N z.1 z.2 (zero_mem_centeredNeckDomain N hz)]
  have hlo := cylinderModelField_zero_lower v
  have hhi := cylinderModelField_zero_upper v
  have hsmall' := mul_le_mul_of_nonneg_right hε (sq_nonneg ‖v‖)
  obtain ⟨hl, hu⟩ := abs_le.mp hdiff
  constructor <;> dsimp only [B] at hl hu <;> nlinarith

end PoincareConjecture.MetricSurgery
