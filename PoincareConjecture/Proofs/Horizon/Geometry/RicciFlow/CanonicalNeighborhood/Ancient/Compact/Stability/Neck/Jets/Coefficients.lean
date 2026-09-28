import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderAllOrderBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.MetricSurgery

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem normalizedNeckMetric_centeredCoefficients_eq_model_add_error
    (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ)
    {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    (normalizedNeckMetric N).parametrizedCoefficients (centeredNeckLift N theta s) p =
      cylinderModelField p +
        centeredCylinderError (fun z v w => normalizedNeckForm N z v w) theta s p := by
  rw [RiemannianMetric.parametrizedCoefficients_eq_pullbackCoefficients,
    normalizedNeckMetric_pullbackCoefficients N theta s hp]
  have h := congrFun
    (centeredCylinderMetric_sub_model (fun z v w => normalizedNeckForm N z v w)
      theta s) p
  rw [← h]
  abel

theorem normalizedNeckMetric_centeredCoefficients_germ
    (N : EpsilonNeck g) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    (normalizedNeckMetric N).parametrizedCoefficients (centeredNeckLift N z.1 z.2)
      =ᶠ[𝓝 0] fun p => cylinderModelField p +
        centeredCylinderError (fun z v w => normalizedNeckForm N z v w) z.1 z.2 p := by
  filter_upwards [(centeredNeckDomain_isOpen N z.2).mem_nhds
    (zero_mem_centeredNeckDomain N hz)] with p hp
  exact normalizedNeckMetric_centeredCoefficients_eq_model_add_error N z.1 z.2 hp

theorem normalizedNeckMetric_centeredCoefficients_jet
    (N : EpsilonNeck g) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (m : ℕ) :
    iteratedFDeriv ℝ m
      ((normalizedNeckMetric N).parametrizedCoefficients (centeredNeckLift N z.1 z.2)) 0 =
      iteratedFDeriv ℝ m cylinderModelField 0 +
        iteratedFDeriv ℝ m
          (centeredCylinderError (fun z v w => normalizedNeckForm N z v w) z.1 z.2) 0 := by
  rw [((normalizedNeckMetric_centeredCoefficients_germ N z hz).iteratedFDeriv ℝ m).self_of_nhds]
  apply fun_iteratedFDeriv_add_apply
  · exact cylinderModelField_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  · exact (centeredCylinderError_contDiffAt N.metric_comparison.close z hz).of_le
      (by exact_mod_cast le_top)



theorem exists_normalizedNeck_centered_coefficient_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
        [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
        (N : EpsilonNeck g), m ≤ ⌊N.epsilon⁻¹⌋₊ →
        ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          ‖iteratedFDeriv ℝ m
            ((normalizedNeckMetric N).parametrizedCoefficients
              (centeredNeckLift N z.1 z.2)) 0‖ ≤ C := by
  obtain ⟨A, hA, hbound⟩ := exists_centeredCylinderError_jet_bound m
  refine ⟨‖iteratedFDeriv ℝ m cylinderModelField 0‖ + A,
    by positivity, ?_⟩
  intro M _ _ _ g N hm z hz
  rw [normalizedNeckMetric_centeredCoefficients_jet N z hz m]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  apply (hbound N.epsilon_pos N.metric_comparison.close hm z hz).trans
  exact (mul_le_mul_of_nonneg_left (show N.epsilon ≤ 1 by
    linarith [N.epsilon_lt_half]) hA.le).trans_eq (mul_one A)



theorem exists_normalizedNeck_centered_coefficient_jet_bounds (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
        [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
        (N : EpsilonNeck g) (j : ℕ), j ≤ m → j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          ‖iteratedFDeriv ℝ j
            ((normalizedNeckMetric N).parametrizedCoefficients
              (centeredNeckLift N z.1 z.2)) 0‖ ≤ C := by
  classical
  choose A hA hbound using fun j : Fin (m + 1) =>
    exists_normalizedNeck_centered_coefficient_jet_bound.{u} j
  have hsum : 0 ≤ ∑ j, A j := Finset.sum_nonneg (fun j _ => (hA j).le)
  refine ⟨1 + ∑ j, A j, by linarith, ?_⟩
  intro M _ _ _ g N j hj horder z hz
  let j' : Fin (m + 1) := ⟨j, by omega⟩
  have hle : A j' ≤ ∑ l, A l :=
    Finset.single_le_sum (fun l _ => (hA l).le) (Finset.mem_univ j')
  exact (hbound j' N horder z hz).trans (by linarith)

end PoincareConjecture.MetricSurgery
