import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_FiniteScalarBound
import PoincareConjecture.Proofs.M36.CylinderAllOrderBounds
import PoincareConjecture.Proofs.M36.CenteredNeckMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open PoincareConjecture.SpacetimeBounds PoincareConjecture.M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000 in

theorem exists_centeredCylinderMetric_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
      ∀ {B : RoundCylinderTwoTensor}, RoundCylinderClose epsilon 0 B →
      4 ≤ ⌊epsilon⁻¹⌋₊ → ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ j ≤ 4,
        ‖iteratedFDeriv ℝ j (centeredCylinderMetric B z.1 z.2) 0‖ ≤ C := by
  choose A hA hAbound using fun j : Fin 5 => exists_centeredCylinderError_jet_bound j
  let C : ℝ := 1 + ∑ j : Fin 5, (A j + ‖iteratedFDeriv ℝ j cylinderModelField 0‖)
  have hsum : 0 ≤ ∑ j : Fin 5, (A j + ‖iteratedFDeriv ℝ j cylinderModelField 0‖) :=
    Finset.sum_nonneg fun j _ => add_nonneg (hA j).le (norm_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro epsilon hepsilon hsmall B hB horder z hz j hj
  let k : Fin 5 := ⟨j, by omega⟩
  have heq : centeredCylinderMetric B z.1 z.2 =
      fun p => centeredCylinderError B z.1 z.2 p + cylinderModelField p := by
    funext p
    ext u v
    have hh := congrArg (fun L : MetricCoefficient 3 => L u v)
      (congrFun (centeredCylinderMetric_sub_model B z.1 z.2) p)
    change centeredCylinderMetric B z.1 z.2 p u v - cylinderModelField p u v =
      centeredCylinderError B z.1 z.2 p u v at hh
    change centeredCylinderMetric B z.1 z.2 p u v =
      centeredCylinderError B z.1 z.2 p u v + cylinderModelField p u v
    linarith only [hh]
  rw [heq, fun_iteratedFDeriv_add_apply
    ((centeredCylinderError_contDiffAt hB z hz).of_le (by exact_mod_cast le_top))
    (cylinderModelField_contDiff.contDiffAt.of_le (by exact_mod_cast le_top))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (centeredCylinderError B z.1 z.2) 0‖ +
        ‖iteratedFDeriv ℝ j cylinderModelField 0‖ := norm_add_le _ _
    _ ≤ A k * epsilon + ‖iteratedFDeriv ℝ j cylinderModelField 0‖ :=
      add_le_add (hAbound k hepsilon hB (hj.trans horder) z hz) le_rfl
    _ ≤ A k + ‖iteratedFDeriv ℝ j cylinderModelField 0‖ := by
      nlinarith [hA k]
    _ ≤ ∑ l : Fin 5, (A l + ‖iteratedFDeriv ℝ l cylinderModelField 0‖) :=
      Finset.single_le_sum
        (f := fun l : Fin 5 => A l + ‖iteratedFDeriv ℝ l cylinderModelField 0‖)
        (fun l _ => add_nonneg (hA l).le (norm_nonneg _))
        (Finset.mem_univ k)
    _ ≤ C := by dsimp [C]; linarith

theorem centeredCylinderMetric_lower {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 36) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon 0 B) (horder : 2 ≤ ⌊epsilon⁻¹⌋₊)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ centeredCylinderMetric B z.1 z.2 0 v v := by
  have hnorm := (roundCylinderClose_error_operator_bounds hepsilon hB horder z hz).1
  have herr : |centeredCylinderError B z.1 z.2 0 v v| ≤
      (18 * epsilon) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖centeredCylinderError B z.1 z.2 0‖ * ‖v‖ * ‖v‖ :=
        (centeredCylinderError B z.1 z.2 0).le_opNorm₂ v v
      _ ≤ (18 * epsilon) * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have hmodel := cylinderModelField_zero_lower v
  have heq := congrArg (fun L : MetricCoefficient 3 => L v v)
    (congrFun (centeredCylinderMetric_sub_model B z.1 z.2) 0)
  change centeredCylinderMetric B z.1 z.2 0 v v - cylinderModelField 0 v v =
    centeredCylinderError B z.1 z.2 0 v v at heq
  have hlo := (abs_le.mp herr).1
  nlinarith [mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖)]

theorem exists_centeredNeck_scalar_evolution_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ 1 / 36 →
        4 ≤ ⌊N.epsilon⁻¹⌋₊ → ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ (gE : RiemannianMetric 3 E) (DE : LeviCivitaData gE),
          gE.euclideanCoefficients =ᶠ[𝓝 0]
            centeredCylinderMetric (fun q v w => normalizedNeckForm N q v w) z.1 z.2 →
          |DE.laplacian DE.scalarCurvature 0 + 2 * DE.ricciNormSq 0| ≤ C := by
  obtain ⟨B, _, hB⟩ := exists_centeredCylinderMetric_fourJet_bound
  obtain ⟨C, hC, hbound⟩ := exists_scalar_evolution_bound_of_coordinate_jets 3
    (show 0 < (1 / 2 : ℝ) by norm_num) B
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g N hsmall horder z hz gE DE heq
  have hclose : RoundCylinderClose N.epsilon 0 (fun q v w => normalizedNeckForm N q v w) :=
    N.metric_comparison.close
  apply hbound gE DE 0
  · intro j hj
    rw [(heq.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
    exact hB N.epsilon_pos (by linarith) hclose horder z hz j hj
  · intro v
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gE.euclideanCoefficients 0 v v
    rw [heq.self_of_nhds]
    exact centeredCylinderMetric_lower N.epsilon_pos hsmall hclose
      (by omega) z hz v

end PoincareConjecture.M44
