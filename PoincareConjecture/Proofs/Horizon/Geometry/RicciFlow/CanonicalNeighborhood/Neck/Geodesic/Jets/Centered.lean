import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Charts










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

theorem fderiv_roundCylinderGram_center (q : UnitTwoSphere) (s : ℝ)
    (a b : Fin 3) :
    fderiv ℝ (fun p => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) (0, s) = 0 := by
  have hnorm : HasFDerivAt (fun p : RoundCylinderCoordinates => ‖p.1‖ ^ 2)
      (0 : RoundCylinderCoordinates →L[ℝ] ℝ) (0, s) := by
    simpa using (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).hasFDerivAt.norm_sq
      (x := (0, s))
  have hfactor : HasFDerivAt
      (fun p : RoundCylinderCoordinates => 2 * (1 - (0 : ℝ)) *
        (16 / (‖p.1‖ ^ 2 + 4) ^ 2))
      (0 : RoundCylinderCoordinates →L[ℝ] ℝ) (0, s) := by
    have hd : DifferentiableAt ℝ
        (fun t : ℝ => 2 * (1 - (0 : ℝ)) * (16 / (t + 4) ^ 2))
        (‖(0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2) := by
      fun_prop (disch := norm_num)
    simpa +instances only [Function.comp_def, ContinuousLinearMap.comp_zero] using
      hd.hasFDerivAt.comp (0, s) hnorm
  have h := (hfactor.mul_const
    ⟪(roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis b).1⟫_ℝ).add_const
      ((roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2)
  simpa only [roundCylinderGram_eq_stereographic_formula, smul_zero] using h.fderiv

theorem roundCylinderChristoffel_center (q : UnitTwoSphere) (s : ℝ)
    (a b d : Fin 3) :
    roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (0, s) a b d = 0 := by
  simp [roundCylinderChristoffel, fderiv_roundCylinderGram_center]

namespace EpsilonNeck

local instance : Bundle.RiemannianBundle
    (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
  ⟨roundCylinderProductMetric.toRiemannianMetric⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem normalized_pullback_first_jet_center (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 3 → Fin 3) :
    roundCylinderIteratedDerivative 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      N.normalized_pullback 1 (0, s) a =
    fderiv ℝ (fun p => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) (0, s)
      (roundCylinderCoordinateBasis (a 0)) := by
  have hB : DifferentiableAt ℝ (fun p => roundCylinderTensorCoefficient
      N.normalized_pullback (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2))
      (0, s) := by
    apply ((N.normalized_pullback_close.1 q (a 1) (a 2)).contDiffAt ?_).differentiableAt
      (by simp)
    rw [roundCylinder_sphereChart_target]
    exact (isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (0, s) ∈ (univ : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ
        Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, hs⟩)
  simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative,
    roundCylinderChristoffel_center, zero_mul, Finset.sum_const_zero, sub_zero]
  change (fderiv ℝ ((fun p => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) -
    (fun p => roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
      (a 1) (a 2))) (0, s)) (roundCylinderCoordinateBasis (a 0)) = _
  rw [fderiv_sub hB ((contDiff_roundCylinderGram 0 q (a 1) (a 2)).differentiable
    (by simp) (0, s)), fderiv_roundCylinderGram_center]
  simp

theorem norm_roundCylinderChartBasis_center_le_two
    (q : UnitTwoSphere) (s : ℝ) (i : Fin 3) :
    ‖roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) i‖ ≤ 2 := by
  have hsq : ‖roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) i‖ ^ 2 ≤ 2 := by
    rw [← real_inner_self_eq_norm_sq, roundCylinderChartBasis_apply]
    change roundCylinderProductMetric.inner _ _ _ ≤ _
    rw [roundCylinderChartFrame_gram, roundCylinderGram_eq_stereographic_formula,
      sphere_chart_center]
    fin_cases i <;> norm_num [roundCylinderCoordinateBasis]
  nlinarith [sq_nonneg (‖roundCylinderChartBasis q
    (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) i‖ - 2)]



theorem abs_normalized_pullback_coefficient_derivative_center_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i j k : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j k) (0, s)
      (roundCylinderCoordinateBasis i)| ≤ 8 * N.epsilon := by
  let a : Fin 3 → Fin 3 := ![i, j, k]
  have h := N.normalized_pullback_first_derivative_apply_le q hs
    (fun r => roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (a r))
  simp +instances only [componentMultilinearMap_basis, sphere_chart_center] at h
  rw [N.normalized_pullback_first_jet_center q hs] at h
  change |fderiv ℝ (fun p => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j k) (0, s)
      (roundCylinderCoordinateBasis i)| ≤ _ at h
  have hprod : (∏ r : Fin 3, ‖roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (a r)‖) ≤ 8 := by
    calc
      _ ≤ ∏ _r : Fin 3, (2 : ℝ) := Finset.prod_le_prod
        (fun r _ => norm_nonneg _) (fun r _ => norm_roundCylinderChartBasis_center_le_two q s (a r))
      _ = 8 := by norm_num
  calc
    _ ≤ N.epsilon * ∏ r : Fin 3, ‖roundCylinderChartBasis q
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (a r)‖ := h
    _ ≤ N.epsilon * 8 := mul_le_mul_of_nonneg_left hprod N.epsilon_pos.le
    _ = 8 * N.epsilon := mul_comm _ _

end EpsilonNeck
end PoincareConjecture
