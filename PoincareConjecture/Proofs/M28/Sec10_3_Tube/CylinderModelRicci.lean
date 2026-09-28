import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderJetReadout

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology InnerProductSpace

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev cb := EuclideanSpace.basisFun (Fin 3) ℝ
private abbrev CMetric := MetricCoefficient 3
local instance : NormedAddCommGroup CMetric := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CMetric := ContinuousLinearMap.toNormedSpace
private abbrev CFirst := CE →L[ℝ] CMetric
local instance : NormedAddCommGroup CFirst := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CFirst := ContinuousLinearMap.toNormedSpace
private abbrev CSecond := CE →L[ℝ] CFirst
local instance : NormedAddCommGroup CSecond := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CSecond := ContinuousLinearMap.toNormedSpace

private theorem cylinderModelMetricCoefficient_projection_apply (x v w : CE) :
    cylinderModelMetricCoefficient x v w =
      2 * sphereChartConformalFactor (cylinderSphereProjection x) *
        inner ℝ (cylinderSphereProjection v) (cylinderSphereProjection w) +
      cylinderAxisProjection v * cylinderAxisProjection w := by
  rw [cylinderModelMetricCoefficient_apply]
  rfl

theorem cylinderModelMetricCoefficient_fderiv_apply (x u v w : CE) :
    fderiv ℝ cylinderModelMetricCoefficient x u v w =
      2 * (-64 / (‖cylinderSphereProjection x‖ ^ 2 + 4) ^ 3) *
        inner ℝ (cylinderSphereProjection x) (cylinderSphereProjection u) *
        inner ℝ (cylinderSphereProjection v) (cylinderSphereProjection w) := by
  rw [← coefficient_fderiv_evaluation
    (contDiff_cylinderModelMetricCoefficient.differentiable (by simp) x)]
  simp_rw [cylinderModelMetricCoefficient_projection_apply]
  have hc := (hasFDerivAt_sphereChartConformalFactor
    (cylinderSphereProjection x)).comp x cylinderSphereProjection.hasFDerivAt
  have h := (((hc.const_mul 2).mul_const
    (inner ℝ (cylinderSphereProjection v) (cylinderSphereProjection w))).add_const
    (cylinderAxisProjection v * cylinderAxisProjection w))
  have heq := congrArg (fun L : CE →L[ℝ] ℝ => L u) h.fderiv
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul] at heq
  exact heq.trans (by ring)

theorem cylinderModelTwoJet_first_eq_zero : cylinderModelTwoJet.2.1 = 0 := by
  ext u v w
  change fderiv ℝ cylinderModelMetricCoefficient 0 u v w = 0
  rw [cylinderModelMetricCoefficient_fderiv_apply]
  simp

theorem cylinderModelTwoJet_second_apply (u v w z : CE) :
    cylinderModelTwoJet.2.2 u v w z =
      -2 * inner ℝ (cylinderSphereProjection u) (cylinderSphereProjection v) *
        inner ℝ (cylinderSphereProjection w) (cylinderSphereProjection z) := by
  have hB := contDiff_cylinderModelMetricCoefficient.contDiffAt (x := (0 : CE))
  have hD : DifferentiableAt ℝ (fderiv ℝ cylinderModelMetricCoefficient) 0 :=
    (hB.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have heval :
      fderiv ℝ (fun y => fderiv ℝ cylinderModelMetricCoefficient y v w z) 0 u =
        cylinderModelTwoJet.2.2 u v w z := by
    rw [fderiv_clm_apply
      ((hD.clm_apply (differentiableAt_const (c := v))).clm_apply
        (differentiableAt_const (c := w))) (differentiableAt_const (c := z)),
      fderiv_clm_apply (hD.clm_apply (differentiableAt_const (c := v)))
        (differentiableAt_const (c := w)),
      fderiv_clm_apply hD (differentiableAt_const (c := v))]
    simp [cylinderModelTwoJet, metricTwoJet]
  rw [← heval]
  simp_rw [cylinderModelMetricCoefficient_fderiv_apply]
  let f : CE → ℝ := fun x =>
    2 * (-64 / (‖cylinderSphereProjection x‖ ^ 2 + 4) ^ 3)
  have hdenSmooth : ContDiff ℝ ∞
      (fun x : CE => (‖cylinderSphereProjection x‖ ^ 2 + 4) ^ 3) :=
    (((contDiff_norm_sq ℝ).comp cylinderSphereProjection.contDiff).add
      contDiff_const).pow 3
  have hden := hdenSmooth.differentiable (by simp) (0 : CE)
  have hden0 : (‖cylinderSphereProjection (0 : CE)‖ ^ 2 + 4) ^ 3 ≠ 0 := by
    norm_num
  have hiDen : DifferentiableAt ℝ
      (fun x : CE => ((‖cylinderSphereProjection x‖ ^ 2 + 4) ^ 3)⁻¹) 0 :=
    hden.fun_inv hden0
  have hf : DifferentiableAt ℝ f 0 := by
    have h := (hiDen.const_mul (-64)).const_mul 2
    simpa only [f, div_eq_mul_inv] using h
  have hi := cylinderSphereProjection.hasFDerivAt.inner ℝ
    (hasFDerivAt_const (cylinderSphereProjection v) (0 : CE))
  have hh := ((hf.hasFDerivAt.mul hi).mul_const
    (inner ℝ (cylinderSphereProjection w) (cylinderSphereProjection z))).fderiv
  have heq := congrArg (fun L : CE →L[ℝ] ℝ => L u) hh
  norm_num [f] at heq
  convert heq using 1
  ring

private theorem cylinderModelMetricCoefficient_zero_coordinates (v w : CE) :
    cylinderModelMetricCoefficient 0 v w =
      2 * (v 0 * w 0 + v 1 * w 1) + v 2 * w 2 := by
  rw [cylinderModelMetricCoefficient_apply,
    cylinderScalarCoordinateEquiv_apply v, cylinderScalarCoordinateEquiv_apply w]
  norm_num [sphereChartConformalFactor, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, mul_comm]

theorem cylinderModelTwoJet_inverse_coefficient (i j : Fin 3) :
    EuclideanSpace.proj j (cylinderModelTwoJet.1.inverse (EuclideanSpace.proj i)) =
      if i = j then (cylinderGramDiagonal 0 i)⁻¹ else 0 := by
  have h := congrArg (fun L : CE →L[ℝ] ℝ => L (cb j))
    (cylinderModelMetricCoefficient_zero_isInvertible.self_apply_inverse
      (EuclideanSpace.proj i))
  let v : CE := (cylinderModelMetricCoefficient 0).inverse (EuclideanSpace.proj i)
  change cylinderModelMetricCoefficient 0 v (cb j) = (cb j) i at h
  rw [cylinderModelMetricCoefficient_zero_coordinates] at h
  change v j = _
  fin_cases i <;> fin_cases j <;>
    norm_num [cb, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      cylinderGramDiagonal, Fin.ext_iff] at h ⊢
  · change v 0 = (1 / 2 : ℝ)
    linarith only [h]
  · change v 1 = 0
    linarith only [h]
  · change v 2 = 0
    linarith only [h]
  · change v 0 = 0
    linarith only [h]
  · change v 1 = (1 / 2 : ℝ)
    linarith only [h]
  · change v 2 = 0
    linarith only [h]
  · change v 0 = 0
    linarith only [h]
  · change v 1 = 0
    linarith only [h]
  · change v 2 = 1
    exact h

private theorem cylinderModelTwoJet_christoffel (u v : CE) :
    jetChristoffel cylinderModelTwoJet u v = 0 := by
  simp [jetChristoffel, cylinderModelTwoJet_first_eq_zero, metricKoszulCovector]

theorem cylinderModelTwoJet_curvature (u w v z : CE) :
    jetCurvature cylinderModelTwoJet u w v z =
      2 * (inner ℝ (cylinderSphereProjection u) (cylinderSphereProjection v) *
        inner ℝ (cylinderSphereProjection w) (cylinderSphereProjection z) -
      inner ℝ (cylinderSphereProjection u) (cylinderSphereProjection z) *
        inner ℝ (cylinderSphereProjection w) (cylinderSphereProjection v)) := by
  simp only [jetCurvature, cylinderModelTwoJet_first_eq_zero,
    cylinderModelTwoJet_christoffel, cylinderModelTwoJet_second_apply,
    zero_apply, map_zero, neg_zero, add_zero, sub_zero]
  ring

theorem cylinderModelTwoJet_ricci (u v : CE) :
    jetRicci cylinderModelTwoJet u v =
      inner ℝ (cylinderSphereProjection u) (cylinderSphereProjection v) := by
  have hcb (i : Fin 3) : cylinderSphereProjection (cb i) =
      (roundCylinderCoordinateBasis i).1 := by
    change (cylinderScalarCoordinateEquiv (cb i)).1 = _
    rw [cylinderScalarCoordinateEquiv_basis]
  simp only [jetRicci, cylinderModelTwoJet_inverse_coefficient,
    cylinderModelTwoJet_curvature, hcb]
  norm_num [Fin.sum_univ_three, cylinderGramDiagonal, roundCylinderCoordinateBasis,
    Matrix.cons_val_two, Fin.isValue,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

end PoincareConjecture.M28.tube
