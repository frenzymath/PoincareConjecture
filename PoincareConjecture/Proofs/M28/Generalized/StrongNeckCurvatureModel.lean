import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureOperator
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderModelJet

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M28

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckAnalysis tube

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev CMetric := MetricCoefficient 3
local instance : NormedAddCommGroup CMetric := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CMetric := ContinuousLinearMap.toNormedSpace
private abbrev CFirst := CE →L[ℝ] CMetric
local instance : NormedAddCommGroup CFirst := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CFirst := ContinuousLinearMap.toNormedSpace
private abbrev CSecond := CE →L[ℝ] CFirst
local instance : NormedAddCommGroup CSecond := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CSecond := ContinuousLinearMap.toNormedSpace

def cylinderAxialMetricCoefficient : MetricCoefficient 3 :=
  (innerSL ℝ).bilinearComp cylinderAxisProjection cylinderAxisProjection

def evolvingCylinderModelCoefficient (u : ℝ) (x : CE) : MetricCoefficient 3 :=
  (1 - u) • cylinderModelMetricCoefficient x + u • cylinderAxialMetricCoefficient

theorem evolvingCylinderModelCoefficient_apply (u : ℝ) (x v w : CE) :
    evolvingCylinderModelCoefficient u x v w =
      2 * (1 - u) * sphereChartConformalFactor (cylinderScalarCoordinateEquiv x).1 *
        inner ℝ (cylinderScalarCoordinateEquiv v).1 (cylinderScalarCoordinateEquiv w).1 +
      (cylinderScalarCoordinateEquiv v).2 * (cylinderScalarCoordinateEquiv w).2 := by
  have haxis : cylinderAxialMetricCoefficient v w =
      (cylinderScalarCoordinateEquiv v).2 * (cylinderScalarCoordinateEquiv w).2 := by
    simp [cylinderAxialMetricCoefficient, cylinderAxisProjection,
      ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply, mul_comm]
  simp only [evolvingCylinderModelCoefficient, add_apply, smul_apply, smul_eq_mul,
    cylinderModelMetricCoefficient_apply, haxis]
  ring

theorem evolvingCylinderModelCoefficient_basis
    (u : ℝ) (q : UnitTwoSphere) (s : ℝ) (x : CE) (a b : Fin 3) :
    evolvingCylinderModelCoefficient u x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (cylinderScalarCoordinates s x) a b := by
  rw [evolvingCylinderModelCoefficient_apply,
    cylinderScalarCoordinateEquiv_basis, cylinderScalarCoordinateEquiv_basis,
    roundCylinderGram_chosen_chart]
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderCoordinateBasis, cylinderScalarCoordinates, Matrix.diagonal,
      EuclideanSpace.inner_single_left, mul_comm]

theorem contDiff_evolvingCylinderModelCoefficient (u : ℝ) :
    ContDiff ℝ ∞ (evolvingCylinderModelCoefficient u) :=
  (contDiff_cylinderModelMetricCoefficient.const_smul (1 - u)).add contDiff_const

theorem evolvingCylinderModelCoefficient_zero_isInvertible
    {u : ℝ} (hu : u < 1) : (evolvingCylinderModelCoefficient u 0).IsInvertible := by
  apply PoincareConjecture.Proofs.M03.isInvertible_bilinear_of_pos
  intro v hv
  rw [evolvingCylinderModelCoefficient_apply]
  simp only [map_zero, Prod.fst_zero, sphereChartConformalFactor, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [real_inner_self_eq_norm_sq]
  have hne : cylinderScalarCoordinateEquiv v ≠ 0 := by
    intro hzero
    apply hv
    apply cylinderScalarCoordinateEquiv.injective
    simpa only [map_zero] using hzero
  have hpair : (cylinderScalarCoordinateEquiv v).1 ≠ 0 ∨
      (cylinderScalarCoordinateEquiv v).2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 h.2)
  have htime : 0 < 1 - u := sub_pos.mpr hu
  rcases hpair with hs | ha
  · have hp := sq_pos_of_pos (norm_pos_iff.mpr hs)
    nlinarith [mul_pos htime hp, sq_nonneg (cylinderScalarCoordinateEquiv v).2]
  · have hp := sq_pos_of_ne_zero ha
    nlinarith [mul_nonneg htime.le (sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖)]

def evolvingCylinderModelTwoJet (u : ℝ) : MetricTwoJet 3 :=
  metricTwoJet (evolvingCylinderModelCoefficient u) 0

theorem evolvingCylinderModelTwoJet_eq (u : ℝ) :
    evolvingCylinderModelTwoJet u =
      ((1 - u) • cylinderModelMetricCoefficient 0 + u • cylinderAxialMetricCoefficient,
        (1 - u) • fderiv ℝ cylinderModelMetricCoefficient 0,
        (1 - u) • fderiv ℝ (fderiv ℝ cylinderModelMetricCoefficient) 0) := by
  have hfirst (x : CE) : fderiv ℝ (evolvingCylinderModelCoefficient u) x =
      (1 - u) • fderiv ℝ cylinderModelMetricCoefficient x := by
    have hd := (contDiff_cylinderModelMetricCoefficient.differentiable
      (by simp) x).hasFDerivAt
    exact ((hd.const_smul (1 - u)).add_const (u • cylinderAxialMetricCoefficient)).fderiv
  have hsecond : fderiv ℝ (fderiv ℝ (evolvingCylinderModelCoefficient u)) 0 =
      (1 - u) • fderiv ℝ (fderiv ℝ cylinderModelMetricCoefficient) 0 := by
    rw [funext hfirst]
    exact (((contDiff_cylinderModelMetricCoefficient.contDiffAt.fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.const_smul (1 - u)).fderiv
  exact Prod.ext rfl (Prod.ext (hfirst 0) hsecond)

theorem continuous_evolvingCylinderModelTwoJet : Continuous evolvingCylinderModelTwoJet := by
  change Continuous (fun u : ℝ => evolvingCylinderModelTwoJet u)
  simp_rw [evolvingCylinderModelTwoJet_eq]
  fun_prop

theorem exists_half_cylinder_model_curvature_bound :
    ∃ eta : ℝ, 0 < eta ∧ ∃ K : ℝ, 0 < K ∧
      ∀ u ∈ Icc (-(1 / 2 : ℝ)) 0, ∀ J : MetricTwoJet 3,
        dist J (evolvingCylinderModelTwoJet u) < eta → jetCurvatureNorm J ≤ K := by
  let S := evolvingCylinderModelTwoJet '' Icc (-(1 / 2 : ℝ)) 0
  have hS : IsCompact S := isCompact_Icc.image continuous_evolvingCylinderModelTwoJet
  have hI : ∀ J ∈ S, J.1.IsInvertible := by
    rintro J ⟨u, hu, rfl⟩
    exact evolvingCylinderModelCoefficient_zero_isInvertible
      (lt_of_le_of_lt hu.2 (by norm_num))
  obtain ⟨eta, heta, hclose⟩ := exists_jetCurvatureNorm_uniform_modulus hS hI
    (by norm_num : (0 : ℝ) < 1)
  have hcontinuous : ContinuousOn jetCurvatureNorm S := fun J hJ =>
    (continuousAt_jetCurvatureNorm (hI J hJ)).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcontinuous
  refine ⟨eta, heta, max C 0 + 1, by positivity, ?_⟩
  intro u hu J hJ
  have hmodel : evolvingCylinderModelTwoJet u ∈ S := mem_image_of_mem _ hu
  have hdiff := (abs_lt.mp (hclose _ hmodel J hJ)).2
  have hbound : jetCurvatureNorm (evolvingCylinderModelTwoJet u) ≤ C := by
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC _ hmodel)
  linarith [le_max_left C 0]

end PoincareConjecture.M28
