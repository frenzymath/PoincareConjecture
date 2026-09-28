import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderModelJet
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderCoefficientBounds
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderJetNorm
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundGaussJetReadout

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

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

private theorem coefficient_second_fderiv_of_contDiffAt
    {F : CE → MetricCoefficient 3} (hF : ContDiffAt ℝ ∞ F 0)
    (u v w z : CE) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => F x w z) y v) 0 u =
      fderiv ℝ (fderiv ℝ F) 0 u v w z := by
  have hF1 : ContDiffAt ℝ 1 F 0 := hF.of_le (by simp)
  have heq : (fun y => fderiv ℝ (fun x => F x w z) y v) =ᶠ[𝓝 0]
      (fun y => fderiv ℝ F y v w z) := by
    filter_upwards [hF1.eventually (by norm_num)] with y hy
    exact coefficient_fderiv_evaluation (hy.differentiableAt (by norm_num)) v w z
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [heq.fderiv_eq, coefficient_fderiv_evaluation
    (hDF.clm_apply (differentiableAt_const (c := v)))]
  rw [fderiv_clm_apply hDF (differentiableAt_const (c := v))]
  simp

private theorem cylinder_affine_first_derivative
    (s : ℝ) {f : RoundCylinderCoordinates → ℝ}
    (hf : DifferentiableAt ℝ f (0, s)) (i : Fin 3) :
    fderiv ℝ (fun x => f (cylinderScalarCoordinates s x)) 0 (cb i) =
      fderiv ℝ f (0, s) (roundCylinderCoordinateBasis i) := by
  have hf' : DifferentiableAt ℝ f (cylinderScalarCoordinates s 0) := by
    simpa only [cylinderScalarCoordinates_zero] using hf
  change fderiv ℝ (f ∘ cylinderScalarCoordinates s) 0 (cb i) = _
  rw [fderiv_comp 0 hf' (cylinderScalarCoordinates_hasFDerivAt s 0).differentiableAt,
    (cylinderScalarCoordinates_hasFDerivAt s 0).fderiv]
  simp only [ContinuousLinearMap.comp_apply, cylinderScalarCoordinates_zero,
    ContinuousLinearEquiv.coe_coe, cylinderScalarCoordinateEquiv_basis]

private theorem cylinder_affine_second_derivative
    (s : ℝ) {f : RoundCylinderCoordinates → ℝ}
    (hf : ContDiffAt ℝ ∞ f (0, s)) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => f (cylinderScalarCoordinates s x)) y
        (cb i)) 0 (cb j) =
      fderiv ℝ (fun p => fderiv ℝ f p (roundCylinderCoordinateBasis i))
        (0, s) (roundCylinderCoordinateBasis j) := by
  have hf1 : ContDiffAt ℝ 1 f (0, s) := hf.of_le (by simp)
  have ht : Tendsto (cylinderScalarCoordinates s) (𝓝 (0 : CE)) (𝓝 (0, s)) := by
    have hc : ContinuousAt (cylinderScalarCoordinates s) (0 : CE) :=
      (contDiff_cylinderScalarCoordinates s).continuous.continuousAt
    simpa only [cylinderScalarCoordinates_zero] using
      hc.tendsto
  have heq : (fun y => fderiv ℝ (fun x => f (cylinderScalarCoordinates s x)) y
      (cb i)) =ᶠ[𝓝 (0 : CE)]
      (fun y => fderiv ℝ f (cylinderScalarCoordinates s y)
        (roundCylinderCoordinateBasis i)) := by
    filter_upwards [ht.eventually (hf1.eventually (by norm_num))] with y hy
    have h := (hy.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (cylinderScalarCoordinates_hasFDerivAt s y)
    change fderiv ℝ (f ∘ cylinderScalarCoordinates s) y (cb i) = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      cylinderScalarCoordinateEquiv_basis]
  rw [heq.fderiv_eq]
  have hdf : ContDiffAt ℝ ∞
      (fun p => fderiv ℝ f p (roundCylinderCoordinateBasis i)) (0, s) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  exact cylinder_affine_first_derivative s (hdf.differentiableAt (by simp)) j

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

private def normalizedNeckTensor (N : EpsilonNeck g) : RoundCylinderTwoTensor :=
  fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w

def cylinderErrorCoefficients (N : EpsilonNeck g) (z : RoundCylinderSpace) :
    CE → MetricCoefficient 3 :=
  fun x => cylinderNeckCoefficients N z.1 z.2 x - cylinderModelMetricCoefficient x

theorem cylinderErrorCoefficients_contDiffAt (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (cylinderErrorCoefficients N z) 0 :=
  ((contDiffOn_cylinderNeckCoefficients N z.1 z.2).contDiffAt
    ((isOpen_cylinderNeckChartDomain N z.1 z.2).mem_nhds
      (zero_mem_cylinderNeckChartDomain N z.1 hz))).sub
    contDiff_cylinderModelMetricCoefficient.contDiffAt

private theorem cylinder_error_frozen_germ (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (a b : Fin 3) :
    (fun x => cylinderErrorCoefficients N z x (cb a) (cb b)) =ᶠ[𝓝 (0 : CE)]
      (fun x => roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) (normalizedNeckTensor N) 0
        (cylinderScalarCoordinates z.2 x) ![a, b]) := by
  filter_upwards [cylinderNeckCoefficients_frozen_germ N z.1 hz a b] with x hx
  change cylinderNeckCoefficients N z.1 z.2 x (cb a) (cb b) -
    cylinderModelMetricCoefficient x (cb a) (cb b) = _
  rw [hx, cylinderModelMetricCoefficient_basis z.1 z.2 x a b]
  rfl

theorem exists_cylinder_metricTwoJet_bound :
    ∃ L : ℝ, 0 < L ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
        2 ≤ ⌊N.epsilon⁻¹⌋₊ → ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        dist (metricTwoJet (cylinderNeckCoefficients N z.1 z.2) 0)
          cylinderModelTwoJet ≤ L * N.epsilon := by
  obtain ⟨K, hK, hnorm⟩ := exists_metricTwoJet_coefficient_bound
  obtain ⟨C, hC, hsecond⟩ := exists_cylinder_second_component_bound
  refine ⟨K * (4 + C), mul_pos hK (by positivity), ?_⟩
  intro M _ _ _ g N horder z hz
  let B := normalizedNeckTensor N
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let T := roundCylinderIteratedDerivative 0 c B 0
  let F := cylinderErrorCoefficients N z
  have hB : RoundCylinderClose N.epsilon 0 B := N.metric_comparison.close
  have hF : ContDiffAt ℝ ∞ F 0 := cylinderErrorCoefficients_contDiffAt N hz
  have hFdiff : DifferentiableAt ℝ F 0 := hF.differentiableAt (by simp)
  have hp : (0, z.2) ∈ c.target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    rw [← sphere_chart_center z.1]
    exact c.map_source (mem_chart_source _ z.1)
  have hT (a : Fin 2 → Fin 3) : ContDiffAt ℝ ∞ (fun p => T p a) (0, z.2) :=
    (contDiffOn_roundCylinderIteratedDerivative (by norm_num) hB.1 z.1 0 a).contDiffAt
      ((c.open_target.prod isOpen_Ioo).mem_nhds hp)
  have hfour : 4 * N.epsilon ≤ (4 + C) * N.epsilon := by
    nlinarith [N.epsilon_pos]
  have hCbound : C * N.epsilon ≤ (4 + C) * N.epsilon := by
    nlinarith [N.epsilon_pos]
  have hzero (a b : Fin 3) : |F 0 (cb a) (cb b)| ≤ (4 + C) * N.epsilon := by
    have heq : F 0 (cb a) (cb b) =
        T (cylinderScalarCoordinates z.2 0) ![a, b] :=
      (cylinder_error_frozen_germ N hz a b).self_of_nhds
    rw [heq, cylinderScalarCoordinates_zero]
    exact (cylinder_covariant_component_le (k := 0) N.epsilon_pos hB hz
      (by omega) (by omega) ![a, b]).trans hfour
  have hfirst (i a b : Fin 3) :
      |fderiv ℝ F 0 (cb i) (cb a) (cb b)| ≤ (4 + C) * N.epsilon := by
    rw [← coefficient_fderiv_evaluation hFdiff,
      (cylinder_error_frozen_germ N hz a b).fderiv_eq,
      cylinder_affine_first_derivative z.2 ((hT ![a, b]).differentiableAt (by simp))]
    exact (cylinder_first_component_le N.epsilon_pos hB hz (by omega) ![a, b] i).trans
      hfour
  have hsecond' (j i a b : Fin 3) :
      |fderiv ℝ (fderiv ℝ F) 0 (cb j) (cb i) (cb a) (cb b)| ≤
        (4 + C) * N.epsilon := by
    have hder : (fun y => fderiv ℝ (fun x => F x (cb a) (cb b)) y (cb i))
        =ᶠ[𝓝 (0 : CE)] (fun y => fderiv ℝ
          (fun x => T (cylinderScalarCoordinates z.2 x) ![a, b]) y (cb i)) := by
      filter_upwards [(cylinder_error_frozen_germ N hz a b).fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : CE →L[ℝ] ℝ => L (cb i)) hy
    rw [← coefficient_second_fderiv_of_contDiffAt hF,
      hder.fderiv_eq, cylinder_affine_second_derivative z.2 (hT ![a, b]) i j]
    exact (hsecond N.epsilon N.epsilon_pos B hB z hz horder ![a, b] i j).trans hCbound
  have hn := hnorm (metricTwoJet F 0) ((4 + C) * N.epsilon)
    (mul_nonneg (by positivity) N.epsilon_pos.le) hzero hfirst hsecond'
  have hdiff : metricTwoJet F 0 =
      metricTwoJet (cylinderNeckCoefficients N z.1 z.2) 0 - cylinderModelTwoJet :=
    metricTwoJet_sub_of_smooth
      ((contDiffOn_cylinderNeckCoefficients N z.1 z.2).contDiffAt
        ((isOpen_cylinderNeckChartDomain N z.1 z.2).mem_nhds
          (zero_mem_cylinderNeckChartDomain N z.1 hz)))
      contDiff_cylinderModelMetricCoefficient.contDiffAt
  rw [dist_eq_norm, ← hdiff]
  simpa only [mul_assoc] using hn

end PoincareConjecture.M28.tube
