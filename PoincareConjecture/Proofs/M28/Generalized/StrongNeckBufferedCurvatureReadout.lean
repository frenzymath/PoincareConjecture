import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedCurvatureJets
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderJetReadout

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M28

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckAnalysis tube

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev cb := EuclideanSpace.basisFun (Fin 3) ℝ
private abbrev CMetric := MetricCoefficient 3
local instance bufferedMetricNorm : NormedAddCommGroup CMetric :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance bufferedMetricSpace : NormedSpace ℝ CMetric := ContinuousLinearMap.toNormedSpace
private abbrev CFirst := CE →L[ℝ] CMetric
local instance bufferedFirstNorm : NormedAddCommGroup CFirst :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance bufferedFirstSpace : NormedSpace ℝ CFirst := ContinuousLinearMap.toNormedSpace
private abbrev CSecond := CE →L[ℝ] CFirst
local instance bufferedSecondNorm : NormedAddCommGroup CSecond :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance bufferedSecondSpace : NormedSpace ℝ CSecond := ContinuousLinearMap.toNormedSpace

private theorem coefficient_second_evaluation
    {F : CE → MetricCoefficient 3} (hF : ContDiffAt ℝ ∞ F 0) (u v w z : CE) :
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

private theorem affine_first_derivative
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

private theorem affine_second_derivative
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
  exact affine_first_derivative s (hdf.differentiableAt (by simp)) j

theorem exists_buffered_cylinder_model_curvature_bound :
    ∃ eta : ℝ, 0 < eta ∧ ∃ K : ℝ, 0 < K ∧
      ∀ u ∈ Icc (-(3 / 4 : ℝ)) 0, ∀ J : MetricTwoJet 3,
        dist J (evolvingCylinderModelTwoJet u) < eta → jetCurvatureNorm J ≤ K := by
  let S := evolvingCylinderModelTwoJet '' Icc (-(3 / 4 : ℝ)) 0
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

theorem exists_buffered_cylinder_metricTwoJet_bound :
    ∃ L : ℝ, 0 < L ∧ ∀ (epsilon u : ℝ), 0 < epsilon →
      u ∈ Icc (-(3 / 4 : ℝ)) 0 →
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon u B →
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      2 ≤ ⌊epsilon⁻¹⌋₊ → ∀ F : CE → MetricCoefficient 3,
      ContDiffAt ℝ ∞ F 0 →
      (∀ a b : Fin 3, (fun x => F x (cb a) (cb b)) =ᶠ[𝓝 (0 : CE)]
        (fun x => roundCylinderTensorCoefficient B
          (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          (cylinderScalarCoordinates z.2 x) a b)) →
      dist (metricTwoJet F 0) (evolvingCylinderModelTwoJet u) ≤ L * epsilon := by
  obtain ⟨K, hK, hnorm⟩ := exists_metricTwoJet_coefficient_bound
  obtain ⟨C, hC, hsecond⟩ := exists_buffered_cylinder_second_component_bound
  refine ⟨K * (16 + C), mul_pos hK (by positivity), ?_⟩
  intro epsilon u hepsilon hu B hB z hz horder F hF hfrozen
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let T := roundCylinderIteratedDerivative u c B 0
  let E := fun x => F x - evolvingCylinderModelCoefficient u x
  have hE : ContDiffAt ℝ ∞ E 0 :=
    hF.sub (contDiff_evolvingCylinderModelCoefficient u).contDiffAt
  have hgerm (a b : Fin 3) : (fun x => E x (cb a) (cb b)) =ᶠ[𝓝 (0 : CE)]
      (fun x => T (cylinderScalarCoordinates z.2 x) ![a, b]) := by
    filter_upwards [hfrozen a b] with x hx
    change F x (cb a) (cb b) - evolvingCylinderModelCoefficient u x (cb a) (cb b) = _
    rw [hx, evolvingCylinderModelCoefficient_basis u z.1 z.2 x a b]
    rfl
  have hp : (0, z.2) ∈ c.target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    rw [← sphere_chart_center z.1]
    exact c.map_source (mem_chart_source _ z.1)
  have hT (a : Fin 2 → Fin 3) : ContDiffAt ℝ ∞ (fun p => T p a) (0, z.2) :=
    (contDiffOn_roundCylinderIteratedDerivative
      (lt_of_le_of_lt hu.2 (by norm_num)) hB.1 z.1 0 a).contDiffAt
        ((c.open_target.prod isOpen_Ioo).mem_nhds hp)
  have hsixteen : 16 * epsilon ≤ (16 + C) * epsilon := by nlinarith
  have hCbound : C * epsilon ≤ (16 + C) * epsilon := by nlinarith
  have hzero (a b : Fin 3) : |E 0 (cb a) (cb b)| ≤ (16 + C) * epsilon := by
    have heq : E 0 (cb a) (cb b) = T (cylinderScalarCoordinates z.2 0) ![a, b] :=
      (hgerm a b).self_of_nhds
    rw [heq, cylinderScalarCoordinates_zero]
    exact (buffered_cylinder_covariant_component_le (k := 0) hepsilon hu hB hz
      (by omega) (by omega) ![a, b]).trans hsixteen
  have hfirst (i a b : Fin 3) :
      |fderiv ℝ E 0 (cb i) (cb a) (cb b)| ≤ (16 + C) * epsilon := by
    rw [← coefficient_fderiv_evaluation (hE.differentiableAt (by simp)),
      (hgerm a b).fderiv_eq,
      affine_first_derivative z.2 ((hT ![a, b]).differentiableAt (by simp))]
    exact (buffered_cylinder_first_component_le hepsilon hu hB hz
      (by omega) ![a, b] i).trans hsixteen
  have hsecond' (j i a b : Fin 3) :
      |fderiv ℝ (fderiv ℝ E) 0 (cb j) (cb i) (cb a) (cb b)| ≤
        (16 + C) * epsilon := by
    have hder : (fun y => fderiv ℝ (fun x => E x (cb a) (cb b)) y (cb i))
        =ᶠ[𝓝 (0 : CE)] (fun y => fderiv ℝ
          (fun x => T (cylinderScalarCoordinates z.2 x) ![a, b]) y (cb i)) := by
      filter_upwards [(hgerm a b).fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : CE →L[ℝ] ℝ => L (cb i)) hy
    rw [← coefficient_second_evaluation hE,
      hder.fderiv_eq, affine_second_derivative z.2 (hT ![a, b]) i j]
    exact (hsecond epsilon u hepsilon hu B hB z hz horder ![a, b] i j).trans hCbound
  have hn := hnorm (metricTwoJet E 0) ((16 + C) * epsilon)
    (mul_nonneg (by positivity) hepsilon.le) hzero hfirst hsecond'
  have hdiff : metricTwoJet E 0 = metricTwoJet F 0 - evolvingCylinderModelTwoJet u :=
    metricTwoJet_sub_of_smooth hF (contDiff_evolvingCylinderModelCoefficient u).contDiffAt
  rw [dist_eq_norm, ← hdiff]
  simpa only [mul_assoc] using hn

theorem exists_buffered_cylinder_curvature_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ (epsilon u : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ →
        u ∈ Icc (-(3 / 4 : ℝ)) 0 →
        ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon u B →
        ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ∀ F : CE → MetricCoefficient 3, ContDiffAt ℝ ∞ F 0 →
        (∀ a b : Fin 3, (fun x => F x (cb a) (cb b)) =ᶠ[𝓝 (0 : CE)]
          (fun x => roundCylinderTensorCoefficient B
            (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
            (cylinderScalarCoordinates z.2 x) a b)) →
        jetCurvatureNorm (metricTwoJet F 0) ≤ K := by
  obtain ⟨L, hL, hjet⟩ := exists_buffered_cylinder_metricTwoJet_bound
  obtain ⟨eta, heta, K, hK, hbound⟩ := exists_buffered_cylinder_model_curvature_bound
  refine ⟨min (1 / 200) (eta / (2 * L)),
    lt_min (by norm_num) (by positivity), min_le_left _ _, K, hK, ?_⟩
  intro epsilon u hepsilon hsmall hu B hB z hz F hF hfrozen
  have heps : epsilon ≤ (1 / 200 : ℝ) := hsmall.trans (min_le_left _ _)
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ hepsilon]
    norm_num
    linarith
  have hdist : L * epsilon < eta := by
    have h := hsmall.trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).mp h
    nlinarith
  exact hbound u hu _ ((hjet epsilon u hepsilon hu B hB z hz horder F hF hfrozen).trans_lt
    hdist)

end PoincareConjecture.M28
