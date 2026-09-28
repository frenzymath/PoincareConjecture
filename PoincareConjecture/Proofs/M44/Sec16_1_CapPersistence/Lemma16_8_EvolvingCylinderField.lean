import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderTimeComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

noncomputable local instance evolvingCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance evolvingCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance evolvingTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance evolvingTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace



noncomputable def evolvingCylinderModelField (t : ℝ) (x : E) : MetricCoefficient 3 :=
  (1 - t) • cylinderModelField x +
    t • cylinderHeightCovector.smulRight cylinderHeightCovector



theorem evolvingCylinderModelField_contDiff (t : ℝ) :
    ContDiff ℝ ∞ (evolvingCylinderModelField t) := by
  have h : ContDiff ℝ ∞ (fun x : E => (1 - t) • cylinderModelField x) :=
    cylinderModelField_contDiff.const_smul (1 - t)
  exact h.add contDiff_const



theorem centeredCylinderBilinear_evolving_gram (t : ℝ) (theta : UnitTwoSphere) (s : ℝ) :
    centeredCylinderBilinear (roundCylinderGram t (chartAt E₂ theta)) s =
      evolvingCylinderModelField t := by
  funext p
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderBilinear_basis, evolving_roundCylinderGram_entry]
  simp only [evolvingCylinderModelField, cylinderModelField, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, cylinderHorizontalForm_basis,
    cylinderHeightCovector_basis]
  simp only [cylinderSphereFactor, Prod.fst_add, add_zero]
  ring



theorem evolvingCylinderModelField_fderiv (t : ℝ) (x : E) :
    fderiv ℝ (evolvingCylinderModelField t) x =
      (1 - t) • fderiv ℝ cylinderModelField x := by
  exact (((cylinderModelField_contDiff.differentiable (by simp) x).hasFDerivAt.const_smul
    (1 - t)).add_const (t • cylinderHeightCovector.smulRight cylinderHeightCovector)).fderiv



theorem evolvingCylinderModelField_second_fderiv (t : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (evolvingCylinderModelField t)) x =
      (1 - t) • fderiv ℝ (fderiv ℝ cylinderModelField) x := by
  have heq : fderiv ℝ (evolvingCylinderModelField t) =
      fun y => (1 - t) • fderiv ℝ cylinderModelField y :=
    funext (evolvingCylinderModelField_fderiv t)
  rw [heq]
  exact (((cylinderModelField_contDiff.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) x).hasFDerivAt.const_smul (1 - t)).fderiv



noncomputable def evolvingCylinderModelJet (t : ℝ) : MetricTwoJet 3 :=
  metricTwoJet (evolvingCylinderModelField t) 0



theorem evolvingCylinderModelJet_eq (t : ℝ) :
    evolvingCylinderModelJet t = (1 - t) • cylinderModelJet +
      (t • cylinderHeightCovector.smulRight cylinderHeightCovector, 0, 0) := by
  simp only [evolvingCylinderModelJet, cylinderModelJet, metricTwoJet,
    evolvingCylinderModelField_fderiv, evolvingCylinderModelField_second_fderiv]
  simp only [evolvingCylinderModelField, Prod.smul_mk, Prod.mk_add_mk, add_zero]



theorem continuous_evolvingCylinderModelJet : Continuous evolvingCylinderModelJet := by
  rw [show evolvingCylinderModelJet = fun t : ℝ => (1 - t) • cylinderModelJet +
      (t • cylinderHeightCovector.smulRight cylinderHeightCovector, 0, 0) from
    funext evolvingCylinderModelJet_eq]
  fun_prop



theorem staticCylinderCorrection_centered_error (t : ℝ) (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (s : ℝ) :
    (fun p => centeredCylinderMetric (staticCylinderCorrection t B) theta s p -
      cylinderModelField p) =
        fun p => centeredCylinderMetric B theta s p - evolvingCylinderModelField t p := by
  rw [← centeredCylinderBilinear_gram theta s, ← centeredCylinderBilinear_evolving_gram t theta s]
  funext p
  apply euclideanThree_bilinear_ext
  intro i j
  simp only [centeredCylinderMetric, sub_apply, centeredCylinderBilinear_basis,
    staticCylinderCorrection_coefficient]
  ring




theorem evolving_centeredCylinderMetric_contDiffAt {epsilon t : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon t B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContDiffAt ℝ ∞ (centeredCylinderMetric B z.1 z.2) 0 := by
  apply centeredCylinderBilinear_contDiffAt
  intro i j
  have hzero : (0 : E₂) ∈ (chartAt E₂ z.1).target := by
    rw [← sphere_chart_center_zero z.1]
    exact (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  exact (hB.1 z.1 i j).contDiffAt
    (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds ⟨hzero, hz⟩)




theorem evolving_roundCylinderClose_twoJet_error {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (ht0 : 0 ≤ t) (ht : t < 1)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon t B)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ‖metricTwoJet (centeredCylinderMetric B z.1 z.2) 0 - evolvingCylinderModelJet t‖ ≤
      810 * epsilon := by
  have hflat := staticCylinderCorrection_close ht0 ht hB
  have h := roundCylinderClose_twoJet_error hepsilon hflat horder z hz
  rw [cylinderModelJet, ← metricTwoJet_sub_of_contDiffAt
    (centeredCylinderMetric_contDiffAt hflat z hz) cylinderModelField_contDiff.contDiffAt,
    staticCylinderCorrection_centered_error, metricTwoJet_sub_of_contDiffAt
      (evolving_centeredCylinderMetric_contDiffAt hB z hz)
      (evolvingCylinderModelField_contDiff t).contDiffAt] at h
  exact h

end PoincareConjecture.M44
