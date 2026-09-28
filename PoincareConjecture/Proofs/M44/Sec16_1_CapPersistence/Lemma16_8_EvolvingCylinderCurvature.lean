import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderField
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CollarJetMargin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance cylinderCurvatureCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderCurvatureCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance cylinderCurvatureTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance cylinderCurvatureTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem evolvingCylinderModelField_zero (t : ℝ) :
    evolvingCylinderModelField t 0 = (2 * (1 - t)) • cylinderHorizontalForm +
      cylinderHeightCovector.smulRight cylinderHeightCovector := by
  rw [evolvingCylinderModelField, cylinderModelField_zero]
  module

theorem evolvingCylinderModelJet_isInvertible {t : ℝ} (ht : t < 1) :
    (evolvingCylinderModelJet t).1.IsInvertible := by
  have ha : 0 < min (2 * (1 - t)) 1 := lt_min (by linarith) zero_lt_one
  apply CoordinateTransition.isInvertible_of_uniformEllipticity ha
  intro v
  have hsplit := congrArg (fun A : MetricCoefficient 3 => A v v)
    cylinderHorizontalForm_add_vertical
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hV : 0 ≤ cylinderHeightCovector v * cylinderHeightCovector v := mul_self_nonneg _
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (2 * (1 - t)) 1) hH
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (2 * (1 - t)) 1) hV
  change min (2 * (1 - t)) 1 * ‖v‖ ^ 2 ≤ evolvingCylinderModelField t 0 v v
  rw [evolvingCylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [← hsplit, mul_add]
  exact add_le_add h1 (by simpa only [one_mul] using h2)

theorem jetChristoffel_evolvingCylinderModelJet (t : ℝ) (u v : E) :
    jetChristoffel (evolvingCylinderModelJet t) u v = 0 := by
  simp [jetChristoffel, evolvingCylinderModelJet, metricTwoJet,
    evolvingCylinderModelField_fderiv, cylinderModelField_fderiv_zero, metricKoszulCovector]

theorem jetCurvature_evolvingCylinderModelJet (t : ℝ) (u w v z : E) :
    jetCurvature (evolvingCylinderModelJet t) u w v z =
      2 * (1 - t) * (cylinderHorizontalForm u v * cylinderHorizontalForm w z -
        cylinderHorizontalForm u z * cylinderHorizontalForm w v) := by
  unfold jetCurvature
  simp only [jetChristoffel_evolvingCylinderModelJet]
  simp only [evolvingCylinderModelJet, metricTwoJet,
    evolvingCylinderModelField_second_fderiv, evolvingCylinderModelField_fderiv,
    cylinderModelField_fderiv_zero, zero_apply, map_zero, neg_zero, add_zero,
    sub_zero, smul_apply, smul_zero, smul_eq_mul, cylinderModelField_second_fderiv_zero]
  ring

theorem evolvingCylinderModelJet_inverse_proj {t : ℝ} (ht : t < 1) (i : Fin 3) :
    (evolvingCylinderModelJet t).1.inverse (EuclideanSpace.proj i) =
      evolvingCylinderInverseWeight t i • e i := by
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have heq : (evolvingCylinderModelJet t).1
      (evolvingCylinderInverseWeight t i • e i) = EuclideanSpace.proj i := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro j
    change evolvingCylinderModelField t 0 (evolvingCylinderInverseWeight t i • e i) (e j) = _
    rw [evolvingCylinderModelField_zero]
    simp only [map_smul, smul_apply, add_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, cylinderHorizontalForm_basis, cylinderHeightCovector_basis]
    fin_cases i <;> fin_cases j <;>
      simp [evolvingCylinderInverseWeight, cylinderHorizontalGram,
        roundCylinderCoordinateBasis,
        EuclideanSpace.inner_single_left, PiLp.proj_apply, htime, mul_assoc]
  rw [← heq, (evolvingCylinderModelJet_isInvertible ht).inverse_apply_self]

theorem jetScalarCurvature_evolvingCylinderModelJet {t : ℝ} (ht : t < 1) :
    jetScalarCurvature (evolvingCylinderModelJet t) = (1 - t)⁻¹ := by
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  unfold jetScalarCurvature jetRicci
  simp only [evolvingCylinderModelJet_inverse_proj ht,
    jetCurvature_evolvingCylinderModelJet, cylinderHorizontalForm_basis]
  simp [Fin.sum_univ_succ, evolvingCylinderInverseWeight, cylinderHorizontalGram,
    roundCylinderCoordinateBasis,
    EuclideanSpace.inner_single_left, PiLp.proj_apply]
  field_simp [htime]
  ring

theorem evolvingCylinderModelJet_collarGram (t : ℝ) :
    collarJetGram (e 0) (e 2) (evolvingCylinderModelJet t) = 2 * (1 - t) := by
  unfold collarJetGram
  change evolvingCylinderModelField t 0 (e 0) (e 0) *
      evolvingCylinderModelField t 0 (e 2) (e 2) -
        (evolvingCylinderModelField t 0 (e 0) (e 2)) ^ 2 = _
  rw [evolvingCylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    cylinderHorizontalForm_basis, cylinderHeightCovector_basis]
  simp [cylinderHorizontalGram, roundCylinderCoordinateBasis]

theorem evolvingCylinderModelJet_mem_collarRegion {C t : ℝ} (hC : 0 < C) (ht : t < 1) :
    evolvingCylinderModelJet t ∈ collarJetRegion C (e 0) (e 2) := by
  refine ⟨evolvingCylinderModelJet_isInvertible ht, ?_, ?_⟩
  · rw [evolvingCylinderModelJet_collarGram]
    positivity
  · unfold collarJetMargin
    rw [jetScalarCurvature_evolvingCylinderModelJet ht, jetCurvature_evolvingCylinderModelJet]
    have hzero : cylinderHorizontalForm (e 2) (e 2) = 0 := by
      rw [cylinderHorizontalForm_basis]
      simp [cylinderHorizontalGram, roundCylinderCoordinateBasis]
    have hmixed : cylinderHorizontalForm (e 0) (e 2) = 0 := by
      rw [cylinderHorizontalForm_basis]
      simp [cylinderHorizontalGram, roundCylinderCoordinateBasis]
    rw [hzero, hmixed, mul_zero, zero_mul, sub_self, mul_zero, zero_div, sub_zero]
    exact mul_pos (inv_pos.mpr hC) (inv_pos.mpr (sub_pos.mpr ht))

theorem exists_evolvingCylinder_collar_tolerance {C theta : ℝ}
    (hC : 0 < C) (htheta : theta < 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Icc (0 : ℝ) theta, ∀ J : MetricTwoJet 3,
      ‖J - evolvingCylinderModelJet t‖ ≤ delta → J ∈ collarJetRegion C (e 0) (e 2) := by
  obtain ⟨delta, hdelta, hmargin⟩ := exists_uniform_collar_jet_margin C (e 0) (e 2)
    (isCompact_Icc.image continuous_evolvingCylinderModelJet)
    (by
      rintro J ⟨t, ht, rfl⟩
      exact evolvingCylinderModelJet_mem_collarRegion hC (ht.2.trans_lt htheta))
  exact ⟨delta, hdelta, fun t ht J hnear => hmargin _ ⟨t, ht, rfl⟩ J hnear⟩

end PoincareConjecture.M44
