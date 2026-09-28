import PoincareConjecture.Proofs.M36.CylinderModelField
import PoincareConjecture.Proofs.M36.JetCurvatureBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem metricTwoJet_sub_of_contDiffAt
    {F G : E₃ → MetricCoefficient 3} {x : E₃}
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G x) :
    metricTwoJet (fun p => F p - G p) x = metricTwoJet F x - metricTwoJet G x := by
  have hd : fderiv ℝ (fun p => F p - G p) =ᶠ[𝓝 x]
      (fun p => fderiv ℝ F p - fderiv ℝ G p) := by
    filter_upwards [(hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp),
      (hG.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with p hpF hpG
    exact fderiv_fun_sub (hpF.differentiableAt (by simp)) (hpG.differentiableAt (by simp))
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact fderiv_fun_sub (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))
  change fderiv ℝ (fderiv ℝ (fun p => F p - G p)) x =
    fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x
  rw [hd.fderiv_eq]
  exact fderiv_fun_sub
    ((hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))

noncomputable def cylinderModelJet : MetricTwoJet 3 := metricTwoJet cylinderModelField 0

theorem cylinderModelJet_isInvertible : cylinderModelJet.1.IsInvertible := by
  apply CoordinateTransition.isInvertible_of_uniformEllipticity (a := 1) zero_lt_one
  intro v
  simpa only [cylinderModelJet, metricTwoJet, one_mul] using cylinderModelField_zero_lower v

theorem jetChristoffel_cylinderModelJet (u v : E₃) :
    jetChristoffel cylinderModelJet u v = 0 := by
  simp [jetChristoffel, cylinderModelJet, metricTwoJet,
    cylinderModelField_fderiv_zero, metricKoszulCovector]

theorem jetCurvature_cylinderModelJet (u w v z : E₃) :
    jetCurvature cylinderModelJet u w v z =
      2 * (cylinderHorizontalForm u v * cylinderHorizontalForm w z -
        cylinderHorizontalForm u z * cylinderHorizontalForm w v) := by
  unfold jetCurvature
  simp only [jetChristoffel_cylinderModelJet]
  change (2⁻¹ : ℝ) *
      (fderiv ℝ (fderiv ℝ cylinderModelField) 0 u z w v -
        fderiv ℝ (fderiv ℝ cylinderModelField) 0 u v w z -
        fderiv ℝ (fderiv ℝ cylinderModelField) 0 w z u v +
        fderiv ℝ (fderiv ℝ cylinderModelField) 0 w v u z) + _ = _
  simp only [cylinderModelField_second_fderiv_zero, cylinderModelJet, metricTwoJet,
    cylinderModelField_fderiv_zero, zero_apply, map_zero, neg_zero, add_zero,
    sub_zero]
  ring

theorem roundCylinderClose_twoJet_error {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ‖metricTwoJet (centeredCylinderMetric B z.1 z.2) 0 - cylinderModelJet‖ ≤
      810 * epsilon := by
  have hF := centeredCylinderMetric_contDiffAt hB z hz
  rw [cylinderModelJet, ← metricTwoJet_sub_of_contDiffAt hF
    cylinderModelField_contDiff.contDiffAt, centeredCylinderMetric_sub_model]
  obtain ⟨h0, h1, h2⟩ := roundCylinderClose_error_operator_bounds hepsilon hB horder z hz
  simp only [metricTwoJet, Prod.norm_def]
  exact max_le (by linarith) (max_le (by linarith) h2)

theorem exists_roundCylinderClose_jetCurvature_bounds :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : ℝ, 0 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ B : RoundCylinderTwoTensor, RoundCylinderClose epsilon 0 B →
      2 ≤ ⌊epsilon⁻¹⌋₊ →
      ∀ z : RoundCylinderSpace, z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
        (∀ i j k l : Fin 3,
          |jetCurvature (metricTwoJet (centeredCylinderMetric B z.1 z.2) 0)
              (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)
              (EuclideanSpace.basisFun (Fin 3) ℝ k)
              (EuclideanSpace.basisFun (Fin 3) ℝ l) -
            jetCurvature cylinderModelJet (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)
              (EuclideanSpace.basisFun (Fin 3) ℝ k)
              (EuclideanSpace.basisFun (Fin 3) ℝ l)| ≤ K * epsilon) ∧
        (∀ i j : Fin 3,
          ‖jetChristoffel (metricTwoJet (centeredCylinderMetric B z.1 z.2) 0)
              (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)‖ ≤ K * epsilon) := by
  obtain ⟨r, hr, K, hK, hb⟩ := exists_jetCurvature_component_bounds
    cylinderModelJet cylinderModelJet_isInvertible
  refine ⟨r / 1620, by positivity, 810 * K, by positivity, ?_⟩
  intro epsilon hepsilon hsmall B hB horder z hz
  have hj := roundCylinderClose_twoJet_error hepsilon hB horder z hz
  have hnear : ‖metricTwoJet (centeredCylinderMetric B z.1 z.2) 0 - cylinderModelJet‖ < r := by
    have he : 810 * epsilon ≤ r / 2 := by linarith
    exact hj.trans_lt (he.trans_lt (by linarith))
  obtain ⟨hc, hconn⟩ := hb _ hnear
  have hscale : K * ‖metricTwoJet (centeredCylinderMetric B z.1 z.2) 0 -
      cylinderModelJet‖ ≤ (810 * K) * epsilon := by
    calc
      _ ≤ K * (810 * epsilon) := mul_le_mul_of_nonneg_left hj hK.le
      _ = _ := by ring
  constructor
  · intro i j k l
    exact (hc i j k l).trans hscale
  · intro i j
    simpa only [jetChristoffel_cylinderModelJet, sub_zero] using
      (hconn i j).trans hscale

end PoincareConjecture.M36
