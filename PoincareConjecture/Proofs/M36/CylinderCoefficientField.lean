import PoincareConjecture.Proofs.M36.CylinderCoordinateJets
import PoincareConjecture.Proofs.M36.CylinderEuclidean
import Mathlib.Analysis.Calculus.FDeriv.CompCLM









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "C" => RoundCylinderCoordinates

noncomputable def centeredCylinderBilinear
    (c : C → Fin 3 → Fin 3 → ℝ) (s : ℝ) (p : E₃) : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  ∑ i, ∑ j, c (cylinderEuclideanEquiv p + (0, s)) i j •
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)).smulRight
      (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ j))

theorem centeredCylinderBilinear_basis
    (c : C → Fin 3 → Fin 3 → ℝ) (s : ℝ) (p : E₃) (i j : Fin 3) :
    centeredCylinderBilinear c s p (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        c (cylinderEuclideanEquiv p + (0, s)) i j := by
  classical
  simp only [centeredCylinderBilinear, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul,
    (EuclideanSpace.basisFun (Fin 3) ℝ).inner_eq_ite]
  simp

theorem centeredCylinderBilinear_contDiffAt
    (c : C → Fin 3 → Fin 3 → ℝ) (s : ℝ)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun p => c p i j) (0, s)) :
    ContDiffAt ℝ ∞ (centeredCylinderBilinear c s) 0 := by
  unfold centeredCylinderBilinear
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have ha : ContDiffAt ℝ ∞ (fun p : E₃ => cylinderEuclideanEquiv p + (0, s)) 0 :=
    cylinderEuclideanEquiv.contDiff.contDiffAt.add contDiffAt_const
  have hcomp : ContDiffAt ℝ ∞
      (fun p : E₃ => c (cylinderEuclideanEquiv p + (0, s)) i j) 0 := by
    have hc' : ContDiffAt ℝ ∞ (fun p => c p i j)
        (cylinderEuclideanEquiv 0 + (0, s)) := by
      simpa only [map_zero, zero_add] using hc i j
    exact hc'.comp 0 ha
  exact hcomp.smul contDiffAt_const

theorem fderiv_bilinear_component
    {F : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ} {x : E₃}
    (hF : DifferentiableAt ℝ F x) (v a b : E₃) :
    fderiv ℝ (fun y => F y a b) x v = fderiv ℝ F x v a b := by
  rw [fderiv_clm_apply (hF.clm_apply (differentiableAt_const a)) (differentiableAt_const b),
    fderiv_clm_apply hF (differentiableAt_const a)]
  simp

theorem second_fderiv_bilinear_component
    {F : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ} {x : E₃}
    (hF : ContDiffAt ℝ ∞ F x) (w v a b : E₃) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => F z a b) y v) x w =
      fderiv ℝ (fderiv ℝ F) x w v a b := by
  have he : (fun y => fderiv ℝ (fun z => F z a b) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y v a b) := by
    filter_upwards [(hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with y hy
    exact fderiv_bilinear_component (hy.differentiableAt (by simp)) v a b
  rw [he.fderiv_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply
      ((hd.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const a))
      (differentiableAt_const b),
    fderiv_clm_apply (hd.clm_apply (differentiableAt_const v)) (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simp

noncomputable def centeredCylinderError
    (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (s : ℝ) :
    E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  centeredCylinderBilinear (fun p i j =>
    roundCylinderTensorCoefficient B (chartAt E₂ theta) p i j -
      roundCylinderGram 0 (chartAt E₂ theta) p i j) s

theorem centeredCylinderError_contDiffAt {epsilon : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContDiffAt ℝ ∞ (centeredCylinderError B z.1 z.2) 0 := by
  apply centeredCylinderBilinear_contDiffAt
  intro i j
  exact roundCylinder_metric_error_contDiffAt hB z hz ![i, j]

theorem roundCylinderClose_error_operator_bounds {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ‖centeredCylinderError B z.1 z.2 0‖ ≤ 18 * epsilon ∧
      ‖fderiv ℝ (centeredCylinderError B z.1 z.2) 0‖ ≤ 81 * epsilon ∧
      ‖fderiv ℝ (fderiv ℝ (centeredCylinderError B z.1 z.2)) 0‖ ≤ 810 * epsilon := by
  let F := centeredCylinderError B z.1 z.2
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have hF : ContDiffAt ℝ ∞ F 0 := centeredCylinderError_contDiffAt hB z hz
  have h0 (i j : Fin 3) : ‖F 0 (e i) (e j)‖ ≤ 2 * epsilon := by
    have h := roundCylinderClose_coefficient_error hepsilon hB z hz i j
    rw [sphere_chart_center_zero] at h
    simpa only [F, e, centeredCylinderError, centeredCylinderBilinear_basis,
      map_zero, zero_add, Real.norm_eq_abs] using h
  have h1 (i a b : Fin 3) : ‖fderiv ℝ F 0 (e i) (e a) (e b)‖ ≤ 3 * epsilon := by
    rw [← fderiv_bilinear_component (hF.differentiableAt (by simp))]
    simp only [F, e, centeredCylinderError, centeredCylinderBilinear_basis]
    rw [fderiv_cylinder_affine (fun p =>
        roundCylinderTensorCoefficient B (chartAt E₂ z.1) p a b -
          roundCylinderGram 0 (chartAt E₂ z.1) p a b),
      map_zero, zero_add, cylinderEuclideanEquiv_basis,
      Real.norm_eq_abs]
    exact roundCylinderClose_first_coordinate_error hepsilon.le hB
      (le_trans (by omega) horder) z hz i a b
  have h2 (k i a b : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ F) 0 (e k) (e i) (e a) (e b)‖ ≤ 10 * epsilon := by
    rw [← second_fderiv_bilinear_component hF]
    simp only [F, e, centeredCylinderError, centeredCylinderBilinear_basis]
    rw [second_fderiv_cylinder_affine (fun p =>
        roundCylinderTensorCoefficient B (chartAt E₂ z.1) p a b -
          roundCylinderGram 0 (chartAt E₂ z.1) p a b), map_zero, zero_add,
      cylinderEuclideanEquiv_basis, cylinderEuclideanEquiv_basis, Real.norm_eq_abs]
    exact roundCylinderClose_second_coordinate_error hepsilon.le hB horder z hz k i a b
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖F 0‖ ≤ 9 * (2 * epsilon) := euclideanThree_bilinear_norm_le _ (by positivity) h0
      _ = 18 * epsilon := by ring
  · calc
      ‖fderiv ℝ F 0‖ ≤ 27 * (3 * epsilon) :=
        euclideanThree_trilinear_norm_le _ (by positivity) h1
      _ = 81 * epsilon := by ring
  · calc
      ‖fderiv ℝ (fderiv ℝ F) 0‖ ≤ 81 * (10 * epsilon) :=
        euclideanThree_quadrilinear_norm_le _ (by positivity) h2
      _ = 810 * epsilon := by ring

end PoincareConjecture.M36
