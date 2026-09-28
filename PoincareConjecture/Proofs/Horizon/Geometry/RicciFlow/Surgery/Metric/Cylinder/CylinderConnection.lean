import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderChartMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.MetricSurgery

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "C" => RoundCylinderCoordinates

noncomputable def cylinderSphereFactor (p : C) : ℝ := 32 / (‖p.1‖ ^ 2 + 4) ^ 2

noncomputable def cylinderHorizontalCovector (i : Fin 3) : C →L[ℝ] ℝ :=
  (innerSL ℝ (roundCylinderCoordinateBasis i).1).comp (ContinuousLinearMap.fst ℝ E₂ ℝ)

noncomputable def cylinderHorizontalGram (i j : Fin 3) : ℝ :=
  inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1

theorem cylinderSphereFactor_hasFDerivAt (p : C) :
    HasFDerivAt cylinderSphereFactor
      ((-128 / (‖p.1‖ ^ 2 + 4) ^ 3) •
        (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ E₂ ℝ)) p := by
  have hn := (hasStrictFDerivAt_norm_sq p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hne : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hi := (hasFDerivAt_inv (pow_ne_zero 2 hne)).comp p ((hn.add_const 4).pow 2)
  have hd := hi.const_smul (32 : ℝ)
  have hfun : cylinderSphereFactor =
      (32 : ℝ) • ((fun x : ℝ => x⁻¹) ∘
        fun q : C => (‖q.1‖ ^ 2 + 4) ^ 2) := by
    funext q
    simp [cylinderSphereFactor, div_eq_mul_inv]
  rw [hfun]
  refine hd.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
  field_simp
  ring

theorem cylinderSphereFactor_contDiff : ContDiff ℝ ∞ cylinderSphereFactor := by
  apply contDiff_const.div
    ((((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const).pow 2)
  intro p
  exact pow_ne_zero 2 (ne_of_gt (show 0 < ‖p.1‖ ^ 2 + 4 by positivity))

theorem roundCylinderGram_chart_entry (theta : UnitTwoSphere) (p : C) (i j : Fin 3) :
    roundCylinderGram 0 (chartAt E₂ theta) p i j =
      cylinderSphereFactor p * cylinderHorizontalGram i j +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 := by
  rw [roundCylinderGram_chart]
  fin_cases i <;> fin_cases j <;>
    simp [cylinderSphereFactor, cylinderHorizontalGram, roundCylinderCoordinateBasis,
      Matrix.diagonal, EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]

theorem roundCylinderGram_chart_fderiv (theta : UnitTwoSphere) (p v : C) (i j : Fin 3) :
    fderiv ℝ (fun q => roundCylinderGram 0 (chartAt E₂ theta) q i j) p v =
      (-128 / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 v.1 * cylinderHorizontalGram i j := by
  have heq : (fun q => roundCylinderGram 0 (chartAt E₂ theta) q i j) =
      fun q => cylinderSphereFactor q * cylinderHorizontalGram i j +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 :=
    funext (fun q => roundCylinderGram_chart_entry theta q i j)
  have hd := ((cylinderSphereFactor_hasFDerivAt p).mul_const
    (cylinderHorizontalGram i j)).add_const
      ((roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2)
  rw [heq]
  simpa [mul_comm, mul_left_comm] using congrArg (fun L : C →L[ℝ] ℝ => L v) hd.fderiv

theorem roundCylinderGram_chart_contDiff (theta : UnitTwoSphere) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p => roundCylinderGram 0 (chartAt E₂ theta) p i j) := by
  simp only [roundCylinderGram_chart_entry]
  exact (cylinderSphereFactor_contDiff.mul contDiff_const).add contDiff_const

theorem roundCylinderGram_chart_inv (theta : UnitTwoSphere) (p : C) :
    (roundCylinderGram 0 (chartAt E₂ theta) p)⁻¹ =
      Matrix.diagonal ![(cylinderSphereFactor p)⁻¹, (cylinderSphereFactor p)⁻¹, 1] := by
  apply Matrix.inv_eq_left_inv
  rw [roundCylinderGram_chart, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, cylinderSphereFactor, ne_of_gt
      (show 0 < ‖p.1‖ ^ 2 + 4 by positivity)]

noncomputable def cylinderChristoffelLinear (a b d : Fin 3) : C →L[ℝ] ℝ :=
  cylinderHorizontalGram d a • cylinderHorizontalCovector b +
    cylinderHorizontalGram b a • cylinderHorizontalCovector d -
    cylinderHorizontalGram b d • cylinderHorizontalCovector a

theorem roundCylinderChristoffel_chart (theta : UnitTwoSphere) (p : C) (a b d : Fin 3) :
    roundCylinderChristoffel 0 (chartAt E₂ theta) p a b d =
      (-2 / (‖p.1‖ ^ 2 + 4)) * cylinderChristoffelLinear a b d p := by
  have hne : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  unfold roundCylinderChristoffel
  simp only [roundCylinderGram_chart_inv, roundCylinderGram_chart_fderiv]
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [Matrix.diagonal, cylinderSphereFactor,
      cylinderChristoffelLinear, cylinderHorizontalCovector, cylinderHorizontalGram,
      roundCylinderCoordinateBasis, EuclideanSpace.basisFun,
      real_inner_comm] <;>
    field_simp <;> ring

theorem roundCylinderChristoffel_center (theta : UnitTwoSphere) (s : ℝ) (a b d : Fin 3) :
    roundCylinderChristoffel 0 (chartAt E₂ theta) (0, s) a b d = 0 := by
  rw [roundCylinderChristoffel_chart]
  simp [cylinderChristoffelLinear, cylinderHorizontalCovector]

theorem roundCylinderChristoffel_chart_contDiff (theta : UnitTwoSphere) (a b d : Fin 3) :
    ContDiff ℝ ∞ (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p a b d) := by
  simp only [roundCylinderChristoffel_chart]
  exact (contDiff_const.div
    (((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const)
    (fun p => ne_of_gt (show 0 < ‖p.1‖ ^ 2 + 4 by positivity))).mul
      (cylinderChristoffelLinear a b d).contDiff

theorem roundCylinderChristoffel_center_fderiv (theta : UnitTwoSphere) (s : ℝ)
    (a b d : Fin 3) (v : C) :
    fderiv ℝ (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p a b d) (0, s) v =
      (-1 / 2 : ℝ) * cylinderChristoffelLinear a b d v := by
  let F : C → ℝ := fun p => -2 / (‖p.1‖ ^ 2 + 4)
  have hF : DifferentiableAt ℝ F (0, s) := by
    have hden : ContDiff ℝ ∞ (fun p : C => ‖p.1‖ ^ 2 + 4) :=
      ((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const
    have hfull : ContDiff ℝ ∞ F := contDiff_const.div hden
      (fun p => ne_of_gt (show 0 < ‖p.1‖ ^ 2 + 4 by positivity))
    exact hfull.differentiable (by simp) _
  have hzero : cylinderChristoffelLinear a b d (0, s) = 0 := by
    simp [cylinderChristoffelLinear, cylinderHorizontalCovector]
  have hd := hF.hasFDerivAt.mul (cylinderChristoffelLinear a b d).hasFDerivAt
  have heq : (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p a b d) =
      fun p => F p * cylinderChristoffelLinear a b d p :=
    funext (fun p => roundCylinderChristoffel_chart theta p a b d)
  rw [heq]
  simpa [Pi.mul_def, F, hzero, show (-2 / 4 : ℝ) = -1 / 2 by norm_num] using
    congrArg (fun L : C →L[ℝ] ℝ => L v) hd.fderiv

theorem roundCylinderChristoffel_center_derivative_bound (theta : UnitTwoSphere) (s : ℝ)
    (a b d k : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderChristoffel 0 (chartAt E₂ theta) p a b d)
      (0, s) (roundCylinderCoordinateBasis k)| ≤ 1 / 2 := by
  rw [roundCylinderChristoffel_center_fderiv]
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases k <;>
    norm_num [cylinderChristoffelLinear, cylinderHorizontalCovector, cylinderHorizontalGram,
      roundCylinderCoordinateBasis, EuclideanSpace.basisFun,
      EuclideanSpace.inner_single_left]

end PoincareConjecture.MetricSurgery
