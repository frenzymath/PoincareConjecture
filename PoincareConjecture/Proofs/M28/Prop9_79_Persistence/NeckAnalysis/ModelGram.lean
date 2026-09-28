import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.SphereMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

theorem contDiff_sphereChartConformalFactor :
    ContDiff ℝ ∞ sphereChartConformalFactor := by
  unfold sphereChartConformalFactor
  exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
    (fun _ => by positivity)

theorem hasFDerivAt_sphereChartConformalFactor (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt sphereChartConformalFactor
      ((-64 / (‖x‖ ^ 2 + 4) ^ 3) • innerSL ℝ x) x := by
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hsq : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ x) x := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasFDerivAt_inv hd).comp x (hsq.add_const 4)
  convert! (hi.pow 2).const_mul (16 : ℝ) using 1
  · funext y
    simp [sphereChartConformalFactor, div_eq_mul_inv, inv_pow]
  · ext h
    simp [innerSL_apply_apply, nsmul_eq_mul]
    field_simp [hd]
    ring

theorem fderiv_sphereChartConformalFactor_fst (p h : RoundCylinderCoordinates) :
    fderiv ℝ (fun y : RoundCylinderCoordinates => sphereChartConformalFactor y.1) p h =
      (-64 / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 h.1 := by
  have hh := ((hasFDerivAt_sphereChartConformalFactor p.1).comp p
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).hasFDerivAt).fderiv
  exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ => L h) hh

theorem roundCylinderGram_inverse_chosen_chart {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ =
      Matrix.diagonal ![(2 * (1-u) * sphereChartConformalFactor p.1)⁻¹,
        (2 * (1-u) * sphereChartConformalFactor p.1)⁻¹, 1] := by
  rw [roundCylinderGram_chosen_chart]
  have hnonzero : 2 * (1-u) * sphereChartConformalFactor p.1 ≠ 0 := by
    have hpos := sphereChartConformalFactor_pos p.1
    positivity
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    fin_cases a
    · change (2 * (1-u) * sphereChartConformalFactor p.1) *
        (2 * (1-u) * sphereChartConformalFactor p.1)⁻¹ = 1
      exact mul_inv_cancel₀ hnonzero
    · change (2 * (1-u) * sphereChartConformalFactor p.1) *
        (2 * (1-u) * sphereChartConformalFactor p.1)⁻¹ = 1
      exact mul_inv_cancel₀ hnonzero
    · norm_num [Matrix.diagonal]
  · simp [Matrix.diagonal, hab]

theorem fderiv_roundCylinderGram_chosen_chart (u : ℝ) (q : UnitTwoSphere)
    (p h : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fun y => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) p h =
      if a = b ∧ a ≠ 2 then
        (-128 * (1-u) / (‖p.1‖ ^ 2 + 4) ^ 3) * inner ℝ p.1 h.1
      else 0 := by
  have hd : DifferentiableAt ℝ
      (fun y : RoundCylinderCoordinates => sphereChartConformalFactor y.1) p :=
    (contDiff_sphereChartConformalFactor.comp contDiff_fst).contDiffAt.differentiableAt (by simp)
  simp_rw [roundCylinderGram_chosen_chart]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.diagonal, fderiv_const_mul hd, fderiv_sphereChartConformalFactor_fst] <;>
    ring

end PoincareConjecture.Proofs.M28.NeckAnalysis
