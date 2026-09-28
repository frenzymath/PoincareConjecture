import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_ActualPositiveAction
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}



theorem pathInitialSquareKinetic_nonneg (p : M14BackwardPath G T 0 tau x y) (s : ℝ) :
    0 ≤ M14.pathSquareKinetic p s := by
  dsimp only [M14.pathSquareKinetic]
  by_cases hv : (2 * s) • p.horizontal_velocity (s ^ 2) = 0
  · simp only [hv, map_zero, le_refl]
  · exact (G.spacetime.horizontalMetric.pos _ _ hv).le




theorem pathSquareKinetic_integral_le_positiveAction
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (p : M14BackwardPath G T 0 tau x y) :
    (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤
      2 * ∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t := by
  let density := fun t => Real.sqrt t * pathPositiveDensity p t
  have hsqrt : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg tau
  have hderiv : ∀ s ∈ uIoo 0 (Real.sqrt tau), 0 ≤ 2 * s := by
    intro s hs
    rw [uIoo_of_le hsqrt] at hs
    exact mul_nonneg (by norm_num) hs.1.le
  have htrans : IntervalIntegrable (fun s => density (s ^ 2) * (2 * s))
      volume 0 (Real.sqrt tau) := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s) (g := density)
      (continuous_id.pow 2).continuousOn
      (fun s _ => by simpa using hasDerivAt_pow 2 s) hderiv).mpr
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), Real.sq_sqrt p.tau_lt.le, density] using
      pathPositiveAction_integrable hM12 p
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.sqrt tau)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s) (g := density)
    (continuous_id.pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s) hderiv
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), Real.sq_sqrt p.tau_lt.le,
    Function.comp_def] at hchange
  have hk : IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau) := by
    change IntervalIntegrable (fun s => G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
      ((2 * s) • p.horizontal_velocity (s ^ 2)) ((2 * s) • p.horizontal_velocity (s ^ 2)))
      volume 0 (Real.sqrt tau)
    simpa only [Real.sqrt_zero] using M14.squarePath_kinetic_intervalIntegrable p hM12
  have hpoint : ∀ s ∈ Icc 0 (Real.sqrt tau),
      (1 / 2 : ℝ) * M14.pathSquareKinetic p s ≤ density (s ^ 2) * (2 * s) := by
    intro s hs
    dsimp only [density, pathPositiveDensity, M14.pathSquareKinetic]
    simp only [Real.sqrt_sq hs.1, map_smul, smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg (sq_nonneg s)
      (le_max_right (horizontalScalarCurvature G.leafwise (p.curve (s ^ 2))) 0)]
  have hbound := intervalIntegral.integral_mono_on hsqrt (hk.const_mul (1 / 2)) htrans hpoint
  rw [intervalIntegral.integral_const_mul, hchange] at hbound
  dsimp only [density] at hbound
  linarith



theorem pathSquareKinetic_prefix_le_positiveAction
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (p : M14BackwardPath G T 0 tau x y) {b : ℝ}
    (hb : 0 ≤ b) (hbtau : b ≤ Real.sqrt tau) :
    (∫ s in 0..b, M14.pathSquareKinetic p s) ≤
      2 * ∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t := by
  have hk : IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau) := by
    change IntervalIntegrable (fun s => G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
      ((2 * s) • p.horizontal_velocity (s ^ 2)) ((2 * s) • p.horizontal_velocity (s ^ 2)))
      volume 0 (Real.sqrt tau)
    simpa only [Real.sqrt_zero] using M14.squarePath_kinetic_intervalIntegrable p hM12
  exact (intervalIntegral.integral_mono_interval le_rfl hb hbtau
    (Filter.Eventually.of_forall (pathInitialSquareKinetic_nonneg p)) hk).trans
      (pathSquareKinetic_integral_le_positiveAction hM12 p)

end PoincareConjecture.Proofs.M46
