import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_PositiveAction
import PoincareConjecture.Statements.M12GeneralizedEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}

noncomputable def pathPositiveDensity (p : M14BackwardPath G T 0 tau x y) (s : ℝ) : ℝ :=
  max (horizontalScalarCurvature G.leafwise (p.curve s)) 0 +
    G.spacetime.horizontalMetric.inner (p.curve s)
      (p.horizontal_velocity s) (p.horizontal_velocity s)

theorem pathPositiveDensity_nonneg (p : M14BackwardPath G T 0 tau x y) (s : ℝ) :
    0 ≤ pathPositiveDensity p s := by
  apply add_nonneg (le_max_right _ _)
  by_cases hv : p.horizontal_velocity s = 0
  · simp only [hv, map_zero, le_refl]
  · exact (G.spacetime.horizontalMetric.pos (p.curve s) (p.horizontal_velocity s) hv).le

theorem pathPositiveAction_integrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) (p : M14BackwardPath G T 0 tau x y) :
    IntervalIntegrable (fun s => Real.sqrt s * pathPositiveDensity p s) volume 0 tau := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := H.scalar_smooth.continuous.comp_continuousOn p.curve_continuous
  have hcorrection : IntervalIntegrable (fun s => Real.sqrt s *
      (max (horizontalScalarCurvature G.leafwise (p.curve s)) 0 -
        horizontalScalarCurvature G.leafwise (p.curve s))) volume 0 tau := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le p.tau_lt.le]
    exact Real.continuous_sqrt.continuousOn.mul
      ((hscalar.sup continuousOn_const).sub hscalar)
  convert p.action_integrable.add hcorrection using 1
  ext s
  dsimp only [pathPositiveDensity, M14RawLIntegrand]
  ring

theorem pathPositiveAction_le_action_add
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) (p : M14BackwardPath G T 0 tau x y)
    {K : ℝ} (hK : 0 ≤ K)
    (hscalar : ∀ s ∈ Ioo 0 tau, -K ≤ horizontalScalarCurvature G.leafwise (p.curve s)) :
    (∫ s in 0..tau, Real.sqrt s * pathPositiveDensity p s) ≤
      M14BackwardLAction G p + (2 / 3 : ℝ) * K * tau * Real.sqrt tau :=
  positiveAction_le_action_add p.tau_lt.le hK hscalar p.action_integrable
    (pathPositiveAction_integrable hM12 p)

theorem pathPositiveDensity_tail_integrable
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) (p : M14BackwardPath G T 0 tau x y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbtau : b ≤ tau) :
    IntervalIntegrable (pathPositiveDensity p) volume a b := by
  have hsub : uIcc a b ⊆ uIcc 0 tau := by
    rw [uIcc_of_le hab, uIcc_of_le p.tau_lt.le]
    exact Icc_subset_Icc ha.le hbtau
  have hinv : ContinuousOn (fun s => (Real.sqrt s)⁻¹) (uIcc a b) := by
    apply Real.continuous_sqrt.continuousOn.inv₀
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact (Real.sqrt_pos.mpr (ha.trans_le hs.1)).ne'
  have hprod := ((pathPositiveAction_integrable hM12 p).mono_set hsub).mul_continuousOn
    hinv
  apply hprod.congr_uIoo
  intro s hs
  rw [uIoo_of_le hab] at hs
  have hroot : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr (ha.trans hs.1)).ne'
  dsimp only
  rw [mul_comm (Real.sqrt s), mul_assoc, mul_inv_cancel₀ hroot, mul_one]

end PoincareConjecture.Proofs.M46
