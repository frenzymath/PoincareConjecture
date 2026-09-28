import PoincareConjecture.Proofs.M14.Sec6_3_PhasePath
import PoincareConjecture.Definitions.M14Exponential










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem exists_initialValuePath_of_normalized_phase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {τ : ℝ} (hτ : 0 < τ)
    (htime : ∀ s ∈ M14SqrtParameterInterval 0 τ,
      t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    {q P : ℝ → EuclideanSpace ℝ (Fin n)}
    (hq : ContDiffOn ℝ ∞ q (M14SqrtParameterInterval 0 τ))
    (hmap : MapsTo q (M14SqrtParameterInterval 0 τ) (extChartAt (𝓡 n) x₀).target)
    (hphase : ∀ s ∈ M14SqrtParameterInterval 0 τ,
      HasDerivWithinAt (fun r => (q r, P r))
        (M08.closedChartEulerPhase W.flow t₀.val x₀ (M14SqrtParameterInterval 0 τ)
          s (q s, P s)) (M14SqrtParameterInterval 0 τ) s)
    (hq₀ : q 0 = x₀.val)
    (hv₀ : derivWithin q (M14SqrtParameterInterval 0 τ) 0 =
      (2 : ℝ) • ((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm Z) :
    ∃ y : G.Point, Nonempty (M14SquareRootInitialValuePath G t₀.val τ
      ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) y Z) := by
  obtain ⟨β, _, hclock, hcoord, p, R, E, _, hR, hE, hv⟩ :=
    exists_gaugeEulerPath_of_phase hM04 hM12 b W t₀ x₀ le_rfl hτ htime hq hmap hphase
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ :=
    ⟨by simp only [Real.sqrt_zero, le_refl], Real.sqrt_nonneg τ⟩
  have hβ₀ : β 0 = (t₀, x₀) := by
    apply Prod.ext
    · apply Subtype.ext
      simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hclock 0 hzero
    · exact Subtype.ext ((hcoord 0 hzero).trans hq₀)
  have hstart : (G.gaugeCover.cylinder b).toSpacetime (β (Real.sqrt 0)) =
      (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀) := by
    rw [Real.sqrt_zero, hβ₀]
  let p' : M14BackwardPath G t₀.val 0 τ
      ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))
      ((G.gaugeCover.cylinder b).toSpacetime (β (Real.sqrt τ))) :=
    { p with
      base_time := by simpa only [sub_zero] using (G.gaugeCover.cylinder b).time_eq (t₀, x₀)
      curve_start := p.curve_start.trans hstart }
  let R' : M14SquareRootPath G p' := { R with curve := R.curve }
  refine ⟨_, ⟨{
    path := p'
    square_path := R'
    extension := E
    euler := hE
    initial_velocity := ?_ }⟩⟩
  have hR₀ : R.curve 0 = (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀) :=
    (hR 0 hzero).trans (congrArg (G.gaugeCover.cylinder b).toSpacetime hβ₀)
  refine ⟨hR₀, ?_⟩
  have hvzero := hv 0 hzero
  rw [hβ₀, hv₀, map_smul, ContinuousLinearEquiv.apply_symm_apply] at hvzero
  have ht : HEq (hR₀ ▸ R.horizontal_velocity 0) (R.horizontal_velocity 0) := eqRec_heq _ _
  exact eq_of_heq (ht.trans hvzero)




theorem exists_initialValuePath_of_momentum_phase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {τ : ℝ} (hτ : 0 < τ)
    (htime : ∀ s ∈ M14SqrtParameterInterval 0 τ,
      t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    {q P : ℝ → EuclideanSpace ℝ (Fin n)}
    (hq : ContDiffOn ℝ ∞ q (M14SqrtParameterInterval 0 τ))
    (hmap : MapsTo q (M14SqrtParameterInterval 0 τ) (extChartAt (𝓡 n) x₀).target)
    (hphase : ∀ s ∈ M14SqrtParameterInterval 0 τ,
      HasDerivWithinAt (fun r => (q r, P r))
        (M08.closedChartEulerPhase W.flow t₀.val x₀ (M14SqrtParameterInterval 0 τ)
          s (q s, P s)) (M14SqrtParameterInterval 0 τ) s)
    (hi : (q 0, P 0) = (x₀.val, M08.chartMetricOperator W.flow t₀.val x₀ (0, x₀.val)
      ((2 : ℝ) • ((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm Z))) :
    ∃ y : G.Point, Nonempty (M14SquareRootInitialValuePath G t₀.val τ
      ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) y Z) := by
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ :=
    ⟨by simp only [Real.sqrt_zero, le_refl], Real.sqrt_nonneg τ⟩
  have hv : HasDerivWithinAt q
      (Ring.inverse (M08.chartMetricOperator W.flow t₀.val x₀ (0, q 0)) (P 0))
      (M14SqrtParameterInterval 0 τ) 0 := (hphase 0 hzero).fst
  have hv₀ := hv.derivWithin
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (le_refl (0 : ℝ)) hτ) 0 hzero)
  have hq₀ := congrArg Prod.fst hi
  have hP₀ := congrArg Prod.snd hi
  dsimp only [Prod.fst, Prod.snd] at hq₀ hP₀
  have hx₀ : x₀.val ∈ (extChartAt (𝓡 n) x₀).target := hq₀ ▸ hmap hzero
  rw [hq₀, hP₀] at hv₀
  exact exists_initialValuePath_of_normalized_phase hM04 hM12 b W t₀ x₀ Z hτ
    htime hq hmap hphase hq₀ (hv₀.trans (M08.inverse_operator_apply _
      (M08.chartMetricOperator_isUnit_of_target W.flow t₀.val x₀ hx₀) _))

end PoincareConjecture.M14
