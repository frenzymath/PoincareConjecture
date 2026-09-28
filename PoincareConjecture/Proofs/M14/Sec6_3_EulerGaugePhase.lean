import PoincareConjecture.Proofs.M14.Sec6_3_EulerGaugeResidual
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerMomentum
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)
  (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
  (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
    (horizontalScalarCurvature G.leafwise))
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
  (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
  {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
  {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b}
  (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
  (hrec : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
  (hclock : ∀ s ∈ Icc a c, (β s).1.val = T - s ^ 2)
  (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
    R.horizontal_velocity)
  (heuler : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R.curve s),
    M14SquareRootEulerResidual G R E s Z = 0)

private theorem gaugeCoordinate_mem_target (s : ℝ) :
    (β s).2.val ∈ (extChartAt (𝓡 n) x₀).target := by
  have hval : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
    rw [extChartAt_coe]
    rfl
  rw [← hval]
  apply (extChartAt (𝓡 n) x₀).map_source
  rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
  exact mem_univ _

include hCoordinates hscalar hM04 hac hsub hβ hrec hclock heuler

theorem squareRootEuler_gauge_momentum :
    let q := fun r => (β r).2.val
    let v := derivWithin q (Icc a c)
    let B := M08.chartActionMetric W.flow T x₀
    ∀ s ∈ Icc a c,
      HasDerivWithinAt (fun r => M08.chartMomentumVector (B (r, q r)) (v r))
        (M08.chartForceVector
          (M08.spatialWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target B (s, q s))
          (M08.spatialWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target
            (M08.chartActionPotential W.flow T x₀) (s, q s)) (v s)) (Icc a c) s := by
  dsimp only
  intro s hs
  let q := fun r => (β r).2.val
  let v := derivWithin q (Icc a c)
  let B := M08.chartActionMetric W.flow T x₀
  let P := fun r => M08.chartMomentumVector (B (r, q r)) (v r)
  let F := M08.chartForceVector
    (M08.spatialWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target B (s, q s))
    (M08.spatialWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target
      (M08.chartActionPotential W.flow T x₀) (s, q s)) (v s)
  have hC := uniqueDiffOn_Icc hac
  have hq := gaugeLift_spatialCurve_contDiffOn b hβ
  have hmap : MapsTo q (Icc a c) (extChartAt (𝓡 n) x₀).target :=
    fun r _ => gaugeCoordinate_mem_target b x₀ r
  have htime (r : ℝ) (hr : r ∈ Icc a c) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr]
    exact (β r).1.property
  have hPd := ((closedChartMomentum_contDiffOn W.flow T x₀ hC htime hq hmap) s hs)
    |>.differentiableWithinAt (by simp) |>.hasDerivWithinAt
  have hforce : derivWithin P (Icc a c) s = F := by
    apply ext_inner_left ℝ
    intro w
    let Z := horizontalFieldOfGauge b hrec (fun _ => w) s
    have hgeom := squareRootEulerResidual_gauge R b hCoordinates hscalar W hM04 x₀ hac hsub
      hβ hrec hclock E hs w (horizontalFieldOfGauge_heq b hrec (fun _ => w) hs)
    have hp := closedChartMomentum_residual_pair W.flow T x₀ hC htime hq hmap hs w
    have hz : inner ℝ w (derivWithin P (Icc a c) s - F) = 0 :=
      hp.trans (hgeom.symm.trans (heuler s hs Z))
    simpa only [inner_sub_right, sub_eq_zero] using hz
  change HasDerivWithinAt P F (Icc a c) s
  rw [← hforce]
  exact hPd

theorem squareRootEuler_gauge_phase :
    let q := fun r => (β r).2.val
    let P := fun r => M08.chartMomentumVector (M08.chartActionMetric W.flow T x₀ (r, q r))
      (derivWithin q (Icc a c) r)
    ∀ s ∈ Icc a c, HasDerivWithinAt (fun r => (q r, P r))
      (M08.closedChartEulerPhase W.flow T x₀ (Icc a c) s (q s, P s)) (Icc a c) s := by
  dsimp only
  intro s hs
  let q := fun r => (β r).2.val
  let v := derivWithin q (Icc a c)
  let P := fun r => M08.chartMomentumVector (M08.chartActionMetric W.flow T x₀ (r, q r)) (v r)
  have hq := gaugeLift_spatialCurve_contDiffOn b hβ
  have hqd := ((hq s hs).differentiableWithinAt (by simp)).hasDerivWithinAt
  have hPd := squareRootEuler_gauge_momentum R b hCoordinates hscalar W hM04 x₀ hac hsub
    hβ hrec hclock E heuler s hs
  have hinv : Ring.inverse (M08.chartMetricOperator W.flow T x₀ (s, q s)) (P s) = v s :=
    M08.inverse_operator_apply _ (M08.chartMetricOperator_isUnit_of_target W.flow T x₀
      (gaugeCoordinate_mem_target b x₀ s)) (v s)
  change HasDerivWithinAt (fun r => (q r, P r))
    (M08.closedChartEulerPhase W.flow T x₀ (Icc a c) s (q s, P s)) (Icc a c) s
  dsimp only [M08.closedChartEulerPhase]
  rw [hinv]
  exact hqd.prodMk hPd

end PoincareConjecture.M14
