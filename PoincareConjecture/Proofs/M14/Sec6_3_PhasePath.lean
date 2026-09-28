import PoincareConjecture.Proofs.M14.Sec6_3_GaugeCoordinateLift
import PoincareConjecture.Proofs.M14.Sec6_3_PhaseEuler
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurvePath

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem exists_gaugeEulerPath_of_phase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b) {T a c : ℝ} (ha : 0 ≤ a) (hac : a < c)
    (htime : ∀ s ∈ M14SqrtParameterInterval a c,
      T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    {q P : ℝ → EuclideanSpace ℝ (Fin n)}
    (hq : ContDiffOn ℝ ∞ q (M14SqrtParameterInterval a c))
    (hmap : MapsTo q (M14SqrtParameterInterval a c) (extChartAt (𝓡 n) x₀).target)
    (hphase : ∀ s ∈ M14SqrtParameterInterval a c,
      HasDerivWithinAt (fun r => (q r, P r))
        (M08.closedChartEulerPhase W.flow T x₀ (M14SqrtParameterInterval a c)
          s (q s, P s)) (M14SqrtParameterInterval a c) s) :
    ∃ β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b,
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (M14SqrtParameterInterval a c) ∧
      (∀ s ∈ M14SqrtParameterInterval a c, (β s).1.val = T - s ^ 2) ∧
      (∀ s ∈ M14SqrtParameterInterval a c, (β s).2.val = q s) ∧
      ∃ (p : M14BackwardPath G T a c
          ((G.gaugeCover.cylinder b).toSpacetime (β (Real.sqrt a)))
          ((G.gaugeCover.cylinder b).toSpacetime (β (Real.sqrt c))))
        (R : M14SquareRootPath G p)
        (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a c) R.horizontal_velocity),
        (∀ τ ∈ Icc a c, p.curve τ = (G.gaugeCover.cylinder b).toSpacetime (β (Real.sqrt τ))) ∧
        (∀ s ∈ M14SqrtParameterInterval a c,
          R.curve s = (G.gaugeCover.cylinder b).toSpacetime (β s)) ∧
        (∀ s ∈ M14SqrtParameterInterval a c, ∀ Z : G.Horizontal (R.curve s),
          M14SquareRootEulerResidual G R E s Z = 0) ∧
        ∀ s ∈ M14SqrtParameterInterval a c,
          HEq (R.horizontal_velocity s)
            ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
              (derivWithin q (M14SqrtParameterInterval a c) s)) := by
  obtain ⟨β, hβ, hclock, hcoord⟩ :=
    exists_smooth_gaugeLift_of_coordinates b t₀ x₀ T htime hq hmap
  let α := fun s => (G.gaugeCover.cylinder b).toSpacetime (β s)
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (M14SqrtParameterInterval a c) :=
    (G.gaugeCover.cylinder b).smooth.comp_contMDiffOn hβ
  have hαclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a c) :
      G.spacetime.timeFunction (α s) = T - s ^ 2 :=
    ((G.gaugeCover.cylinder b).time_eq (β s)).trans (hclock s hs)
  let p := backwardPathOfSquareCurve hM12 ha hac α hα hαclock
  let R := squareRootPathOfSquareCurve hM12 ha hac α hα hαclock
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  have hrec (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a c) :
      (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s :=
    (squareRootPathOfSquareCurve_curve hM12 ha hac α hα hαclock hs).symm
  have hphaseβ (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a c) :
      HasDerivWithinAt (fun r => ((β r).2.val, P r))
        (M08.closedChartEulerPhase W.flow T x₀ (M14SqrtParameterInterval a c)
          s ((β s).2.val, P s)) (M14SqrtParameterInterval a c) s := by
    rw [hcoord s hs]
    exact (hphase s hs).congr_of_mem (fun r hr => Prod.ext (hcoord r hr) rfl) hs
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  have hC := Real.sqrt_lt_sqrt ha hac
  refine ⟨β, hβ, hclock, hcoord, p, R, E, fun _ _ => rfl,
    fun s hs => (hrec s hs).symm,
    squareRootEuler_of_gauge_phase R b hCoordinates hscalar W hM04 x₀ hC Subset.rfl
      hβ hrec hclock E hphaseβ, ?_⟩
  intro s hs
  have hv := squareRootVelocity_gauge_subset b R Subset.rfl hβ hrec hs (uniqueDiffOn_Icc hC s hs)
  rw [derivWithin_congr hcoord (hcoord s hs)] at hv
  exact hv

end PoincareConjecture.M14
