import PoincareConjecture.Proofs.M14.Sec6_3_PhaseMomentum
import PoincareConjecture.Proofs.M14.Sec6_3_EulerGaugeResidual
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}





theorem squareRootEuler_of_gauge_phase
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
    {P : ℝ → EuclideanSpace ℝ (Fin n)}
    (hphase : ∀ s ∈ Icc a c, HasDerivWithinAt (fun r => ((β r).2.val, P r))
      (M08.closedChartEulerPhase W.flow T x₀ (Icc a c) s ((β s).2.val, P s)) (Icc a c) s) :
    ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R.curve s),
      M14SquareRootEulerResidual G R E s Z = 0 := by
  let q := fun r => (β r).2.val
  have hC := uniqueDiffOn_Icc hac
  have hq := gaugeLift_spatialCurve_contDiffOn b hβ
  have hmap : MapsTo q (Icc a c) (extChartAt (𝓡 n) x₀).target := by
    intro s _
    have hval : extChartAt (𝓡 n) x₀ (β s).2 = q s := by rw [extChartAt_coe]; rfl
    rw [← hval]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  have htime (s : ℝ) (hs : s ∈ Icc a c) : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock s hs]
    exact (β s).1.property
  intro s hs Z
  obtain ⟨w, hw⟩ := exists_horizontalGauge_coordinates b (hrec s hs) Z
  have hgeom := squareRootEulerResidual_gauge R b hCoordinates hscalar W hM04 x₀ hac hsub
    hβ hrec hclock E hs w hw
  have hpair := closedChartMomentum_residual_pair W.flow T x₀ hC htime hq hmap hs w
  have hPd := (closedChartPhase_momentum_equation W.flow T x₀ hC hmap hphase s hs).derivWithin
    (hC s hs)
  calc
    _ = _ := hgeom.trans hpair.symm
    _ = 0 := by rw [hPd, sub_self, inner_zero_right]

end PoincareConjecture.M14
