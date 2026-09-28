import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeFields
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoefficients
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPair










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_five_eval_heq
    (F : ∀ q, G.Horizontal q → G.Horizontal q → G.Horizontal q →
      G.Horizontal q → G.Horizontal q → ℝ)
    {q r : G.Point} (h : q = r)
    {A Y P DP Z : G.Horizontal q} {A' Y' P' DP' Z' : G.Horizontal r}
    (hA : HEq A A') (hY : HEq Y Y') (hP : HEq P P') (hDP : HEq DP DP') (hZ : HEq Z Z') :
    F q A Y P DP Z = F r A' Y' P' DP' Z' := by
  cases h
  cases hA
  cases hY
  cases hP
  cases hDP
  cases hZ
  rfl

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)




theorem horizontalJacobiPairResidual_gauge
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
    {s : ℝ} (hs : s ∈ Icc a c) {Y P DP Z : G.Horizontal (R.curve s)}
    (v f d w : EuclideanSpace ℝ (Fin n))
    (hY : HEq Y ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 v))
    (hP : HEq P ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 f))
    (hDP : HEq DP ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 d))
    (hZ : HEq Z ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 w)) :
    horizontalJacobiPairResidual R s Y P DP Z =
      M08.chartActionMetric W.flow T x₀ (s, (β s).2.val) d w -
        M08.closedChartJacobiPotential W.flow T x₀ (Icc a c) (s, (β s).2.val)
          (derivWithin (fun r => (β r).2.val) (Icc a c) s) v w +
        M08.timeWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target
          (M08.chartActionMetric W.flow T x₀) (s, (β s).2.val) f w := by
  have htime (r : ℝ) (hr : r ∈ Icc a c) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr]
    exact (β r).1.property
  let A := derivWithin (fun r => (β r).2.val) (Icc a c) s
  have hA := squareRootVelocity_gauge_subset b R hsub hβ hrec hs (uniqueDiffOn_Icc hac s hs)
  let φ := fun (q : G.Point) (A Y P DP Z : G.Horizontal q) =>
    G.spacetime.horizontalMetric.inner q DP Z + horizontalRiemann G.leafwise q Y A Z A -
      2 * s * M14BcalPairing G q A Y Z - 2 * s ^ 2 * M14HorizontalHessianPairing G q Y Z +
      4 * s * M14HorizontalRicciDerivativePairing G q Y A Z +
      4 * s * horizontalRicci G.leafwise q P Z
  have hgeom := horizontal_five_eval_heq φ (hrec s hs).symm hA hY hP hDP hZ
  change φ (R.curve s) (R.horizontal_velocity s) Y P DP Z = _
  rw [hgeom]
  rw [gauge_chartActionMetric b W T x₀ (β s).2 s (β s).1 (hclock s hs).symm,
    gauge_closedJacobiPotential b hCoordinates W hM04 T hac htime x₀ (β s).2 hs (β s).1
      (hclock s hs).symm hscalar,
    gauge_chartActionMetric_timeWithin_pair b hCoordinates W hM04 T hac htime x₀ (β s).2 hs
      (β s).1 (hclock s hs).symm]
  dsimp only [φ]
  ring

end PoincareConjecture.M14
