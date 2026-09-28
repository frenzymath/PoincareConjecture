import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeFields
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoefficients
import PoincareConjecture.Proofs.M14.Sec6_4_GaugeFirstDerivatives
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackRestriction

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_three_eval_heq
    (F : ∀ q, G.Horizontal q → G.Horizontal q → G.Horizontal q → ℝ)
    {q r : G.Point} (h : q = r)
    {A D Z : G.Horizontal q} {A' D' Z' : G.Horizontal r}
    (hA : HEq A A') (hD : HEq D D') (hZ : HEq Z Z') : F q A D Z = F r A' D' Z' := by
  cases h
  cases hA
  cases hD
  cases hZ
  rfl

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)

theorem squareRootEulerResidual_gauge
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
    {s : ℝ} (hs : s ∈ Icc a c) {Z : G.Horizontal (R.curve s)}
    (w : EuclideanSpace ℝ (Fin n))
    (hZ : HEq Z ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 w)) :
    let q := fun r => (β r).2.val
    let v := derivWithin q (Icc a c)
    M14SquareRootEulerResidual G R E s Z =
      M08.chartActionMetric W.flow T x₀ (s, q s)
        (derivWithin v (Icc a c) s +
          M08.closedChartConnection W.flow T x₀ (Icc a c) (s, q s) (v s) (v s)) w -
        M08.spatialWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target
          (M08.chartActionPotential W.flow T x₀) (s, q s) w +
        M08.timeWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target
          (M08.chartActionMetric W.flow T x₀) (s, q s) (v s) w := by
  dsimp only
  let q := fun r => (β r).2.val
  let v := derivWithin q (Icc a c)
  have hC := uniqueDiffOn_Icc hac
  have htime (r : ℝ) (hr : r ∈ Icc a c) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr]
    exact (β r).1.property
  have hA (r : ℝ) (hr : r ∈ Icc a c) :=
    squareRootVelocity_gauge_subset b R hsub hβ hrec hr (hC r hr)
  have hD := horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec hclock
    (pullbackExtensionRestrict E hsub) v hA hs (hC s hs)
  have hres := horizontalCovariantDerivative_restrict_subset E hsub (hC s hs)
    ((R.smooth.mono R.interval_subset s (hsub hs)).mdifferentiableWithinAt (by simp))
  have hD' := (heq_of_eq hres).trans hD
  let φ := fun (z : G.Point) (A D Z : G.Horizontal z) =>
    G.spacetime.horizontalMetric.inner z D Z -
      2 * s ^ 2 * M14HorizontalScalarDifferential G z Z.val +
      4 * s * horizontalRicci G.leafwise z A Z
  have hgeom := horizontal_three_eval_heq φ (hrec s hs).symm (hA s hs) hD' hZ
  change φ (R.curve s) (R.horizontal_velocity s) _ Z = _
  rw [hgeom]
  have hy : (β s).2 ∈ (extChartAt (𝓡 n) x₀).source := by
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  have hval : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
    rw [extChartAt_coe]
    rfl
  have hy' : (β s).2.val ∈ (extChartAt (𝓡 n) x₀).target := by
    rw [← hval]
    exact (extChartAt (𝓡 n) x₀).map_source hy
  have hpot := gauge_chartActionPotential_differential b W hCoordinates hscalar hM04 T htime
    x₀ (β s).2 hs (β s).1 (hclock s hs).symm w
  rw [(M08.hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x₀) _
    (M08.chartActionPotential_closed_contDiffOn W.flow hM04 T x₀ htime) hs hy').fderiv] at hpot
  rw [gauge_chartActionMetric b W T x₀ (β s).2 s (β s).1 (hclock s hs).symm, hpot,
    gauge_chartActionMetric_timeWithin_pair b hCoordinates W hM04 T hac htime x₀ (β s).2 hs
      (β s).1 (hclock s hs).symm]

end PoincareConjecture.M14
