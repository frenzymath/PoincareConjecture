import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeResidual

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

theorem jacobiResidual_gauge_secondOrder
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ r ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r)
    (hclock : ∀ r ∈ Icc a c, (β r).1.val = T - r ^ 2)
    (Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂))
    (f : ℝ → EuclideanSpace ℝ (Fin n))
    (hfield : ∀ r ∈ Icc a c, HEq (Q.field r)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2 (f r)))
    {s : ℝ} (hs : s ∈ Icc a c) {Z : G.Horizontal (R.curve s)}
    (w : EuclideanSpace ℝ (Fin n))
    (hZ : HEq Z ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 w)) :
    let q := fun r => (β r).2.val
    let A := derivWithin q (Icc a c)
    let d := fun r => derivWithin f (Icc a c) r +
      M08.closedChartConnection W.flow T x₀ (Icc a c) (r, q r) (A r) (f r)
    M14JacobiResidual G R Q s Z =
      M08.chartActionMetric W.flow T x₀ (s, q s)
          (derivWithin d (Icc a c) s +
            M08.closedChartConnection W.flow T x₀ (Icc a c) (s, q s) (A s) (d s)) w -
        M08.closedChartJacobiPotential W.flow T x₀ (Icc a c) (s, q s) (A s) (f s) w +
        M08.timeWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x₀).target
          (M08.chartActionMetric W.flow T x₀) (s, q s) (d s) w := by
  let q := fun r => (β r).2.val
  let A := derivWithin q (Icc a c)
  let d := fun r => derivWithin f (Icc a c) r +
    M08.closedChartConnection W.flow T x₀ (Icc a c) (r, q r) (A r) (f r)
  have hC := uniqueDiffOn_Icc hac
  have hR := R.smooth.mono R.interval_subset
  have hd (r : ℝ) (hr : r ∈ Icc a c) : HEq (M14JacobiFirstDerivative Q r)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2 (d r)) := by
    have hres := horizontalCovariantDerivative_restrict_subset Q.extension hsub (hC r hr)
      ((hR r (hsub hr)).mdifferentiableWithinAt (by simp))
    exact (heq_of_eq hres).trans
      (horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec hclock
        (pullbackExtensionRestrict Q.extension hsub) f hfield hr (hC r hr))
  have hdd : HEq (M14JacobiSecondDerivative Q s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin d (Icc a c) s +
          M08.closedChartConnection W.flow T x₀ (Icc a c) (s, q s) (A s) (d s))) := by
    have hres := horizontalCovariantDerivative_restrict_subset Q.derivative_extension hsub
      (hC s hs) ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))
    exact (heq_of_eq hres).trans
      (horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec hclock
        (pullbackExtensionRestrict Q.derivative_extension hsub) d hd hs (hC s hs))
  exact horizontalJacobiPairResidual_gauge R b hCoordinates hscalar W hM04 x₀ hac hsub
    hβ hrec hclock hs (f s) (d s)
    (derivWithin d (Icc a c) s +
      M08.closedChartConnection W.flow T x₀ (Icc a c) (s, q s) (A s) (d s)) w
    (hfield s hs) (hd s hs) hdd hZ

end PoincareConjecture.M14
