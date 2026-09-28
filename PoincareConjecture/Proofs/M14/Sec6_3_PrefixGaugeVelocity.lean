import PoincareConjecture.Proofs.M14.Sec6_3_SquareRootComparison
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeParameterDifferential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem squareRootVelocity_gauge_continuation (R : M14SquareRootPath G p)
    (α : ℝ → G.Point) (heq : EqOn R.curve α (M14SqrtParameterInterval a b))
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n) α s)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j)
    (hlift : MDifferentiableAt (spacetimeModel n) (spacetimeModel n) lift (α s))
    (hrec : α =ᶠ[𝓝 s] fun t => (G.gaugeCover.cylinder j).toSpacetime (lift (α t))) :
    HEq (R.horizontal_velocity s) ((G.gaugeCover.metric j).spatialTangentEquiv
      (lift (α s)).1 (lift (α s)).2 (deriv (fun t => (lift (α t)).2.val) s)) := by
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs
  have hv := projectedCurveVelocityWithin_congrOn (G := G) heq hs
  rw [squareRoot_projectedVelocityWithin_subset R Subset.rfl hs hC] at hv
  have hactual : projectedCurveVelocityWithin G α (M14SqrtParameterInterval a b) s =
      projectedCurveVelocity G α s := by
    exact congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n =>
      G.spacetime.horizontalProjection (α s) (L (1 : ℝ)))
        (mfderivWithin_eq_mfderiv hC.uniqueMDiffWithinAt hα)
  rw [hactual] at hv
  have hg := gaugeMap_projectedDifferential_congr j (hlift.comp s hα) hrec (1 : ℝ)
  rw [fderiv_apply_one_eq_deriv] at hg
  exact hv.trans hg

end PoincareConjecture.M14
