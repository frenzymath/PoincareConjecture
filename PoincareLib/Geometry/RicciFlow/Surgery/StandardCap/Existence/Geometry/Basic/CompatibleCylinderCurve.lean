import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.CompatibleCylinderDifferential
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.IntervalClockDerivative

/-!
# Curve derivatives through an actual compatible cylinder

An interval-valued clock and a spatial curve determine a genuine
spacetime curve. The within derivative retains both components, including
the endpoints needed for the square-time initial-value problem.
Source: Morgan-Tian Proposition 12.13, pp. 304-306, ordinary capture.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT.M34

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {S : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K} {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The cylinder's curve derivative splits into actual clock and horizontal
velocities within any uniquely differentiable parameter set
(Proposition 12.13, pp. 304-306). -/
theorem compatibleCylinder_curve_mfderivWithin_one (e : CompatibleSpacetimeCylinder S D M)
    (g : SpacetimeCylinderMetric e) {A : Set ℝ} {clock : ℝ → ℝ} {gamma : ℝ → M}
    {s a : ℝ} (hs : s ∈ A) (hA : UniqueDiffWithinAt ℝ A s)
    (hclock : HasDerivWithinAt clock a A s) (hmap : MapsTo clock A K.domain)
    (hgamma : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (𝓡 n) gamma A s) :
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun r => e.toSpacetime (D.realParam (clock r), gamma r)) A s 1 =
      a • S.timeVector (e.toSpacetime (D.realParam (clock s), gamma s)) +
        (g.spatialTangentEquiv (D.realParam (clock s)) (gamma s)
          (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) gamma A s 1)).val := by
  have hbeta : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (𝓡∂ 1)
      (fun r => D.realParam (clock r)) A s :=
    (D.realParam_smoothOn.mdifferentiableOn (by simp) _ (hmap hs)).comp s
      hclock.hasFDerivWithinAt.hasMFDerivWithinAt.mdifferentiableWithinAt hmap
  have hpair := hbeta.prodMk hgamma
  have hd := mfderiv_comp_mfderivWithin s (e.smooth.mdifferentiableAt (by simp))
    hpair hA.uniqueMDiffWithinAt
  rw [mfderivWithin_prodMk hbeta hgamma hA.uniqueMDiffWithinAt] at hd
  have hv := congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) hd
  change mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
    (fun r => e.toSpacetime (D.realParam (clock r), gamma r)) A s 1 =
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime
      (D.realParam (clock s), gamma s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡∂ 1) (fun r => D.realParam (clock r)) A s 1,
        mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) gamma A s 1) at hv
  rw [realParam_comp_mfderivWithin_one D hs hA hclock hmap] at hv
  exact hv.trans (compatibleCylinder_mfderiv_prod e g _ _ a _)

end PoincareMT.M34
