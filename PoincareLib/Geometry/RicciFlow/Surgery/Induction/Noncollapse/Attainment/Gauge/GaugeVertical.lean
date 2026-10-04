import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Gauge.GaugeRecovery
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeCurve
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual vertical curves in inverse gauges

Proposition 16.4, p. 369. Zero horizontal velocity forces constant spatial
coordinates on a connected open parameter interval. This identifies the
vertical endpoint germs used by recovery without an additional worldline
uniqueness premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

/-- A zero-horizontal-velocity curve has zero spatial derivative in
every actual inverse gauge. Source: Definition 3.38 and the coordinate
argument in Proposition 16.4, pp. 61, 369. -/
theorem gauge_lift_spatial_deriv_zero (e : AttainmentGauge G)
    {U : Set ℝ} (hU : IsOpen U) (beta : ℝ → G.Point)
    (hbeta : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 beta U)
    (hsrc : MapsTo beta U e.source)
    (hzero : ∀ s ∈ U, M14.projectedCurveVelocity G beta s = 0)
    {s : ℝ} (hs : s ∈ U) : deriv (fun r => (e.lift (beta r)).2.val) s = 0 := by
  let lift := fun r => e.lift (beta r)
  have hlift : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 lift U :=
    (e.smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hbeta hsrc
  have htheta := ((hlift s hs).fst.contMDiffAt (hU.mem_nhds hs)).mdifferentiableAt
    (by simp)
  have hspace := ((hlift s hs).snd.contMDiffAt (hU.mem_nhds hs)).mdifferentiableAt
    (by simp)
  let alpha := fun r => (G.gaugeCover.cylinder e.index).toSpacetime (lift r)
  have hrec : alpha =ᶠ[𝓝 s] beta := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact e.right_inv (beta r) (hsrc hr)
  have hvel : M14.projectedCurveVelocity G alpha s = 0 := by
    have hd := hrec.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel 3)
    unfold M14.projectedCurveVelocity
    rw [hd, hrec.eq_of_nhds]
    exact hzero s hs
  have hg := M14.gaugeCurve_projectedVelocity e.index
    (fun r => (lift r).1) (fun r => (lift r).2) htheta hspace
  change M14.projectedCurveVelocity G alpha s = _ at hg
  rw [hg] at hvel
  exact (G.gaugeCover.metric e.index).spatialTangentEquiv (lift s).1 (lift s).2 |>.injective
    (by simpa only [map_zero] using hvel)

/-- The actual spatial coordinate of a vertical curve is constant on
each connected open interval in its inverse gauge. Source:
Definition 3.38 and Proposition 16.4, pp. 61, 369. -/
theorem gauge_lift_spatial_constant (e : AttainmentGauge G)
    {U : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U) (beta : ℝ → G.Point)
    (hbeta : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 beta U)
    (hsrc : MapsTo beta U e.source)
    (hzero : ∀ s ∈ U, M14.projectedCurveVelocity G beta s = 0)
    {s c : ℝ} (hs : s ∈ U) (hc : c ∈ U) :
    (e.lift (beta s)).2 = (e.lift (beta c)).2 := by
  have hlift := (e.smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hbeta hsrc
  have hval : ContMDiff (𝓡 3) (𝓡 3) 1
      (Subtype.val : G.gaugeCover.spatial e.index → EuclideanSpace ℝ (Fin 3)) :=
    contMDiff_subtype_val
  have hspatial : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1
      (fun r => (e.lift (beta r)).2) U := fun r hr => (hlift r hr).snd
  have hdiff := (hval.comp_contMDiffOn hspatial).contDiffOn.differentiableOn (by simp)
  apply Subtype.ext
  exact hU.is_const_of_deriv_eq_zero hconn hdiff
    (fun r hr => gauge_lift_spatial_deriv_zero e hU beta hbeta hsrc hzero hr) hs hc

/-- An actual constant-spatial cylinder curve has zero horizontal
velocity wherever its clock is differentiable. Source: Definition 3.38,
p. 61. -/
theorem gauge_vertical_velocity_zero (j : G.gaugeCover.index)
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (x0 : G.gaugeCover.spatial j) {s : ℝ}
    (htheta : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) theta s) :
    M14.projectedCurveVelocity G
      (fun r => (G.gaugeCover.cylinder j).toSpacetime (theta r, x0)) s = 0 := by
  have hg := M14.gaugeCurve_projectedVelocity j theta (fun _ => x0)
    htheta mdifferentiableAt_const
  exact hg.trans ((congrArg ((G.gaugeCover.metric j).spatialTangentEquiv (theta s) x0)
    (deriv_const s x0.val)).trans (map_zero _))

end PoincareMT.Proofs.M46
