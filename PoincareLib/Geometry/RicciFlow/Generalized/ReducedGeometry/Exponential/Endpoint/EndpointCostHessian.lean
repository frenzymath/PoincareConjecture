import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Endpoint.EndpointCostDifferential
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Endpoint.EndpointCostMinimum
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Action.PositiveMomentumDerivative

/-!
# The genuine broken-cost Hessian detects a velocity variation

Morgan-Tian Proposition 6.30, pp. 118-119. M09's generic positive
Hessian and metric-momentum lemmas apply to the actual smooth cost
and its proved local minimum. A stationary endpoint then forces the
actual velocity variation to vanish once the prefix momentum is identified.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

universe u

namespace PoincareMT.M14.GaugeEndpointFamily

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {f : ℝ × ℝ → G.Point} {U : Set ℝ} {T b c : ℝ}
  {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j}
  (D : GaugeEndpointFamily f U T 0 b c 0 j lift)

/-- At the actual broken-action minimum, a stationary endpoint
forces the velocity variation to vanish for any smooth positive
metric representing the proved prefix momentum. This is the Hessian
step of Proposition 6.30, pp. 118-119. -/
theorem meetingVelocity_deriv_eq_zero (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 b) {x y : G.Point} (m : M14BackwardPath G T 0 (b ^ 2) x y)
    (hmin : M14IsMinimizing m)
    (heq : EqOn (fun t => f (Real.sqrt t, 0)) m.curve (Icc 0 (b ^ 2)))
    (hleft : ∀ r ∈ U, f (0, r) = x) (hright : f (b, 0) = y)
    (ξ : ℝ → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hg : ContDiffAt ℝ ∞ g (lift (f (c, 0))).2.val)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < g (lift (f (c, 0))).2.val v v)
    (ha0 : deriv (fun r => (lift (f (c, r))).2.val) 0 = 0)
    (hprefix : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w : ℝ × EuclideanSpace ℝ (Fin n),
      fderiv ℝ D.prefixAction (r, (lift (f (c, r))).2.val) w =
        g (lift (f (c, r))).2.val (ξ r) w.2) : deriv ξ 0 = 0 := by
  let a := fun r => (lift (f (c, r))).2.val
  have hS := D.tailAction_contDiffAt hM12 hc D.center_mem
  have hP : ContDiffAt ℝ ∞ (fun r => g (a r) (ξ r)) 0 :=
    (hg.comp 0 D.coordinate_smooth).clm_apply hξ
  have hR : DifferentiableAt ℝ (fun r => g (a r) (ξ r) + fderiv ℝ D.tailAction (a r)) 0 :=
    (hP.add ((hS.fderiv_right (m := ∞) (by simp)).comp 0 D.coordinate_smooth)).differentiableAt
      (by simp)
  have hderivatives := D.cost_first_derivatives hM12 hc (fun r => g (a r) (ξ r)) hprefix
  have hR0 := Proofs.M09.localMin_meetingMomentum_deriv_eq_zero D.cost a
    (fun r => g (a r) (ξ r) + fderiv ℝ D.tailAction (a r))
    (D.cost_contDiffAt hM12 hc) (D.cost_isLocalMin hM12 hc m hmin heq hleft hright)
    D.coordinate_smooth ha0 hR (hderivatives.mono fun _ h => h.1)
      (hderivatives.mono fun _ h => h.2)
  exact Proofs.M09.positiveMomentum_deriv_eq_zero a ξ g D.tailAction
    D.coordinate_smooth hξ hg hS hpos ha0 hR0

end PoincareMT.M14.GaugeEndpointFamily
