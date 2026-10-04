import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.CylinderLocalInverse
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderMetric
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Ordinary.Capture.OrdinaryCaptureAction
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.ReferenceEnergy

/-!
# Actual kinetic energy in physical inverse-cylinder coordinates

Proposition 16.13, pp. 377-378. The actual cylinder differential sends
the spatial derivative to the horizontal projection of the full path
derivative. The normalized pullback metric is divided by its same
positive scale before comparison with the physical birth metric.
-/

set_option autoImplicit false
-- The physical source and actual horizontal tangent fibers are retained.
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
namespace PoincareMT.M08
export PoincareMT.LGeometry (referenceSpeedSq)
end PoincareMT.M08

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)

include hI in
/-- The actual horizontal kinetic energy dominates the birth-coordinate
kinetic energy when the physical cylinder metrics have that lower bound.
Source: Proposition 16.13, pp. 377-378. -/
theorem rawCylinder_birthEnergy_lower
    (gBirth : RiemannianMetric 3 C.carrier) (mu : ℝ)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (x : U)
      (v : TangentSpace (𝓡 3) x.val),
      q * (mu * gBirth.inner x.val v v) ≤ e.pullbackInner s hs x.val v v)
    (theta : ℝ → (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval a q e.scale_pos J)).Point)
    (z : ℝ → U) {r : ℝ}
    (htheta : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 1) theta r)
    (hz : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) z r) :
    mu * M08.referenceSpeedSq gBirth (fun t => (z t).val) r ≤
      realizedHorizontalForm G.realization (rawCylinderMap G.realization e (theta r, z r))
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3)
          (fun t => rawCylinderMap G.realization e (theta t, z t)) r 1)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3)
          (fun t => rawCylinderMap G.realization e (theta t, z t)) r 1) := by
  let M := rawCylinderMetric G.realization e hI
  let s := cylinderClockHomeomorph a q e.scale_pos J (theta r)
  have hclock : a + s.val / q = (theta r).val :=
    parabolicTimeInv_parabolicTime q e.scale_pos a (theta r).val
  have hvelocity := M14.ordinaryCapture_cylinderVelocity (G := G.toLGeometry)
    (e := rawCylinderTransport G.realization e hI) (g := M) theta z htheta hz
  change M14.projectedCurveVelocity G.toLGeometry
      (fun t => rawCylinderMap G.realization e (theta t, z t)) r =
    M.spatialTangentEquiv (theta r) (z r) (curveVelocity z r) at hvelocity
  change mu * M08.referenceSpeedSq gBirth (fun t => (z t).val) r ≤
    G.toLGeometry.spacetime.horizontalMetric.inner
      (rawCylinderMap G.realization e (theta r, z r))
      (M14.projectedCurveVelocity G.toLGeometry
        (fun t => rawCylinderMap G.realization e (theta t, z t)) r)
      (M14.projectedCurveVelocity G.toLGeometry
        (fun t => rawCylinderMap G.realization e (theta t, z t)) r)
  rw [hvelocity]
  change mu * M08.referenceSpeedSq gBirth (fun t => (z t).val) r ≤
    G.realization.spacetime.horizontalMetric.inner
      ((rawCylinderTransport G.realization e hI).toSpacetime (theta r, z r))
      (M.spatialTangentEquiv (theta r) (z r) (curveVelocity z r))
      (M.spatialTangentEquiv (theta r) (z r) (curveVelocity z r))
  rw [← M.metric_eq]
  have hm := rawCylinderMetric_eq G.realization e hI M s
    (G.sliceIdentification (a + s.val / q)) (z r) (curveVelocity z r) (curveVelocity z r)
  rw [hclock] at hm
  rw [hm]
  have hv : curveVelocity (fun t => (z t).val) r =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (z r) (curveVelocity z r) :=
    mfderiv_comp_apply r
      ((contMDiff_subtype_val (n := ∞) (z r)).mdifferentiableAt (by simp)) hz 1
  unfold M08.referenceSpeedSq
  rw [hv]
  exact (le_div_iff₀ e.scale_pos).mpr (by
    simpa only [mul_comm] using hbound s.val s.property (z r)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (z r) (curveVelocity z r)))

/-- Equality of actual path germs preserves the kinetic readout.
Source: Definition 6.1 and Proposition 16.13, pp. 105 and 377-378. -/
theorem realizedHorizontalEnergy_congr
    {gamma eta : ℝ → G.realization.spacetime.Point} {r : ℝ}
    (h : gamma =ᶠ[𝓝 r] eta) :
    realizedHorizontalForm G.realization (gamma r)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) gamma r 1)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) gamma r 1) =
      realizedHorizontalForm G.realization (eta r)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) eta r 1)
        (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3) eta r 1) := by
  rw [h.mfderiv_eq, h.eq_of_nhds]

end PoincareMT.Proofs.M46
