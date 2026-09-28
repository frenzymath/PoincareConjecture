import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CylinderEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)

include hI in


theorem rawCylinder_sourceEnergy_upper
    (gSource : RiemannianMetric 3 C.carrier) (factor : ℝ)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (x : U)
      (v : TangentSpace (𝓡 3) x.val),
      e.pullbackInner s hs x.val v v ≤ q * (factor * gSource.inner x.val v v))
    (theta : ℝ → (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval a q e.scale_pos J)).Point)
    (z : ℝ → U) {r : ℝ}
    (htheta : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 1) theta r)
    (hz : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) z r) :
    realizedHorizontalForm G.realization (rawCylinderMap G.realization e (theta r, z r))
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3)
        (fun t => rawCylinderMap G.realization e (theta t, z t)) r 1)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel 3)
        (fun t => rawCylinderMap G.realization e (theta t, z t)) r 1) ≤
      factor * M08.referenceSpeedSq gSource (fun t => (z t).val) r := by
  let M := rawCylinderMetric G.realization e hI
  let s := cylinderClockHomeomorph a q e.scale_pos J (theta r)
  have hclock : a + s.val / q = (theta r).val :=
    parabolicTimeInv_parabolicTime q e.scale_pos a (theta r).val
  have hvelocity := M14.ordinaryCapture_cylinderVelocity (G := G.toLGeometry)
    (e := rawCylinderTransport G.realization e hI) (g := M) theta z htheta hz
  change M14.projectedCurveVelocity G.toLGeometry
      (fun t => rawCylinderMap G.realization e (theta t, z t)) r =
    M.spatialTangentEquiv (theta r) (z r) (curveVelocity z r) at hvelocity
  change G.toLGeometry.spacetime.horizontalMetric.inner
      (rawCylinderMap G.realization e (theta r, z r))
      (M14.projectedCurveVelocity G.toLGeometry
        (fun t => rawCylinderMap G.realization e (theta t, z t)) r)
      (M14.projectedCurveVelocity G.toLGeometry
        (fun t => rawCylinderMap G.realization e (theta t, z t)) r) ≤ _
  rw [hvelocity]
  change G.realization.spacetime.horizontalMetric.inner
      ((rawCylinderTransport G.realization e hI).toSpacetime (theta r, z r))
      (M.spatialTangentEquiv (theta r) (z r) (curveVelocity z r))
      (M.spatialTangentEquiv (theta r) (z r) (curveVelocity z r)) ≤ _
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
  exact (div_le_iff₀ e.scale_pos).mpr (by
    simpa only [mul_comm] using hbound s.val s.property (z r)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (z r) (curveVelocity z r)))

end PoincareConjecture.Proofs.M46
