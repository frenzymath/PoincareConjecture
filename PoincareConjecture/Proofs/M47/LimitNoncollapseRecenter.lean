import PoincareConjecture.Proofs.M47.LimitNoncollapseSource

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
  (a : ℝ) (ha : a ∈ I) {J : Set ℝ}
  (hrange : MapsTo (fun s => a + scale * s) J I)
  (V : Set (F.slice (origin + a / scale)).carrier)
  (hV : V ⊆ e.forward a ha '' U)

noncomputable def limitNoncollapseCylinderRecenter :
    GeneralizedFlowCylinder F (F.slice (origin + a / scale))
      (origin + a / scale) 1 J V :=
  let chart := limitRP2CylinderSliceChart e hU a ha
  limitNoncollapseCylinderSource (limitNoncollapseCylinderReclock e a hrange)
    chart.symm V hV (fun _ hx => chart.symm.map_source (hV hx))

theorem limitNoncollapseCylinderRecenter_pointMap (s : ℝ) (hs : s ∈ J)
    (x : (F.slice (origin + a / scale)).carrier) :
    (limitNoncollapseCylinderRecenter e hU a ha hrange V hV).pointMap s hs x =
      e.pointMap (a + scale * s) (hrange hs) (e.inverse a ha x) := by
  exact limitNoncollapseCylinderReclock_pointMap e a hrange s hs (e.inverse a ha x)

theorem limitNoncollapseCylinderRecenter_zero (h0 : 0 ∈ J)
    (x : (F.slice (origin + a / scale)).carrier) (hx : x ∈ V) :
    (limitNoncollapseCylinderRecenter e hU a ha hrange V hV).pointMap 0 h0 x =
      (⟨origin + a / scale, x⟩ : F.point) := by
  have hpoint (b : ℝ) (hb : b ∈ I) (hba : b = a) :
      e.pointMap b hb (e.inverse a ha x) = (⟨origin + a / scale, x⟩ : F.point) := by
    subst b
    exact congrArg (fun y => (⟨origin + a / scale, y⟩ : F.point))
      (e.right_inverse a ha (hV hx))
  exact (limitNoncollapseCylinderRecenter_pointMap e hU a ha hrange V hV 0 h0 x).trans
    (hpoint _ _ (by ring))

theorem limitNoncollapseCylinderRecenter_pullbackInner (s : ℝ) (hs : s ∈ J)
    (x : (F.slice (origin + a / scale)).carrier) (hx : x ∈ V)
    (v w : TangentSpace (𝓡 3) x) :
    (limitNoncollapseCylinderRecenter e hU a ha hrange V hV).pullbackInner s hs x v w =
      e.pullbackInner (a + scale * s) (hrange hs) (e.inverse a ha x)
        (mfderiv (𝓡 3) (𝓡 3) (e.inverse a ha) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e.inverse a ha) x w) / scale := by
  let chart := limitRP2CylinderSliceChart e hU a ha
  have hsource := limitNoncollapseCylinderSource_pullbackInner
    (limitNoncollapseCylinderReclock e a hrange) chart.symm V hV
    (fun _ hy => chart.symm.map_source (hV hy)) hU s hs x hx v w
  exact hsource.trans (limitNoncollapseCylinderReclock_pullbackInner e a hrange s hs
    (e.inverse a ha x) _ _)

theorem limitNoncollapseCylinderRecenter_curvatureNorm (s : ℝ) (hs : s ∈ J)
    (x : (F.slice (origin + a / scale)).carrier) :
    F.curvatureNorm
        ((limitNoncollapseCylinderRecenter e hU a ha hrange V hV).pointMap s hs x) =
      F.curvatureNorm (e.pointMap (a + scale * s) (hrange hs) (e.inverse a ha x)) := by
  rw [limitNoncollapseCylinderRecenter_pointMap]

include e in

theorem limitNoncollapseCylinder_time_mem (s : ℝ) (hs : s ∈ I) (x : C.carrier) :
    origin + s / scale ∈ F.interval :=
  (F.slice_nonempty_iff _).mp ⟨e.forward s hs x⟩

end PoincareConjecture.M47
