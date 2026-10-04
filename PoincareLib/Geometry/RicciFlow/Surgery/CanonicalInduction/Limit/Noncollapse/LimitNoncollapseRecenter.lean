import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Noncollapse.LimitNoncollapseSource

/-!
# Based generalized cylinders from the actual convergence chart

The original slice inverse supplies the spatial labels and the affine
clock supplies the physical time. Every cylinder field is constructed.
Source: Morgan--Tian, Proposition 17.1, pp. 407-408; reviewed
`derivations/limit-noncollapse-transfer.md`, section 6.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
  (a : ℝ) (ha : a ∈ I) {J : Set ℝ}
  (hrange : MapsTo (fun s => a + scale * s) J I)
  (V : Set (F.slice (origin + a / scale)).carrier)
  (hV : V ⊆ e.forward a ha '' U)

/-- The actual physical cylinder on a contained image region, based at its
chosen top time; reviewed section 6. Image containment is local adapter
data, to be produced by the separate ambient-ball coverage argument. -/
noncomputable def limitNoncollapseCylinderRecenter :
    GeneralizedFlowCylinder F (F.slice (origin + a / scale))
      (origin + a / scale) 1 J V :=
  let chart := limitRP2CylinderSliceChart e hU a ha
  limitNoncollapseCylinderSource (limitNoncollapseCylinderReclock e a hrange)
    chart.symm V hV (fun _ hx => chart.symm.map_source (hV hx))

/-- The rebased point follows the same original vertical worldline through
the actual inverse at the top time, with exact physical clock, section 6. -/
theorem limitNoncollapseCylinderRecenter_pointMap (s : ℝ) (hs : s ∈ J)
    (x : (F.slice (origin + a / scale)).carrier) :
    (limitNoncollapseCylinderRecenter e hU a ha hrange V hV).pointMap s hs x =
      e.pointMap (a + scale * s) (hrange hs) (e.inverse a ha x) := by
  exact limitNoncollapseCylinderReclock_pointMap e a hrange s hs (e.inverse a ha x)

/-- The based identity is an equality of actual sigma points, obtained from
the original right inverse; it is not a matching-map premise, section 6. -/
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

/-- The rebased metric is the original normalized pullback, composed with
the actual top-slice inverse in both differential slots, section 6. -/
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

/-- Curvature is read from the same actual connection at the same sigma
point; rebasing itself makes no further curvature scaling, section 6. -/
theorem limitNoncollapseCylinderRecenter_curvatureNorm (s : ℝ) (hs : s ∈ J)
    (x : (F.slice (origin + a / scale)).carrier) :
    F.curvatureNorm
        ((limitNoncollapseCylinderRecenter e hU a ha hrange V hV).pointMap s hs x) =
      F.curvatureNorm (e.pointMap (a + scale * s) (hrange hs) (e.inverse a ha x)) := by
  rw [limitNoncollapseCylinderRecenter_pointMap]

include e in
/-- Actual cylinder points certify membership in the physical flow interval;
no separate survival hypothesis is needed, reviewed section 6. -/
theorem limitNoncollapseCylinder_time_mem (s : ℝ) (hs : s ∈ I) (x : C.carrier) :
    origin + s / scale ∈ F.interval :=
  (F.slice_nonempty_iff _).mp ⟨e.forward s hs x⟩

end PoincareMT.M47
