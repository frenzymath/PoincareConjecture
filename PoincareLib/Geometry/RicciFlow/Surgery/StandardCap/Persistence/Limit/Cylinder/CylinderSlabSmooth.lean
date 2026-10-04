import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.CylinderTimeCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.WithinRicciEquation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Coordinates.ClosedTimeJets

/-!
# Actual cylinder Ricci smoothness on ordinary slabs

The fixed reference chart identifies physical-time coefficients
with the ordinary slab flow, including within-time endpoints.
Morgan--Tian, Lemma 16.8, pp. 372-373;
see M44 derivation 62.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- The physical-time coefficients of an actual cylinder are
jointly smooth and solve Ricci flow on every ordinary slab.
Source: Lemma 16.8, pp. 372-373; M44 derivation 62. -/
theorem cylinderTimeCoefficients_slab_smooth_ricci
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U)
    (r0 : ℝ) (hr0 : r0 ∈ I)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc a b))
    (r : ℝ) (hr : r ∈ I) (hr' : origin + r / scale ∈ Icc a b)
    {J : Set ℝ} (hJI : ∀ t ∈ J, scale * (t - origin) ∈ I)
    (hJslab : J ⊆ Icc a b) :
    ContDiffOn ℝ ∞ (cylinderTimeCoefficients e f r0 hr0) (J ×ˢ f.source) ∧
      ∀ t ∈ J, ∀ x ∈ f.source,
        HasDerivWithinAt (fun s => cylinderTimeCoefficients e f r0 hr0 (s, x))
          (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
            (fun y => cylinderTimeCoefficients e f r0 hr0 (t, y)) x)) J t := by
  let S := F.regular_slabs a b hab hJ hNo
  let A := (S.identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f
  have hfmap : MapsTo f f.source U := fun _ hx => hmap (f.map_source hx)
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A f.source :=
    (S.identify ⟨origin + r / scale, hr'⟩).symm.contMDiff.comp_contMDiffOn
      ((e.forward_smooth r hr).comp f.contMDiffOn hfmap)
  have hi : ∀ x ∈ f.source, (mfderiv (𝓡 3) (𝓡 3) A x).IsInvertible := by
    intro x hx
    let d := (f.trans (cylinderSliceChart e hU r hr)).trans
      (S.identify ⟨origin + r / scale, hr'⟩).symm.toPartialDiffeomorph
    have hxd : x ∈ d.source := ⟨⟨hx, hfmap hx⟩, mem_univ _⟩
    exact ⟨(d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxd).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  have heq (t : ℝ) (ht : t ∈ J) (x : E) (hx : x ∈ f.source) :
      cylinderTimeCoefficients e f r0 hr0 (t, x) =
        (S.flow.metric t).pullbackCoefficients A x :=
    cylinderTimeCoefficients_eq_slab e f.open_source f.contMDiffOn hfmap r0 hr0
      hab hJ hNo r hr hr' (hJI t ht) (hJslab ht) hx
  refine ⟨?_, ?_⟩
  · exact ((contDiffOn_pullbackCoefficients_within S.flow f.open_source hA).mono
      (prod_mono hJslab Subset.rfl)).congr (fun p hp => heq p.1 hp.1 p.2 hp.2)
  · intro t ht x hx
    have hgerm : (fun y => cylinderTimeCoefficients e f r0 hr0 (t, y)) =ᶠ[𝓝 x]
        (S.flow.metric t).pullbackCoefficients A := by
      filter_upwards [f.open_source.mem_nhds hx] with y hy
      exact heq t ht y hy
    rw [SpacetimeBounds.metricTwoJet_congr_of_eventuallyEq hgerm]
    exact (hasDerivWithinAt_pullbackCoefficients_ricci S.flow f.open_source hA hi
      (hJslab ht) hx).congr_mono (fun s hs => heq s hs x hx) (heq t ht x hx) hJslab

end PoincareMT.M44
