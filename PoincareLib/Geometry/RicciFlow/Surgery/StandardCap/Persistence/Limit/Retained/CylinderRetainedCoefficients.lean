import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.CylinderSlabCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.CoefficientTransport

/-!
# The actual cylinder metric after a retained event

The future ordinary slab pulls back through exactly the retention
map of the fixed preterminal reference chart, also at surgery.
Morgan--Tian, Proposition 16.5, pp. 374-375; see derivation 60.
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

/-- The actual post-event cylinder metric is the future flow
pulled through the primitive retention of the fixed preterminal
reference map. Source: Proposition 16.5, pp. 374-375;
M44 derivation 60. -/
theorem cylinderPhysicalCoefficients_eq_retained
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    (c : ℝ) (hc : c ∈ I) (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    {b : ℝ} (hTb : origin + c / scale < b)
    (hJ : Icc (origin + c / scale) b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc (origin + c / scale) b))
    (s : ℝ) (hs : s ∈ I) (hs' : origin + s / scale ∈ Icc (origin + c / scale) b)
    {x : E} (hx : x ∈ V) :
    cylinderPhysicalCoefficients e f s hs x =
      ((F.regular_slabs (origin + c / scale) b hTb hJ hNo).flow.metric
        (origin + s / scale)).pullbackCoefficients
          ((F.event (origin + c / scale) hT).retention.map ∘
            ((F.event (origin + c / scale) hT).pre_identify
              ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f) x := by
  let S := F.regular_slabs (origin + c / scale) b hTb hJ hNo
  have hc' : origin + c / scale ∈ Icc (origin + c / scale) b := ⟨le_rfl, hTb.le⟩
  rw [cylinderPhysicalCoefficients_eq_slab e hV hf hmap hTb hJ hNo c hc hc' s hs hs' hx]
  apply pullbackCoefficients_congr_of_eventuallyEq
  have hinit (y : (F.slice (origin + c / scale)).carrier) :
      (S.identify ⟨origin + c / scale, hc'⟩).symm y = y := by
    have h := S.initial_identify ((S.identify ⟨origin + c / scale, hc'⟩).symm y)
    rw [Diffeomorph.apply_symm_apply] at h
    exact h.symm
  filter_upwards [hV.mem_nhds hx] with y hy
  change (S.identify ⟨origin + c / scale, hc'⟩).symm (e.forward c hc (f y)) = _
  rw [hinit]
  exact (e.surgery_compatibility c hc hT r hr hr' (f y) (hmap hy)).symm

end PoincareMT.M44
