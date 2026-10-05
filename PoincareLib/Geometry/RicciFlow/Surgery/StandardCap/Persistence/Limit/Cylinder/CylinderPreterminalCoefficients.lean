import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.CoefficientTransport
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Cylinder.CylinderCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.Stopping.PreterminalTransport

/-!
# The exact preterminal metric of a tracked cylinder

Constant preterminal coordinates identify the cylinder's actual
metric with the event's preterminal ordinary flow in one fixed
reference chart. Morgan--Tian, Proposition 16.5, pp. 374-375;
see derivation 60.
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

/-- The actual cylinder metric equals the preterminal ordinary
metric pulled through its fixed reference map. Source:
Proposition 16.5, pp. 374-375; M44 derivation 60. -/
theorem cylinderPhysicalCoefficients_eq_preterminal
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (hfree : Disjoint F.surgery_times (Ioo (F.event T hT).tMinus T))
    (r : ℝ) (hr : r ∈ I) (hr' : origin + r / scale ∈ Ico (F.event T hT).tMinus T)
    (s : ℝ) (hs : s ∈ I) (hs' : origin + s / scale ∈ Ico (F.event T hT).tMinus T)
    {x : E} (hx : x ∈ V) :
    cylinderPhysicalCoefficients e f s hs x =
      ((F.event T hT).pre_flow.metric (origin + s / scale)).pullbackCoefficients
        (((F.event T hT).pre_identify ⟨origin + r / scale, hr'⟩).symm ∘
          e.forward r hr ∘ f) x := by
  let event := F.event T hT
  let A := (event.pre_identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V :=
    (event.pre_identify ⟨origin + r / scale, hr'⟩).symm.contMDiff.comp_contMDiffOn
      ((e.forward_smooth r hr).comp hf hmap)
  have heq : e.forward s hs ∘ f =ᶠ[𝓝 x]
      (event.pre_identify ⟨origin + s / scale, hs'⟩) ∘ A := by
    filter_upwards [hV.mem_nhds hx] with y hy
    have h := cylinder_preterminal_coordinates_eq e hT hfree s hs r hr hs' hr' (f y) (hmap hy)
    have hh := congrArg (event.pre_identify ⟨origin + s / scale, hs'⟩) h
    simpa only [A, event, Function.comp_def, Diffeomorph.apply_symm_apply] using hh
  exact pullbackCoefficients_eq_of_metric_germ _ _
    ((event.pre_identify ⟨origin + s / scale, hs'⟩).contMDiff.mdifferentiable (by simp) (A x))
    ((hA.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp)) heq
    (event.pre_metric ⟨origin + s / scale, hs'⟩ (A x))

end PoincareMT.M44
