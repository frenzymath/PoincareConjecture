import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderRestriction

/-!
# Restriction of generalized flow cylinders

M12 supplies the actual cylinder restrictions. Here we establish the time
domain consequences needed in the local limiting-flow construction of
Morgan--Tian Claim 10.10, printed p. 255, including at relative endpoints.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

namespace GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- A cylinder with a source point has an actual target slice at every
time in its domain. See Morgan--Tian Definition 9.78, printed p. 232. -/
theorem time_mem_interval (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier) : origin + s / scale ∈ F.interval :=
  (F.slice_nonempty_iff _).mp ⟨e.forward s hs x⟩

end GeneralizedFlowCylinder

/-- A strong neck's own backward cylinder gives included physical times;
no separate earlier canonical certificate is used. See Morgan--Tian
Claim 10.10, printed p. 255. -/
theorem GeneralizedStrongNeck.backward_time_mem
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon)
    {s : ℝ} (hs : s ∈ Set.Ioc (-1 : ℝ) 0) :
    t + s / (N.scale⁻¹ ^ 2) ∈ F.interval :=
  N.time_cylinder.time_mem_interval s hs N.center

/-- A strong neck cannot be centered at an included minimum of the flow
interval, since its backward cylinder contains earlier included times.
See Morgan--Tian Definition 9.78, printed p. 232, and the regular-time
boundary review of 2026-09-18. -/
theorem GeneralizedStrongNeck.not_minimum
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon)
    (hmin : ∀ s ∈ F.interval, t ≤ s) : False := by
  have htime := N.backward_time_mem (s := -(1 / 2 : ℝ)) (by constructor <;> norm_num)
  have hle := hmin _ htime
  have hscale : 0 < N.scale⁻¹ ^ 2 := N.time_cylinder.scale_pos
  have hneg : -(1 / 2 : ℝ) / (N.scale⁻¹ ^ 2) < 0 := div_neg_of_neg_of_pos
    (by norm_num) hscale
  linarith

end PoincareMT
