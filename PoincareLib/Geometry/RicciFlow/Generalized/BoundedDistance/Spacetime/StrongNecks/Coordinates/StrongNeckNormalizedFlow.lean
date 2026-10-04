import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.Cylinders.CylinderRescaling
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.Cylinders.CylinderRestriction
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity

/-!
# The ordinary rescaled flow carried by one strong neck

The backward cylinder of a `GeneralizedStrongNeck` has an actual physical
time inclusion.  This file discharges the interval obligation of the M12/M13
cylinder producer directly from that cylinder, without assuming a partial
limit or a target neck.  The resulting flow still has the lower endpoint
convention of the strong-neck cylinder (`Ioc (-1, 0)`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

/-! The interval used by the strong-neck cylinder in `GeneralizedStrongNeck`. -/
def strongNeckBackwardInterval : SpacetimeInterval where
  domain := Ioc (-1 : ℝ) 0
  ordConnected := ordConnected_Ioc
  nontrivial := by
    refine ⟨-(1 / 2 : ℝ), ?_, 0, ?_, ?_⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, le_rfl⟩
    · norm_num

def strongNeckCylinder
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    GeneralizedFlowCylinder F (F.slice t) t (S.scale⁻¹ ^ 2)
      strongNeckBackwardInterval.domain S.carrier := by
  simpa [strongNeckBackwardInterval] using S.time_cylinder

theorem GeneralizedStrongNeck.physical_interval_subset
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    (Proofs.M12.cylinderPhysicalInterval t (S.scale⁻¹ ^ 2)
      S.time_cylinder.scale_pos strongNeckBackwardInterval).domain ⊆ F.interval := by
  intro s hs
  rcases hs with ⟨r, hr, rfl⟩
  simpa only [parabolicTimeInv] using S.backward_time_mem hr

theorem GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    let U : TopologicalSpace.Opens (F.slice t).carrier :=
      ⟨S.carrier, S.carrier_open⟩
    Nonempty (RescaledRawCylinderData (C := F.slice t) (U := U)
      (J := strongNeckBackwardInterval) (strongNeckCylinder S)
        (physical_interval_subset S)) := by
  let U : TopologicalSpace.Opens (F.slice t).carrier :=
    ⟨S.carrier, S.carrier_open⟩
  change Nonempty (RescaledRawCylinderData (C := F.slice t) (U := U)
    (J := strongNeckBackwardInterval) (strongNeckCylinder S)
      (physical_interval_subset S))
  exact PoincareMT.M28.exists_rescaled_raw_cylinder_flow
    (C := F.slice t) (U := U) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (physical_interval_subset S)

theorem GeneralizedStrongNeck.exists_rescaled_half_flow
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    let U : TopologicalSpace.Opens (F.slice t).carrier :=
      ⟨S.carrier, S.carrier_open⟩
    Nonempty (RicciFlow 3 U (Set.Icc (-(1 / 2 : ℝ)) 0)) := by
  let U : TopologicalSpace.Opens (F.slice t).carrier :=
    ⟨S.carrier, S.carrier_open⟩
  obtain ⟨H⟩ :=
    PoincareMT.M28.GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow S
  let q : ℝ := S.scale⁻¹ ^ 2
  have hq : 0 < q := by
    dsimp [q]
    exact sq_pos_of_pos (inv_pos.mpr S.scale_pos)
  let K := Proofs.M12.cylinderPhysicalInterval t q
    S.time_cylinder.scale_pos strongNeckBackwardInterval
  have hsub : Set.Icc (-(1 / 2 : ℝ)) 0 ⊆
      (parabolicInterval q hq t K).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff q hq t K s).2
    refine ⟨s, ?_, rfl⟩
    exact ⟨by linarith [hs.1], hs.2⟩
  refine ⟨Poincare.Geometry.RicciFlow.Harnack.restrictFlow H.rescaling.flow
    hsub ordConnected_Icc ?_⟩
  exact ⟨-(1 / 2 : ℝ), by norm_num, 0, by norm_num, by norm_num⟩

end PoincareMT.M28
