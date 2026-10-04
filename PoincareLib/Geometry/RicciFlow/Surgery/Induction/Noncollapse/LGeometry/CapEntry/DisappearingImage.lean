import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.DisappearingTop
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderClock

/-!
# Excluding the top of the lifted disappearing cap image

Proposition 16.13 and Lemma 16.15, pp. 377-381. The literal map
equality supplied by M33 identifies every point of the lifted cylinder
with the original physical cap trace. The closure exclusion therefore
applies to the same raw image used by the last-entry argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
local notation "GeneralizedFlowCarrierConclusion" => PoincareMT.GeneralizedFlowCarrierConclusionWithInterval

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

/-- Every point of the actual lifted raw cylinder is in the original
physical cap trace, using exactly the M33 forward-map equality. Source:
Proposition 14.12 and Lemma 16.15, pp. 350 and 379-381. -/
theorem rawCylinder_range_subset_history_capTrace
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas G))
    (H : M33RegularHistoryRealization G F)
    {origin scale : ℝ} {I : Set ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (d : GeneralizedFlowCylinder G (F.slice origin) origin scale J.domain U)
    (hJI : J.domain ⊆ I)
    (htime : ∀ s ∈ J.domain, origin + s / scale ∈ G.interval)
    (hforward : ∀ s hs x, x ∈ U →
      H.forward (origin + s / scale) (htime s hs) (d.forward s hs x) =
        e.forward s (hJI hs) x) :
    range (rawCylinderMap R d) ⊆ {z : R.spacetime.Point |
      ∃ (s : ℝ) (hs : s ∈ I) (x : (F.slice origin).carrier), x ∈ U ∧
        (⟨origin + s / scale, e.forward s hs x⟩ : Σ t, (F.slice t).carrier) =
          historyPhysicalPoint H z} := by
  rintro z ⟨w, rfl⟩
  let s := cylinderClockHomeomorph origin scale d.scale_pos J w.1
  refine ⟨s.val, hJI s.property, w.2.val, w.2.property, ?_⟩
  change (⟨origin + s.val / scale, e.forward s.val (hJI s.property) w.2.val⟩ :
      Σ t, (F.slice t).carrier) =
    ⟨origin + s.val / scale,
      H.forward (origin + s.val / scale) _ (d.forward s.val s.property w.2.val)⟩
  exact congrArg (fun x => (⟨origin + s.val / scale, x⟩ : Σ t, (F.slice t).carrier))
    (hforward s.val s.property w.2.val w.2.property).symm

/-- The last-entry point cannot lie at the top of a disappearing
lifted cylinder, even when the raw image is approached only in closure.
Source: Proposition 16.13 and Lemma 16.15, pp. 377-381. -/
theorem rawCylinder_closure_excludes_disappearing_top
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas G))
    (H : M33RegularHistoryRealization G F)
    {origin scale top : ℝ} {I : Set ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (d : GeneralizedFlowCylinder G (F.slice origin) origin scale J.domain U)
    (hJI : J.domain ⊆ I)
    (htime : ∀ s ∈ J.domain, origin + s / scale ∈ G.interval)
    (hforward : ∀ s hs x, x ∈ U →
      H.forward (origin + s / scale) (htime s hs) (d.forward s hs x) =
        e.forward s (hJI hs) x)
    (hdisappears : SurgeryBallDisappearsAt F e top)
    (hbefore : ∀ s ∈ I, origin + s / scale < top)
    (z : R.spacetime.Point) (hz : R.spacetime.timeFunction z = top) :
    z ∉ closure (range (rawCylinderMap R d)) := by
  intro hclosure
  apply disappearingCap_trace_closure_excludes_top R H e hdisappears hbefore z hz
  exact closure_mono (rawCylinder_range_subset_history_capTrace R H e d hJI
    htime hforward) hclosure

end PoincareMT.Proofs.M46
