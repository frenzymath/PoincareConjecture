import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_DisappearingTop
import PoincareConjecture.Proofs.M12.GeneralizedCylinderClock










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12




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

end PoincareConjecture.Proofs.M46
