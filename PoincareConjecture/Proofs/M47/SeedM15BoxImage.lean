import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveHistoryPaths








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem seedM15_component_box_image
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (H : M33RegularHistoryRealization G F)
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {I : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier)
    (hcompact : IsCompact (U : Set C.carrier))
    (hconnected : IsConnected (U : Set C.carrier))
    (e : SurgeryFlowCylinder F C origin scale I U)
    (q : G.box_index) (x : (G.box q).carrier.carrier)
    {p : G.point} (hp : p ∈ componentBoxImage G ⟨q, x⟩)
    {s : ℝ} (hs : s ∈ I) (hclock : p.1 = origin + s / scale)
    (htime : p.1 ∈ G.interval) {z : C.carrier} (hz : z ∈ U)
    (hphysical : HEq (H.forward p.1 htime p.2) (e.forward s hs z)) :
    ∃ ht : origin + s / scale ∈ (G.box q).interval,
      H.forward (origin + s / scale) (m33BoxIntervalSubset G q ht)
        ((G.box q).forward (origin + s / scale) ht x) ∈
          e.forward s hs '' (U : Set C.carrier) := by
  obtain ⟨⟨⟨t, ht⟩, y⟩, ⟨_, hy⟩, rfl⟩ := hp
  change t = origin + s / scale at hclock
  subst t
  have hxy : x ∈ connectedComponent y := by
    rw [← connectedComponent_eq hy]
    exact mem_connectedComponent
  have hcont := (H.forward_smooth _ (m33BoxIntervalSubset G q ht)).continuous.comp
    ((G.box q).forward_smooth _ ht).continuous
  have hcomponent := hcont.image_connectedComponent_subset y
    (mem_image_of_mem (H.forward _ (m33BoxIntervalSubset G q ht) ∘
      (G.box q).forward _ ht) hxy)
  change H.forward _ (m33BoxIntervalSubset G q ht) ((G.box q).forward _ ht x) ∈
    connectedComponent (H.forward _ (m33BoxIntervalSubset G q ht)
      ((G.box q).forward _ ht y)) at hcomponent
  have heq : H.forward _ (m33BoxIntervalSubset G q ht) ((G.box q).forward _ ht y) =
      e.forward s hs z := eq_of_heq hphysical
  rw [heq, ← component_cylinder_image_eq e U.isOpen hcompact hconnected s hs hz] at hcomponent
  exact ⟨ht, hcomponent⟩

end PoincareConjecture.M47
