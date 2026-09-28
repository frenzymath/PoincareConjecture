import PoincareConjecture.Proofs.M38.Components
import PoincareConjecture.Proofs.M38.RegionEquivalences
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (hcount : (F.event T hT).cap_count = 0)

include hcount


theorem zero_cap_retained_clopen : IsClopen (F.event T hT).retained_pre := by
  let : IsEmpty (Fin (F.event T hT).cap_count) := by
    rw [hcount]
    infer_instance
  apply isClopen_iff_frontier_eq_empty.mpr
  simpa using (F.event T hT).pre_boundary


theorem zero_cap_retained_post : (F.event T hT).retained_post = Set.univ := by
  let : IsEmpty (Fin (F.event T hT).cap_count) := by
    rw [hcount]
    infer_instance
  simpa using (F.event T hT).post_cover


theorem zero_cap_component_retained
    {x : (F.slice (F.event T hT).tMinus).carrier}
    (hx : x ∈ (F.event T hT).retained_pre) :
    connectedComponent x ⊆ (F.event T hT).retained_pre :=
  (zero_cap_retained_clopen F T hT hcount).connectedComponent_subset hx


theorem zero_cap_component_discarded
    {x : (F.slice (F.event T hT).tMinus).carrier}
    (hx : x ∉ (F.event T hT).retained_pre) :
    connectedComponent x ⊆ (F.event T hT).retained_preᶜ :=
  (zero_cap_retained_clopen F T hT hcount).compl.connectedComponent_subset hx



theorem zero_cap_component_image
    {x : (F.slice (F.event T hT).tMinus).carrier}
    (hx : x ∈ (F.event T hT).retained_pre) :
    (F.event T hT).retention.map '' connectedComponent x =
      connectedComponent ((F.event T hT).retention.map x) := by
  have hsubset := zero_cap_component_retained F T hT hcount hx
  have hpost (y : (F.slice T).carrier) : y ∈ (F.event T hT).retained_post := by
    rw [zero_cap_retained_post F T hT hcount]
    exact Set.mem_univ y
  have hinverse : Continuous (F.event T hT).retention.inverse := by
    apply continuousOn_univ.mp
    rw [← zero_cap_retained_post F T hT hcount]
    exact (F.event T hT).retention.inverse_smooth.continuousOn
  have hback : (F.event T hT).retention.inverse ''
      connectedComponent ((F.event T hT).retention.map x) ⊆ connectedComponent x := by
    apply (isConnected_connectedComponent.image
      (F.event T hT).retention.inverse hinverse.continuousOn).subset_connectedComponent
    exact ⟨(F.event T hT).retention.map x, mem_connectedComponent,
      (F.event T hT).retention.left_inverse hx⟩
  apply Set.Subset.antisymm
  · apply (isConnected_connectedComponent.image (F.event T hT).retention.map
      ((F.event T hT).retention.map_smooth.continuousOn.mono hsubset)).subset_connectedComponent
    exact Set.mem_image_of_mem _ mem_connectedComponent
  · intro y hy
    exact ⟨(F.event T hT).retention.inverse y,
      hback (Set.mem_image_of_mem _ hy), (F.event T hT).retention.right_inverse (hpost y)⟩


noncomputable def zeroCapComponentRetention
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hx : x ∈ (F.event T hT).retained_pre) :
    SurgeryRegionEquivalence (F.slice (F.event T hT).tMinus) (F.slice T)
      (connectedComponent x) (connectedComponent ((F.event T hT).retention.map x)) where
  map := (F.event T hT).retention.map
  inverse := (F.event T hT).retention.inverse
  map_image := zero_cap_component_image F T hT hcount hx
  inverse_image := by
    rw [← zero_cap_component_image F T hT hcount hx]
    exact (F.event T hT).retention.left_inverse.image_image'
      (zero_cap_component_retained F T hT hcount hx)
  left_inverse := (F.event T hT).retention.left_inverse.mono
    (zero_cap_component_retained F T hT hcount hx)
  right_inverse := by
    intro y _
    apply (F.event T hT).retention.right_inverse
    rw [zero_cap_retained_post F T hT hcount]
    exact Set.mem_univ y
  map_smooth := (F.event T hT).retention.map_smooth.mono
    (zero_cap_component_retained F T hT hcount hx)
  inverse_smooth := (F.event T hT).retention.inverse_smooth.mono (by
    intro y _
    rw [zero_cap_retained_post F T hT hcount]
    exact Set.mem_univ y)



noncomputable def zeroCapSurvivorEquivalence
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hx : x ∈ (F.event T hT).retained_pre) :
    SurgeryRegionEquivalence (componentCarrier (F.slice (F.event T hT).tMinus) x)
      (F.slice T) Set.univ (connectedComponent ((F.event T hT).retention.map x)) :=
  composeRegions (componentRegionEquivalence (F.slice (F.event T hT).tMinus) x)
    (zeroCapComponentRetention F T hT hcount x hx)

end PoincareConjecture.M38
