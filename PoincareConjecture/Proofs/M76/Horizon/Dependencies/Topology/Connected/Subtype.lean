import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem subtype_image_connectedComponentIn
    {X : Type*} [TopologicalSpace X] {W A : Set X} (hAW : A ⊆ W)
    (p : W) (hp : p.val ∈ A) :
    Subtype.val '' connectedComponentIn ((Subtype.val : W → X) ⁻¹' A) p =
      connectedComponentIn A p.val := by
  let C := connectedComponentIn A p.val
  have hCW : C ⊆ W := (connectedComponentIn_subset _ _).trans hAW
  have hpreimage : Subtype.val '' ((Subtype.val : W → X) ⁻¹' C) = C := by
    apply image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x, hCW hx⟩, rfl⟩
  have hpre : IsPreconnected ((Subtype.val : W → X) ⁻¹' C) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hpreimage]
    exact isPreconnected_connectedComponentIn
  apply subset_antisymm
  · apply (isPreconnected_connectedComponentIn.image Subtype.val
      continuous_subtype_val.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem Subtype.val (mem_connectedComponentIn hp))
    rintro _ ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset ((Subtype.val : W → X) ⁻¹' A) p hx
  · intro x hx
    refine ⟨⟨x, hCW hx⟩, ?_, rfl⟩
    exact hpre.subset_connectedComponentIn (mem_connectedComponentIn hp)
      (fun y hy => connectedComponentIn_subset A p.val hy) hx

end Poincare.Topology
