import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

open Set

namespace Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_components_homeomorph_closed_attachment {P D : Set X}
    (hP : IsClosed P) (hD : IsClosed D) (hDc : IsConnected D)
    (hPD : IsConnected (P ∩ D)) :
    ∃ H : ConnectedComponents P ≃ₜ ConnectedComponents (P ∪ D : Set X),
      ∀ x : P, H (ConnectedComponents.mk x) =
        ConnectedComponents.mk (⟨x, Or.inl x.property⟩ : (P ∪ D : Set X)) := by
  classical
  let W := P ∪ D
  obtain ⟨b, hbP, hbD⟩ := hPD.nonempty
  let bP : P := ⟨b, hbP⟩
  let inc : P → W := fun x => ⟨x, Or.inl x.property⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  have hpre : IsPreconnected ((Subtype.val : P → X) ⁻¹' (P ∩ D)) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range, Subtype.range_val,
      inter_eq_left.mpr inter_subset_left]
    exact hPD.isPreconnected
  have hmark (x : P) (hx : (x : X) ∈ D) :
      ConnectedComponents.mk x = ConnectedComponents.mk bP := by
    apply ConnectedComponents.coe_eq_coe'.mpr
    exact hpre.subset_connectedComponent (show bP ∈
      (Subtype.val : P → X) ⁻¹' (P ∩ D) from ⟨hbP, hbD⟩) ⟨x.property, hx⟩
  let label : W → ConnectedComponents P := fun x =>
    if hx : (x : X) ∈ P then ConnectedComponents.mk (⟨x, hx⟩ : P)
    else ConnectedComponents.mk bP
  have hlabelP (x : P) : label (inc x) = ConnectedComponents.mk x := by
    dsimp only [label, inc]
    rw [dif_pos x.property]
  have hlabelD (x : W) (hx : (x : X) ∈ D) :
      label x = ConnectedComponents.mk bP := by
    dsimp only [label]
    split_ifs with hxP
    · exact hmark ⟨x, hxP⟩ hx
    · rfl
  have hlP : ContinuousOn label ((Subtype.val : W → X) ⁻¹' P) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let a : ((Subtype.val : W → X) ⁻¹' P) → P := fun x => ⟨x.val, x.property⟩
    have ha : Continuous a :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    apply (ConnectedComponents.continuous_coe.comp ha).congr
    intro x
    exact (hlabelP (a x)).symm
  have hlD : ContinuousOn label ((Subtype.val : W → X) ⁻¹' D) :=
    continuousOn_const.congr (fun x hx => hlabelD x hx)
  have hl : Continuous label := by
    have h := hlP.union_of_isClosed hlD (hP.preimage continuous_subtype_val)
      (hD.preimage continuous_subtype_val)
    have hcover : ((Subtype.val : W → X) ⁻¹' P) ∪
        ((Subtype.val : W → X) ⁻¹' D) = univ := by
      ext x
      simp only [mem_union, mem_preimage, mem_univ, iff_true]
      exact x.property
    rw [hcover] at h
    exact continuousOn_univ.mp h
  let M := hinc.connectedComponentsMap
  let R := hl.connectedComponentsLift
  have hleft : Function.LeftInverse R M := by
    intro z
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
    exact hlabelP x
  have hpreD : IsPreconnected ((Subtype.val : W → X) ⁻¹' D) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range, Subtype.range_val,
      inter_eq_left.mpr (show D ⊆ W from subset_union_right)]
    exact hDc.isPreconnected
  have hsurj : Function.Surjective M := by
    intro z
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
    rcases x.property with hxP | hxD
    · exact ⟨ConnectedComponents.mk (⟨x, hxP⟩ : P), rfl⟩
    · refine ⟨ConnectedComponents.mk bP, ?_⟩
      change ConnectedComponents.mk (inc bP) = ConnectedComponents.mk x
      apply Eq.symm
      apply ConnectedComponents.coe_eq_coe'.mpr
      exact hpreD.subset_connectedComponent (show inc bP ∈
        (Subtype.val : W → X) ⁻¹' D from hbD) hxD
  have hright : Function.RightInverse R M := by
    intro z
    obtain ⟨x, rfl⟩ := hsurj z
    rw [hleft]
  refine ⟨{
    toFun := M
    invFun := R
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hinc.connectedComponentsMap_continuous
    continuous_invFun := hl.connectedComponentsLift_continuous }, fun _ => rfl⟩

end Topology
