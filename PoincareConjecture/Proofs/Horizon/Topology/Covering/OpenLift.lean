import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false

open Set Function Filter Topology

variable {X E B : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]

theorem IsLocalHomeomorph.isOpenMap_lift {p : E → B} (hp : IsLocalHomeomorph p)
    {f : X → E} (hf : Continuous f) (hpf : IsOpenMap (p ∘ f)) : IsOpenMap f := by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, rfl⟩ := hp (f x)
  let V := U ∩ f ⁻¹' e.source
  have hV : IsOpen V := hU.inter (e.open_source.preimage hf)
  have hsub : (e ∘ f) '' V ⊆ e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_source hy.2
  have hopen : IsOpen (e.symm '' ((e ∘ f) '' V)) :=
    e.symm.isOpen_image_of_subset_source (hpf V hV) hsub
  have hximage : f x ∈ e.symm '' ((e ∘ f) '' V) := by
    exact ⟨e (f x), ⟨x, ⟨hx, hxe⟩, rfl⟩, e.left_inv hxe⟩
  apply mem_of_superset (hopen.mem_nhds hximage)
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨y, hy.1, (e.left_inv hy.2).symm⟩
