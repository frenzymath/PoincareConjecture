import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38

variable {A : Type*} [TopologicalSpace A] {O : Set A}
  (hlocal : ∀ z ∈ closure O, ∃ U : Set A,
    IsOpen U ∧ z ∈ U ∧ IsPreconnected (U ∩ O))

theorem local_inter_subset_component {x : A} {U : Set A}
    (hconnected : IsPreconnected (U ∩ O))
    (hmeets : (U ∩ connectedComponentIn O x).Nonempty) :
    U ∩ O ⊆ connectedComponentIn O x := by
  obtain ⟨y, hyU, hyC⟩ := hmeets
  have h := hconnected.subset_connectedComponentIn
    ⟨hyU, connectedComponentIn_subset O x hyC⟩ Set.inter_subset_right
  rwa [← connectedComponentIn_eq hyC] at h

include hlocal

theorem component_closure_clopen (x : A) :
    IsClopen ((Subtype.val : closure O → A) ⁻¹'
      closure (connectedComponentIn O x)) := by
  refine ⟨isClosed_closure.preimage continuous_subtype_val, ?_⟩
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨U, hU, hzU, hconnected⟩ := hlocal z.val z.property
  have hsub := local_inter_subset_component hconnected
    (mem_closure_iff.mp hz U hU hzU)
  have hn : (Subtype.val : closure O → A) ⁻¹' U ∈ 𝓝 z :=
    (hU.preimage continuous_subtype_val).mem_nhds hzU
  filter_upwards [hn] with w hw
  exact closure_mono hsub (hU.inter_closure ⟨hw, w.property⟩)

theorem closure_componentIn_eq (x : A) (hx : x ∈ O) :
    closure (connectedComponentIn O x) = connectedComponentIn (closure O) x := by
  have hsub : closure (connectedComponentIn O x) ⊆ closure O :=
    closure_mono (connectedComponentIn_subset O x)
  apply Set.Subset.antisymm
  · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) hsub
  · have hcc := (component_closure_clopen hlocal x).connectedComponent_subset
      (x := (⟨x, subset_closure hx⟩ : closure O))
      (subset_closure (mem_connectedComponentIn hx))
    rw [connectedComponentIn_eq_image (subset_closure hx)]
    rintro y ⟨z, hz, rfl⟩
    exact hcc hz

theorem exists_component_closure (z : A) (hz : z ∈ closure O) :
    ∃ x ∈ O, closure (connectedComponentIn O x) =
      connectedComponentIn (closure O) z := by
  obtain ⟨U, hU, hzU, hconnected⟩ := hlocal z hz
  obtain ⟨x, hxU, hxO⟩ := mem_closure_iff.mp hz U hU hzU
  have hsub : U ∩ O ⊆ connectedComponentIn O x :=
    hconnected.subset_connectedComponentIn ⟨hxU, hxO⟩ Set.inter_subset_right
  have hzC : z ∈ closure (connectedComponentIn O x) :=
    closure_mono hsub (hU.inter_closure ⟨hzU, hz⟩)
  refine ⟨x, hxO, ?_⟩
  rw [closure_componentIn_eq hlocal x hxO] at hzC ⊢
  exact connectedComponentIn_eq hzC

end PoincareConjecture.M38
