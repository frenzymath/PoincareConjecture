import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem eq_of_finite_fiber_common_connected_side
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {y : Y} (hfinite : (f ⁻¹' {y}).Finite)
    {a b : X} (_ha : f a = y) (hb : f b = y)
    (hside : ∀ V : Set Y, IsOpen V → y ∈ V →
      ∃ C : Set X, IsPreconnected C ∧ C ⊆ f ⁻¹' V ∧ a ∈ closure C ∧ b ∈ closure C) :
    a = b := by
  classical
  by_contra hab
  have hclosed : IsClosed ((f ⁻¹' {y}) \ {a}) := hfinite.sdiff.isClosed
  have haopen : ({a} : Set X) ⊆ ((f ⁻¹' {y}) \ {a})ᶜ := by
    rintro x rfl
    exact fun hx => hx.2 rfl
  obtain ⟨U,hU,haU,hUc⟩ := normal_exists_closure_subset isClosed_singleton hclosed.isOpen_compl haopen
  have haU' : a ∈ U := haU (mem_singleton a)
  have hbUc : b ∉ closure U := by
    intro h
    exact hUc h ⟨hb,fun he => hab he.symm⟩
  have hfront : ∀ x ∈ frontier U, f x ≠ y := by
    intro x hx hxy
    by_cases hxa : x = a
    · subst x
      exact hx.2 (hU.interior_eq.symm ▸ haU')
    · exact hUc (frontier_subset_closure hx) ⟨hxy,hxa⟩
  let V := (f '' frontier U)ᶜ
  have hV : IsOpen V := (hf.isClosedMap _ isClosed_frontier).isOpen_compl
  have hyV : y ∈ V := by
    rintro ⟨x,hx,he⟩
    exact hfront x hx he
  obtain ⟨C,hC,hCV,haC,hbC⟩ := hside V hV hyV
  have hsep : C ∩ (closure U ∩ Uᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hxc,hxu⟩
    have hxf : x ∈ frontier U := ⟨hxc,by
      change x ∉ U at hxu
      rw [hU.interior_eq]
      exact hxu⟩
    exact hCV hx ⟨x,hxf,rfl⟩
  have hcover : C ⊆ closure U ∪ Uᶜ := by
    intro x _
    by_cases hx : x ∈ U
    · exact Or.inl (subset_closure hx)
    · exact Or.inr hx
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC
    (closure U) Uᶜ isClosed_closure hU.isClosed_compl hcover hsep with hc | hc
  · exact hbUc ((closure_minimal hc isClosed_closure) hbC)
  · exact (closure_minimal hc hU.isClosed_compl haC) haU'

end PoincareConjecture.M76.PrismBelt
