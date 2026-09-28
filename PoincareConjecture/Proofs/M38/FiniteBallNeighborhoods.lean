import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem exists_open_disjoint_image_of_compact {K : Set X}
    (hK : IsCompact K) (f : X → X) (hf : Continuous f)
    (hdisjoint : Disjoint K (f '' K)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ Disjoint U (f '' U) := by
  obtain ⟨U, V, hU, hV, hKU, hfKV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hK (hK.image hf) hdisjoint
  refine ⟨U ∩ f ⁻¹' V, hU.inter (hV.preimage hf), ?_, ?_⟩
  · intro x hx
    exact ⟨hKU hx, hfKV (Set.mem_image_of_mem _ hx)⟩
  · apply Set.disjoint_left.mpr
    rintro _ hx ⟨y, hy, rfl⟩
    exact Set.disjoint_left.mp hUV hx.1 hy.2

theorem exists_open_disjoint_finite_images_of_compact
    {I : Type*} [Finite I] {K : Set X} (hK : IsCompact K)
    (f : I → X → X) (hf : ∀ i, Continuous (f i))
    (hdisjoint : ∀ i, Disjoint K (f i '' K)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ ∀ i, Disjoint U (f i '' U) := by
  choose U hU hKU hsep using fun i =>
    exists_open_disjoint_image_of_compact hK (f i) (hf i) (hdisjoint i)
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, ?_, ?_⟩
  · intro x hx
    exact Set.mem_iInter.mpr (fun i => hKU i hx)
  · intro i
    exact (hsep i).mono (Set.iInter_subset U i) (Set.image_mono (Set.iInter_subset U i))

end PoincareConjecture.M38
