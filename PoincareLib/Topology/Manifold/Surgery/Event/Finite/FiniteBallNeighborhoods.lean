import Mathlib.Topology.Separation.Hausdorff

/-!
# Neighborhoods separated from finitely many compact images

Before descending an innermost filled ball through a finite covering,
its full coordinate neighborhood must avoid the nonidentity translates.
Compact Hausdorff separation and a finite intersection supply that
neighborhood without altering the ball itself.
-/

set_option autoImplicit false

open Set Topology

namespace PoincareMT.M38

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A compact set disjoint from its continuous image has an open
neighborhood still disjoint from its own image under the same map. -/
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

/-- A single open neighborhood works for every map in a finite family.
The maps need only be continuous; the later covering application supplies
the actual complete list of nontrivial fiber transformations. -/
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

end PoincareMT.M38
