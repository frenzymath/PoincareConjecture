import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem isLocallyInjective_of_finite_marked_cells
    {X Y ι κ : Type*} [TopologicalSpace X] [Finite ι]
    {S B : Set X} (P : ι → Set X) (label : ι → κ)
    (T D : κ → Set Y) (g : X → Y)
    (hP : ∀ i, IsClosed (P i)) (hB : IsClosed B)
    (hcover : S ⊆ ⋃ i, P i)
    (hsheets : ∀ i j, i ≠ j → label i = label j → Disjoint (P i) (P j))
    (hmap : ∀ i, MapsTo g (P i) (T (label i)))
    (hboundary : ∀ i, ∀ x ∈ P i, g x ∈ D (label i) ↔ x ∈ B)
    (hfaces : ∀ i j, i ≠ j → T i ∩ T j ⊆ D i)
    (hinj : ∀ i, InjOn g (P i))
    (hboundaryInj : IsLocallyInjective (fun x : B => g x)) :
    IsLocallyInjective (fun x : S => g x) := by
  classical
  intro x
  obtain ⟨U, hU, hxU, hiU⟩ :
      ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧ InjOn g (U ∩ B) := by
    by_cases hxB : (x : X) ∈ B
    · obtain ⟨V, hV, hxV, hiV⟩ := hboundaryInj ⟨x, hxB⟩
      obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hV
      refine ⟨U, hU, hxV, ?_⟩
      intro y hy z hz heq
      exact congrArg Subtype.val (hiV
        (show (⟨y, hy.2⟩ : B) ∈ Subtype.val ⁻¹' U from hy.1)
        (show (⟨z, hz.2⟩ : B) ∈ Subtype.val ⁻¹' U from hz.1) heq)
    · refine ⟨Bᶜ, hB.isOpen_compl, hxB, ?_⟩
      intro y hy
      exact (hy.1 hy.2).elim
  let bad : Set X := ⋃ i : {i : ι // (x : X) ∉ P i}, P i
  have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun i => hP i)
  have hxgood : (x : X) ∉ bad := by
    intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact i.property hi
  have hincident {y : X} (hy : y ∉ bad) {i : ι} (hyi : y ∈ P i) :
      (x : X) ∈ P i := by
    by_contra hxi
    exact hy (mem_iUnion.mpr ⟨⟨i, hxi⟩, hyi⟩)
  refine ⟨Subtype.val ⁻¹' (U ∩ badᶜ),
    (hU.inter hbad.isOpen_compl).preimage continuous_subtype_val,
    ⟨hxU, hxgood⟩, ?_⟩
  intro y hy z hz heq
  change g (y : X) = g (z : X) at heq
  obtain ⟨i, hyi⟩ := mem_iUnion.mp (hcover y.property)
  obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover z.property)
  apply Subtype.ext
  by_cases hij : label i = label j
  · have heqij : i = j := by
      by_contra hne
      exact disjoint_left.mp (hsheets i j hne hij)
        (hincident hy.2 hyi) (hincident hz.2 hzj)
    subst j
    exact hinj i hyi hzj heq
  · have hyB : (y : X) ∈ B := (hboundary i y hyi).mp
      (hfaces (label i) (label j) hij ⟨hmap i hyi, heq.symm ▸ hmap j hzj⟩)
    have hzB : (z : X) ∈ B := (hboundary j z hzj).mp
      (hfaces (label j) (label i) (Ne.symm hij) ⟨hmap j hzj, heq ▸ hmap i hyi⟩)
    exact hiU ⟨hy.1, hyB⟩ ⟨hz.1, hzB⟩ heq

end PoincareConjecture.M76
