import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Dehn

theorem exists_open_injOn_inter_closed
    {X Y : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    {f : X → Y} (hf : IsLocallyInjective (fun x : A => f x)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f (U ∩ A) := by
  by_cases hx : x ∈ A
  · obtain ⟨V, hV, hxV, hinj⟩ := hf ⟨x, hx⟩
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hV
    refine ⟨U, hU, hxV, ?_⟩
    intro y hy z hz heq
    exact congrArg Subtype.val (hinj (show (⟨y, hy.2⟩ : A) ∈ Subtype.val ⁻¹' U from hy.1)
      (show (⟨z, hz.2⟩ : A) ∈ Subtype.val ⁻¹' U from hz.1) heq)
  · refine ⟨Aᶜ, hA.isOpen_compl, hx, ?_⟩
    intro y hy
    exact (hy.1 hy.2).elim

theorem isLocallyInjective_of_closed_cover
    {X Y : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ)
    {f : X → Y}
    (hfA : IsLocallyInjective (fun x : A => f x))
    (hfB : IsLocallyInjective (fun x : B => f x))
    (hcross : ∀ x ∈ A, ∀ y ∈ B, f x = f y → x = y) :
    IsLocallyInjective f := by
  intro x
  obtain ⟨U, hU, hxU, hiU⟩ := exists_open_injOn_inter_closed hA hfA x
  obtain ⟨V, hV, hxV, hiV⟩ := exists_open_injOn_inter_closed hB hfB x
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  intro y hy z hz heq
  have hycover : y ∈ A ∪ B := hcover.symm ▸ mem_univ y
  have hzcover : z ∈ A ∪ B := hcover.symm ▸ mem_univ z
  rcases hycover with hyA | hyB <;> rcases hzcover with hzA | hzB
  · exact hiU ⟨hy.1, hyA⟩ ⟨hz.1, hzA⟩ heq
  · exact hcross y hyA z hzB heq
  · exact (hcross z hzA y hyB heq.symm).symm
  · exact hiV ⟨hy.2, hyB⟩ ⟨hz.2, hzB⟩ heq

theorem isLocallyInjective_on_closed_union
    {X Y : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) {f : X → Y}
    (hfA : IsLocallyInjective (fun x : A => f x))
    (hfB : IsLocallyInjective (fun x : B => f x))
    (hcross : ∀ x ∈ A, ∀ y ∈ B, f x = f y → x = y) :
    IsLocallyInjective (fun x : ↥(A ∪ B) => f x) := by
  let A' : Set ↥(A ∪ B) := Subtype.val ⁻¹' A
  let B' : Set ↥(A ∪ B) := Subtype.val ⁻¹' B
  have hcover : A' ∪ B' = univ := by
    ext x
    exact iff_true_intro x.property
  apply isLocallyInjective_of_closed_cover
    (hA.preimage continuous_subtype_val) (hB.preimage continuous_subtype_val) hcover
  · let j : A' → A := fun x => ⟨x.1, x.2⟩
    exact hfA.comp_right
      (by fun_prop : Continuous j) (fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : X)) h)))
  · let j : B' → B := fun x => ⟨x.1, x.2⟩
    exact hfB.comp_right
      (by fun_prop : Continuous j) (fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : B => (z : X)) h)))
  · intro x hx y hy heq
    exact Subtype.ext (hcross x hx y hy heq)

theorem isLocallyInjective_on_disjoint_closed_union
    {X Y : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B) {f : X → Y}
    (hfA : IsLocallyInjective (fun x : A => f x))
    (hfB : IsLocallyInjective (fun x : B => f x)) :
    IsLocallyInjective (fun x : ↥(A ∪ B) => f x) := by
  intro x
  rcases x.property with hxA | hxB
  · obtain ⟨U, hU, hxU, hiU⟩ := exists_open_injOn_inter_closed hA hfA x
    refine ⟨Subtype.val ⁻¹' (U ∩ Bᶜ), (hU.inter hB.isOpen_compl).preimage continuous_subtype_val,
      ⟨hxU, Set.disjoint_left.mp hdis hxA⟩, ?_⟩
    intro y hy z hz heq
    exact Subtype.ext (hiU ⟨hy.1, y.property.resolve_right hy.2⟩
      ⟨hz.1, z.property.resolve_right hz.2⟩ heq)
  · obtain ⟨U, hU, hxU, hiU⟩ := exists_open_injOn_inter_closed hB hfB x
    refine ⟨Subtype.val ⁻¹' (U ∩ Aᶜ), (hU.inter hA.isOpen_compl).preimage continuous_subtype_val,
      ⟨hxU, Set.disjoint_right.mp hdis hxB⟩, ?_⟩
    intro y hy z hz heq
    exact Subtype.ext (hiU ⟨hy.1, y.property.resolve_left hy.2⟩
      ⟨hz.1, z.property.resolve_left hz.2⟩ heq)

theorem exists_compact_embedded_neighborhood
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hlocal : IsLocallyInjective f) (x : X) :
    ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x ∧
      Topology.IsEmbedding (fun y : K => f y) := by
  obtain ⟨U, hU, hxU, hiU⟩ := hlocal x
  obtain ⟨K, hxK, hK, hKU⟩ := exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  refine ⟨K, hK.isCompact, hxK, ?_⟩
  exact (hf.comp continuous_subtype_val).isClosedEmbedding
    (fun y z h => Subtype.ext (hiU (hKU y.property) (hKU z.property) h)) |>.isEmbedding

end Dehn
