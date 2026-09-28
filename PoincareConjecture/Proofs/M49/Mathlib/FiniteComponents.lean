import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Sum

set_option autoImplicit false

open Set
open scoped Topology

universe u v

variable {X : Type u} [TopologicalSpace X]

section LocallyConnected

variable [LocallyConnectedSpace X]

theorem IsClosed.connectedComponentIn_eq_of_disjoint_frontier
    {R : Set X} (hR : IsClosed R) {x : X} (hx : x ∈ R)
    (hd : Disjoint (connectedComponentIn R x) (frontier R)) :
    connectedComponentIn R x = connectedComponent x := by
  have hclosed : IsClosed (connectedComponentIn R x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hR.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hinterior : connectedComponentIn R x ⊆ interior R := by
    intro y hy
    apply (mem_interior_iff_notMem_frontier (connectedComponentIn_subset R x hy)).mpr
    exact fun hf => disjoint_left.mp hd hy hf
  have hopen : IsOpen (connectedComponentIn R x) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [connectedComponentIn_eq hy]
    exact connectedComponentIn_mem_nhds (mem_interior_iff_mem_nhds.mp (hinterior hy))
  have hclopen : IsClopen (connectedComponentIn R x) := ⟨hclosed, hopen⟩
  exact (isPreconnected_connectedComponentIn.subset_connectedComponent
    (mem_connectedComponentIn hx)).antisymm
      (hclopen.connectedComponent_subset (mem_connectedComponentIn hx))

noncomputable def IsClosed.connectedComponentsEmbeddingOfFrontierCover
    {ι : Type v} {R : Set X} (hR : IsClosed R) (B : ι → Set X)
    (hB : ∀ i, IsPreconnected (B i)) (hBR : ∀ i, B i ⊆ R)
    (hfrontier : frontier R ⊆ ⋃ i, B i) :
    ConnectedComponents R ↪ (ConnectedComponents X ⊕ ι) := by
  classical
  let p : ConnectedComponents R → R := fun c =>
    (ConnectedComponents.surjective_coe c).choose
  have hp (c : ConnectedComponents R) : ConnectedComponents.mk (p c) = c :=
    (ConnectedComponents.surjective_coe c).choose_spec
  let C (c : ConnectedComponents R) : Set X := connectedComponentIn R (p c).val
  have hCeq {c d : ConnectedComponents R} (h : C c = C d) : c = d := by
    have hsub : connectedComponent (p c) = connectedComponent (p d) := by
      apply Set.image_val_inj.mp
      simpa only [C, connectedComponentIn_eq_image (p c).property,
        connectedComponentIn_eq_image (p d).property] using h
    exact (hp c).symm.trans ((ConnectedComponents.coe_eq_coe.mpr hsub).trans (hp d))
  let hit (c : ConnectedComponents R) : Prop := ∃ i, (C c ∩ B i).Nonempty
  have hwhole {c : ConnectedComponents R} (hc : ¬hit c) :
      C c = connectedComponent (p c).val := by
    apply hR.connectedComponentIn_eq_of_disjoint_frontier (p c).property
    apply disjoint_left.mpr
    intro x hxC hxF
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hfrontier hxF)
    exact hc ⟨i, x, hxC, hxi⟩
  let f (c : ConnectedComponents R) : ConnectedComponents X ⊕ ι :=
    if hc : hit c then Sum.inr hc.choose else Sum.inl (ConnectedComponents.mk (p c).val)
  refine ⟨f, ?_⟩
  intro c d hcd
  by_cases hc : hit c
  · by_cases hd : hit d
    · have hij : hc.choose = hd.choose := by
        simpa only [f, dif_pos hc, dif_pos hd, Sum.inr.injEq] using hcd
      obtain ⟨x, hxC, hxB⟩ := hc.choose_spec
      obtain ⟨y, hyC, hyB⟩ := hd.choose_spec
      have hBD : B hd.choose ⊆ C d := by
        have hsub := (hB hd.choose).subset_connectedComponentIn hyB (hBR hd.choose)
        rw [← connectedComponentIn_eq hyC] at hsub
        exact hsub
      have hxD : x ∈ C d := hBD (hij ▸ hxB)
      exact hCeq ((connectedComponentIn_eq hxC).trans (connectedComponentIn_eq hxD).symm)
    · simp [f, hc, hd] at hcd
  · by_cases hd : hit d
    · simp [f, hc, hd] at hcd
    · have hxy : ConnectedComponents.mk (p c).val = ConnectedComponents.mk (p d).val := by
        simpa only [f, dif_neg hc, dif_neg hd, Sum.inl.injEq] using hcd
      apply hCeq
      rw [hwhole hc, hwhole hd]
      exact ConnectedComponents.coe_eq_coe.mp hxy

theorem IsClosed.finite_connectedComponents_of_frontier_cover
    {ι : Type v} [Finite (ConnectedComponents X)] [Finite ι]
    {R : Set X} (hR : IsClosed R) (B : ι → Set X)
    (hB : ∀ i, IsPreconnected (B i)) (hBR : ∀ i, B i ⊆ R)
    (hfrontier : frontier R ⊆ ⋃ i, B i) : Finite (ConnectedComponents R) := by
  let e := hR.connectedComponentsEmbeddingOfFrontierCover B hB hBR hfrontier
  exact Finite.of_injective e e.injective

theorem IsClosed.card_connectedComponents_le_of_frontier_cover
    {ι : Type v} [Finite (ConnectedComponents X)] [Finite ι]
    {R : Set X} (hR : IsClosed R) (B : ι → Set X)
    (hB : ∀ i, IsPreconnected (B i)) (hBR : ∀ i, B i ⊆ R)
    (hfrontier : frontier R ⊆ ⋃ i, B i) :
    Nat.card (ConnectedComponents R) ≤ Nat.card (ConnectedComponents X) + Nat.card ι := by
  let e := hR.connectedComponentsEmbeddingOfFrontierCover B hB hBR hfrontier
  simpa only [Nat.card_sum] using Nat.card_le_card_of_injective e e.injective

end LocallyConnected

theorem IsClopen.connectedComponentsMap_injective {R : Set X} (hR : IsClopen R) :
    Function.Injective
      (continuous_subtype_val : Continuous (Subtype.val : R → X)).connectedComponentsMap := by
  intro c d hcd
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe d
  change ConnectedComponents.mk p.val = ConnectedComponents.mk q.val at hcd
  apply ConnectedComponents.coe_eq_coe.mpr
  apply Set.image_val_inj.mp
  rw [← connectedComponentIn_eq_image p.property, ← connectedComponentIn_eq_image q.property,
    hR.connectedComponentIn_eq p.property, hR.connectedComponentIn_eq q.property]
  exact ConnectedComponents.coe_eq_coe.mp hcd

theorem IsClopen.card_connectedComponents_lt_of_component_omitted
    [Finite (ConnectedComponents X)] {R : Set X} (hR : IsClopen R) (x : X)
    (hx : connectedComponent x ⊆ Rᶜ) :
    Nat.card (ConnectedComponents R) < Nat.card (ConnectedComponents X) := by
  classical
  let f := (continuous_subtype_val : Continuous (Subtype.val : R → X)).connectedComponentsMap
  have hf : Function.Injective f := hR.connectedComponentsMap_injective
  let : Finite (ConnectedComponents R) := Finite.of_injective f hf
  let : Fintype (ConnectedComponents R) := Fintype.ofFinite _
  let : Fintype (ConnectedComponents X) := Fintype.ofFinite _
  have hmissing : ConnectedComponents.mk x ∉ Set.range f := by
    rintro ⟨c, hc⟩
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk p.val = ConnectedComponents.mk x at hc
    exact hx (ConnectedComponents.coe_eq_coe'.mp hc) p.property
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem f hf hmissing
