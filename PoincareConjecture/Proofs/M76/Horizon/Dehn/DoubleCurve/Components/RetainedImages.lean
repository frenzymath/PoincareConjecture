import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.Dehn

theorem retained_component_preimage
    {E : Type*} [TopologicalSpace E] {K U : Set E} (hUK : U ⊆ K)
    (hc : IsCompact U) (hn : IsConnected U) :
    IsCompact ((Subtype.val : K → E) ⁻¹' U) ∧
      IsConnected ((Subtype.val : K → E) ⁻¹' U) := by
  have hr : (Subtype.val : K → E) '' ((Subtype.val : K → E) ⁻¹' U) = U :=
    image_preimage_eq_iff.mpr (by simpa using hUK)
  refine ⟨IsEmbedding.subtypeVal.isCompact_iff.mpr (hr.symm ▸ hc), ?_⟩
  refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp (hr.symm ▸ hn.isPreconnected)⟩
  obtain ⟨x, hx⟩ := hn.nonempty
  exact ⟨⟨x, hUK hx⟩, hx⟩

theorem retained_component_image_properties
    {E Y I : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {K Q : Set E} {Q' : Set Y} (U : I → Set E) (P : I → Prop)
    (j : K → Y) (hj : Function.Injective j) (hc : Continuous j)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hdisj : Pairwise (fun i l ↦ Disjoint (U i) (U l)))
    (hretain : ∀ i, P i → U i ⊆ K) (hmark : ∀ x : K, j x ∈ Q' ↔ (x : E) ∈ Q) :
    let V (i : {i // P i}) := j '' ((Subtype.val : K → E) ⁻¹' U i.val)
    (∀ i, IsCompact (V i) ∧ IsConnected (V i)) ∧
      Pairwise (fun i l ↦ Disjoint (V i) (V l)) ∧
      (∀ i, (V i ∩ Q').Nonempty ↔ (U i.val ∩ Q).Nonempty) ∧
      (∀ i, Disjoint (V i) Q' ↔ Disjoint (U i.val) Q) := by
  dsimp only
  have hmeet (i : {i // P i}) :
      (j '' ((Subtype.val : K → E) ⁻¹' U i.val) ∩ Q').Nonempty ↔
        (U i.val ∩ Q).Nonempty := by
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hq⟩
      exact ⟨x, hx, (hmark x).mp hq⟩
    · rintro ⟨x, hx, hq⟩
      let xK : K := ⟨x, hretain i.val i.property hx⟩
      exact ⟨j xK, ⟨xK, hx, rfl⟩, (hmark xK).mpr hq⟩
  refine ⟨?_, ?_, hmeet, ?_⟩
  · intro i
    obtain ⟨hcompact', hconn'⟩ := retained_component_preimage
      (hretain i.val i.property) (hcompact i.val) (hconn i.val)
    exact ⟨hcompact'.image hc, hconn'.image _ hc.continuousOn⟩
  · intro i l hil
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy : y = x := hj heq
    subst y
    exact disjoint_left.mp (hdisj (fun h ↦ hil (Subtype.ext h))) hx hy
  · intro i
    rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty,
      ← not_nonempty_iff_eq_empty, ← not_nonempty_iff_eq_empty, hmeet]

end PoincareConjecture.M76.Dehn
