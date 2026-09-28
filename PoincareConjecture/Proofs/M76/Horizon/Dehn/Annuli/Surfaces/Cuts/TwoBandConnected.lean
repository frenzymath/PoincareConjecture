import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.TwoBandSelection
import Mathlib.Topology.Connected.Clopen



set_option autoImplicit false
open Set Relation

namespace PoincareConjecture.M76.Dehn.Annuli

private theorem transGen_of_finite_closed_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι] (S : ι → Set X)
    (hc : IsPreconnected (⋃ i, S i)) (hclosed : ∀ i, IsClosed (S i))
    (i j : ι) (hi : (S i).Nonempty) (hj : (S j).Nonempty) :
    TransGen (fun a b ↦ (S a ∩ S b).Nonempty) i j := by
  classical
  by_contra hnot
  let P := fun k ↦ TransGen (fun a b ↦ (S a ∩ S b).Nonempty) i k
  let U := ⋃ k : {k // P k}, S k.val
  let V := ⋃ k : {k // ¬ P k}, S k.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun k ↦ hclosed k.val)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k ↦ hclosed k.val)
  have hcover : (⋃ k, S k) ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hp : P k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, hp⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hp⟩, hk⟩)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hip : P i := TransGen.single ⟨a, ha, ha⟩
  have hUne : ((⋃ k, S k) ∩ U).Nonempty :=
    ⟨a, mem_iUnion.mpr ⟨i, ha⟩, mem_iUnion.mpr ⟨⟨i, hip⟩, ha⟩⟩
  have hVne : ((⋃ k, S k) ∩ V).Nonempty :=
    ⟨b, mem_iUnion.mpr ⟨j, hb⟩, mem_iUnion.mpr ⟨⟨j, hnot⟩, hb⟩⟩
  obtain ⟨x, _, hxU, hxV⟩ := (isPreconnected_closed_iff.mp hc) U V hU hV hcover hUne hVne
  obtain ⟨k, hk⟩ := mem_iUnion.mp hxU
  obtain ⟨l, hl⟩ := mem_iUnion.mp hxV
  exact l.property (k.property.tail ⟨x, hk, hl⟩)




theorem twoBandGraph_connected_of_closed_cover
    {X C : Type*} [TopologicalSpace X] [Finite C]
    (D : C → Set X) (N : Bool → Set X) (r : Bool → Bool → C)
    (hD : ∀ i, IsClosed (D i)) (hN : ∀ b, IsClosed (N b))
    (hne : ∀ i, (D i).Nonempty)
    (hDD : Pairwise (fun i j ↦ Disjoint (D i) (D j)))
    (hNN : Disjoint (N false) (N true))
    (hcontact : ∀ i b, (D i ∩ N b).Nonempty → i = r b false ∨ i = r b true)
    (hconn : IsPreconnected ((⋃ i, D i) ∪ ⋃ b, N b)) :
    (twoBandGraph r).Connected := by
  classical
  let S : C ⊕ Bool → Set X := Sum.elim D N
  let g : C ⊕ Bool → C := Sum.elim id (fun b ↦ r b false)
  have hends (b : Bool) : (twoBandGraph r).Reachable (r b false) (r b true) := by
    by_cases he : r b false = r b true
    · exact he ▸ SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨he, b, false, rfl, rfl⟩
  have hmeet (i j : C ⊕ Bool) (h : (S i ∩ S j).Nonempty) :
      (twoBandGraph r).Reachable (g i) (g j) := by
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hij : i = j := by
          by_contra hn
          obtain ⟨x, hx, hy⟩ := h
          exact disjoint_left.mp (hDD hn) hx hy
        exact hij ▸ SimpleGraph.Reachable.refl _
      | inr b =>
        rcases hcontact i b h with rfl | rfl
        · exact SimpleGraph.Reachable.refl _
        · exact (hends b).symm
    | inr b =>
      cases j with
      | inl j =>
        rcases hcontact j b (by simpa only [S, Sum.elim_inl, Sum.elim_inr, inter_comm] using h)
          with rfl | rfl
        · exact SimpleGraph.Reachable.refl _
        · exact hends b
      | inr c =>
        have hbc : b = c := by
          cases b <;> cases c
          · rfl
          · obtain ⟨x, hx, hy⟩ := h
            exact (disjoint_left.mp hNN hx hy).elim
          · obtain ⟨x, hx, hy⟩ := h
            exact (disjoint_left.mp hNN hy hx).elim
          · rfl
        exact hbc ▸ SimpleGraph.Reachable.refl _
  have hclosed : ∀ i, IsClosed (S i) := by
    intro i
    cases i with
    | inl i => exact hD i
    | inr b => exact hN b
  have hc : IsPreconnected (⋃ i, S i) := by
    simpa only [S, iUnion_sum, Sum.elim_inl, Sum.elim_inr] using hconn
  let : Nonempty C := ⟨r false false⟩
  apply SimpleGraph.Connected.mk
  intro i j
  have H := transGen_of_finite_closed_cover S hc hclosed
    (Sum.inl i) (Sum.inl j) (hne i) (hne j)
  have H' : ∀ a b, TransGen (fun a b ↦ (S a ∩ S b).Nonempty) a b →
      (twoBandGraph r).Reachable (g a) (g b) := by
    intro a b hab
    induction hab with
    | single h => exact hmeet _ _ h
    | tail _ h ih => exact ih.trans (hmeet _ _ h)
  exact H' _ _ H


theorem twoBandGraph_components_hit {C : Type*} (r : Bool → Bool → C)
    (hconn : (twoBandGraph r).Connected) (c : C) : ∃ b s, r b s = c := by
  obtain ⟨w⟩ := hconn.preconnected (r false false) c
  have H : ∀ a b, (twoBandGraph r).Walk a b →
      (∃ i s, r i s = a) → ∃ i s, r i s = b := by
    intro a b w
    induction w with
    | nil => exact id
    | cons h _ ih =>
      intro _
      obtain ⟨_, i, s, _, hs⟩ := h
      exact ih ⟨i, !s, hs⟩
  exact H _ _ w ⟨false, false, rfl⟩

end PoincareConjecture.M76.Dehn.Annuli
