import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem connectedComponents_card_of_finite_closed_partition
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {G : Set X} (pieces : κ → Set X)
    (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hcover : ⋃ i, pieces i = G) (hconn : ∀ i, IsConnected (pieces i)) :
    Nat.card (ConnectedComponents G) = Nat.card κ := by
  have h := connected_components_mark_counts_of_ambient_partition
    pieces hclosed hdis hcover hconn (∅ : Set X)
  simpa only [preimage_empty, image_empty, compl_empty, Set.ncard_univ,
    disjoint_empty, ofPred_true] using h.2

theorem connectedComponents_card_lt_of_open_deletion
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {G O : Set X} (pieces : κ → Set X)
    (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hcover : ⋃ i, pieces i = G) (hconn : ∀ i, IsConnected (pieces i))
    (hO : IsOpen O) (hfront : Disjoint G (frontier O))
    (hremoved : (G ∩ O).Nonempty) :
    Nat.card (ConnectedComponents (G \ O : Set X)) < Nat.card (ConnectedComponents G) := by
  let retained : Set κ := {i | pieces i ⊆ Oᶜ}
  have hsub (i : κ) : pieces i ⊆ G := by
    rw [← hcover]
    exact subset_iUnion pieces i
  have hwhole (i : κ) : pieces i ⊆ O ∨ pieces i ⊆ Oᶜ := by
    rcases (hconn i).isPreconnected.subset_or_subset_compl_closure hO
      (hfront.symm.mono_right (hsub i)) with hi | ho
    · exact Or.inl hi
    · exact Or.inr (fun _ hx hxO => ho hx (subset_closure hxO))
  have hretcover : ⋃ i : retained, pieces i.val = G \ O := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨hsub i.val hi, i.property hi⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hx.1)
      rcases hwhole i with hin | hout
      · exact (hx.2 (hin hi)).elim
      · exact mem_iUnion.mpr ⟨⟨i, hout⟩, hi⟩
  have hretcount := connectedComponents_card_of_finite_closed_partition
    (fun i : retained => pieces i.val) (fun i => hclosed i.val)
    (fun i j hij => hdis (fun h => hij (Subtype.ext h))) hretcover (fun i => hconn i.val)
  rw [hretcount, connectedComponents_card_of_finite_closed_partition
    pieces hclosed hdis hcover hconn]
  have hstrict : retained ⊂ univ := by
    refine ⟨subset_univ _, ?_⟩
    intro h
    obtain ⟨x, hxG, hxO⟩ := hremoved
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hxG)
    exact h (mem_univ i) hi hxO
  rw [Nat.card_coe_set_eq]
  simpa only [Set.ncard_univ] using Set.ncard_lt_ncard hstrict (ht := Set.toFinite _)

end PoincareConjecture.M76.Dehn.Annuli
