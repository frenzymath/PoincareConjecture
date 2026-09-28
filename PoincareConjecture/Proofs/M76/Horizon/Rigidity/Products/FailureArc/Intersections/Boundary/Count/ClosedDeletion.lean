import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.Count
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem connectedComponents_card_lt_of_closed_cut_deletion
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {G N C : Set X} (pieces : κ → Set X)
    (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)))
    (hcover : ⋃ i, pieces i = G) (hconn : ∀ i, IsConnected (pieces i))
    (hN : IsClosed N) (hC : IsClosed C) (hGC : G ⊆ N ∪ C)
    (hseam : Disjoint G (N ∩ C)) (hremoved : (G \ C).Nonempty) :
    Nat.card (ConnectedComponents (G ∩ C : Set X)) < Nat.card (ConnectedComponents G) := by
  let retained : Set κ := {i | pieces i ⊆ C}
  have hsub (i : κ) : pieces i ⊆ G := by
    rw [← hcover]
    exact subset_iUnion pieces i
  have hwhole (i : κ) : pieces i ⊆ N ∨ pieces i ⊆ C :=
    isPreconnected_subset_one_cut_piece (hconn i).isPreconnected hN hC
      ((hsub i).trans hGC) rfl (hseam.mono_left (hsub i))
  have hretcover : ⋃ i : retained, pieces i.val = G ∩ C := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨hsub i.val hi, i.property hi⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hx.1)
      rcases hwhole i with hin | hout
      · exact (Set.disjoint_left.mp hseam hx.1 ⟨hin hi, hx.2⟩).elim
      · exact mem_iUnion.mpr ⟨⟨i, hout⟩, hi⟩
  have hretcount := connectedComponents_card_of_finite_closed_partition
    (fun i : retained ↦ pieces i.val) (fun i ↦ hclosed i.val)
    (fun i j hij ↦ hdis (fun h ↦ hij (Subtype.ext h))) hretcover (fun i ↦ hconn i.val)
  rw [hretcount, connectedComponents_card_of_finite_closed_partition
    pieces hclosed hdis hcover hconn]
  have hstrict : retained ⊂ univ := by
    refine ⟨subset_univ _, ?_⟩
    intro h
    obtain ⟨x, hxG, hxC⟩ := hremoved
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hxG)
    exact hxC (h (mem_univ i) hi)
  rw [Nat.card_coe_set_eq]
  simpa only [Set.ncard_univ] using Set.ncard_lt_ncard hstrict (ht := Set.toFinite _)

end PoincareConjecture.M76.Dehn.Annuli
