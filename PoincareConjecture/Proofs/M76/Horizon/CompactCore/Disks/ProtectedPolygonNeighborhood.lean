import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.InnermostFrontierPolygon

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem exists_protected_polygon_neighborhood
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D s : Set E} {U : Set X} {g : E → X} {S : Set (Set E)}
    (hg : ContinuousOn g D) (hU : IsOpen U) (hsD : s ⊆ interior D)
    (hsU : MapsTo g s U) (hS : S.Finite) (hs : s ∈ S)
    (hclosed : ∀ t ∈ S, IsClosed t) (hdisj : S.PairwiseDisjoint id) :
    ∃ W : Set E, IsOpen W ∧ s ⊆ W ∧ W ⊆ interior D ∧ MapsTo g W U ∧
      W ∩ (⋃ t ∈ S, t) = s := by
  let T := ⋃ t ∈ S \ {s}, t
  have hT : IsClosed T := hS.sdiff.isClosed_biUnion fun t ht => hclosed t ht.1
  let W := (interior D ∩ g ⁻¹' U) \ T
  have hW : IsOpen W :=
    ((hg.mono interior_subset).isOpen_inter_preimage isOpen_interior hU).sdiff hT
  have hsW : s ⊆ W := by
    intro x hx
    refine ⟨⟨hsD hx, hsU hx⟩, ?_⟩
    intro hxT
    obtain ⟨t, ⟨ht, hts⟩, hxt⟩ := mem_iUnion₂.mp hxT
    exact Set.disjoint_left.mp (hdisj ht hs (fun heq => hts heq)) hxt hx
  refine ⟨W, hW, hsW, fun _ hx => hx.1.1, fun _ hx => hx.1.2, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxW, hxS⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxS
    by_cases hts : t = s
    · exact hts ▸ hxt
    · exact (hxW.2 (mem_iUnion₂.mpr ⟨t, ⟨ht, hts⟩, hxt⟩)).elim
  · intro x hx
    exact ⟨hsW hx, mem_iUnion₂.mpr ⟨s, hs, hx⟩⟩

theorem collar_enlargement_inter_family
    {E : Type*} {B W A s : Set E} {S : Set (Set E)}
    (hB : B ∩ (⋃ t ∈ S, t) = s) (hW : W ∩ (⋃ t ∈ S, t) = s)
    (hBA : B ⊆ A) (hA : A ⊆ B ∪ W) :
    A ∩ (⋃ t ∈ S, t) = s := by
  apply Subset.antisymm
  · rintro x ⟨hxA, hxS⟩
    rcases hA hxA with hxB | hxW
    · exact hB.subset ⟨hxB, hxS⟩
    · exact hW.subset ⟨hxW, hxS⟩
  · intro x hx
    exact ⟨hBA (hB.superset hx).1, (hB.superset hx).2⟩

end PoincareConjecture.M76
