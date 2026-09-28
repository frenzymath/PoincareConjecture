import PoincareConjecture.Proofs.M76.Mathlib.ClosedRegionPatchIncidence
import Mathlib.SetTheory.Cardinal.Finite









set_option autoImplicit false

open Set

namespace Set





theorem exists_indexed_components_of_closed_partition
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    (S : κ → Set X) (hS : ∀ i, IsClosed (S i))
    (hconn : ∀ i, IsConnected (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    {B F : Set X} (hB : IsClosed B) (hF : IsClosed F)
    (hBF : Disjoint B F) (hcover : (⋃ i, S i) = B ∪ F) (hFne : F.Nonempty) :
    ∃ (n : ℕ) (pick : Fin n ↪ κ), 0 < n ∧
      (⋃ i, S (pick i)) = F ∧
      ∀ i, ∀ x ∈ S (pick i), connectedComponentIn F x = S (pick i) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hside (i : κ) : S i ⊆ B ∨ S i ⊆ F := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp (hconn i).isPreconnected
      B F hB hF
    · exact fun _ hx => hcover.subset (mem_iUnion.mpr ⟨i, hx⟩)
    · rw [disjoint_iff_inter_eq_empty.mp hBF, inter_empty]
  have hselect : ∀ x ∈ F, ∃ i, S i ⊆ F ∧ x ∈ S i := by
    intro x hxF
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm.subset (Or.inr hxF))
    rcases hside i with hiB | hiF
    · exact False.elim (disjoint_left.mp hBF (hiB hxi) hxF)
    · exact ⟨i, hiF, hxi⟩
  let chosen := {i : κ // S i ⊆ F}
  let n := Fintype.card chosen
  let index : Fin n ≃ chosen := (Fintype.equivFin chosen).symm
  let pick : Fin n ↪ κ :=
    ⟨fun i => (index i).val, fun _ _ h => index.injective (Subtype.ext h)⟩
  have hn : 0 < n := by
    obtain ⟨x, hx⟩ := hFne
    obtain ⟨i, hi, _⟩ := hselect x hx
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have hselected (i : Fin n) : S (pick i) ⊆ F := (index i).property
  have hunion : (⋃ i, S (pick i)) = F := by
    apply Subset.antisymm (iUnion_subset hselected)
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hselect x hx
    refine mem_iUnion.mpr ⟨index.symm ⟨i, hi⟩, ?_⟩
    change x ∈ S (index (index.symm ⟨i, hi⟩)).val
    simpa only [index.apply_symm_apply] using hxi
  refine ⟨n, pick, hn, hunion, ?_⟩
  intro i x hx
  have hxF : x ∈ F := hselected i hx
  apply Subset.antisymm
  · have hC := isConnected_connectedComponentIn_iff.mpr hxF
    have hCcover : connectedComponentIn F x ⊆ ⋃ j, S j := by
      intro y hy
      exact hcover.symm.subset (Or.inr (connectedComponentIn_subset F x hy))
    have hpair : Pairwise (fun j k => S j ∩ S k ⊆ (∅ : Set X)) :=
      fun _ _ hjk => (disjoint_iff_inter_eq_empty.mp (hdisjoint hjk)).subset
    obtain ⟨j, hj⟩ := hC.exists_closure_subset_of_finite_closed_cover
      S hS hCcover hpair (disjoint_empty _)
    have hxj : x ∈ S j := hj (subset_closure (mem_connectedComponentIn hxF))
    have hji : j = pick i := by
      by_contra hne
      exact disjoint_left.mp (hdisjoint hne) hxj hx
    exact subset_closure.trans (hji ▸ hj)
  · exact (hconn (pick i)).isPreconnected.subset_connectedComponentIn hx (hselected i)

end Set
