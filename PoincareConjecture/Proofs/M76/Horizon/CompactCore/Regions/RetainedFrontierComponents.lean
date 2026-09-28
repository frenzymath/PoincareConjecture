import PoincareConjecture.Proofs.M76.Wall.CompressionComplexity
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup











set_option autoImplicit false

open Set

namespace Set

theorem IsPreconnected.subset_component_or_disjoint
    {X : Type*} [TopologicalSpace X] {S L : Set X} (hS : IsPreconnected S)
    (hSL : S ⊆ L) (x : X) :
    S ⊆ connectedComponentIn L x ∨ Disjoint S (connectedComponentIn L x) := by
  by_cases h : Disjoint S (connectedComponentIn L x)
  · exact Or.inr h
  · obtain ⟨y, hyS, hyM⟩ := not_disjoint_iff.mp h
    exact Or.inl ((hS.subset_connectedComponentIn hyS hSL).trans
      (connectedComponentIn_eq hyM).symm.subset)

theorem exists_retained_frontier_component_labels
    {X : Type*} [TopologicalSpace X] {n : ℕ} (S : Fin n → Set X)
    {L F : Set X} (x : X) (hFL : F ⊆ L)
    (hconn : ∀ i, IsConnected (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : (⋃ i, S i) = F)
    (hcomponents : ∀ i, ∀ y ∈ S i, connectedComponentIn F y = S i)
    (hne : (F ∩ connectedComponentIn L x).Nonempty) :
    ∃ (kept : List (Fin n)) (pick : Fin kept.length ↪ Fin n),
      kept.Sublist (List.finRange n) ∧ kept.Nodup ∧ 0 < kept.length ∧
      (∀ i, pick i = kept.get i) ∧
      (∀ i, i ∈ kept ↔ S i ⊆ connectedComponentIn L x) ∧
      (⋃ i, S (pick i)) = F ∩ connectedComponentIn L x ∧
      (Pairwise fun i j => Disjoint (S (pick i)) (S (pick j))) ∧
      (∀ i, ∀ y ∈ S (pick i),
        connectedComponentIn (F ∩ connectedComponentIn L x) y = S (pick i)) ∧
      ∀ genus : Fin n → ℕ,
        (kept.map genus).Sublist ((List.finRange n).map genus) ∧
        PoincareConjecture.M76.Wall.compressionComplexity (kept.map genus) ≤
          PoincareConjecture.M76.Wall.compressionComplexity ((List.finRange n).map genus) := by
  classical
  let M := connectedComponentIn L x
  have hSF (i : Fin n) : S i ⊆ F := by
    intro y hy
    exact hcover.subset (mem_iUnion.mpr ⟨i, hy⟩)
  have hside (i : Fin n) : S i ⊆ M ∨ Disjoint (S i) M :=
    (hconn i).isPreconnected.subset_component_or_disjoint ((hSF i).trans hFL) x
  let kept := (List.finRange n).filter (fun i => decide (S i ⊆ M))
  have hsub : kept.Sublist (List.finRange n) := List.filter_sublist
  have hnd : kept.Nodup := (List.nodup_finRange n).sublist hsub
  have hmem (i : Fin n) : i ∈ kept ↔ S i ⊆ M := by
    simp [kept]
  let pick : Fin kept.length ↪ Fin n := ⟨kept.get, hnd.injective_get⟩
  have hselected (i : Fin kept.length) : S (pick i) ⊆ M :=
    (hmem (pick i)).mp (List.get_mem kept i)
  have hselect : ∀ y ∈ F ∩ M, ∃ i ∈ kept, y ∈ S i := by
    intro y hy
    obtain ⟨i, hiy⟩ := mem_iUnion.mp (hcover.symm.subset hy.1)
    refine ⟨i, (hmem i).mpr ?_, hiy⟩
    rcases hside i with hi | hi
    · exact hi
    · exact False.elim (disjoint_left.mp hi hiy hy.2)
  have hunion : (⋃ i, S (pick i)) = F ∩ M := by
    apply Subset.antisymm
    · rintro y ⟨_, ⟨i, rfl⟩, hy⟩
      exact ⟨hSF (pick i) hy, hselected i hy⟩
    · intro y hy
      obtain ⟨i, hi, hiy⟩ := hselect y hy
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hi
      exact mem_iUnion.mpr ⟨k, by simpa only [pick, Function.Embedding.coeFn_mk, hk] using hiy⟩
  have hlength : 0 < kept.length := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨i, hi, _⟩ := hselect y hy
    exact List.length_pos_of_mem hi
  refine ⟨kept, pick, hsub, hnd, hlength, fun _ => rfl, hmem, hunion,
    fun i j hij => hdisjoint (fun h => hij (pick.injective h)), ?_, ?_⟩
  · intro i y hy
    apply Subset.antisymm
    · exact (connectedComponentIn_mono y inter_subset_left).trans
        (hcomponents (pick i) y hy).subset
    · exact (hconn (pick i)).isPreconnected.subset_connectedComponentIn hy
        (fun z hz => ⟨hSF (pick i) hz, hselected i hz⟩)
  · intro genus
    exact ⟨hsub.map genus, PoincareConjecture.M76.Wall.compressionComplexity_sublist (hsub.map genus)⟩

theorem reindexed_genus_list_eq
    {n : ℕ} {kept : List (Fin n)} {pick : Fin kept.length ↪ Fin n}
    (hpick : ∀ i, pick i = kept.get i) (genus : Fin n → ℕ) :
    (List.finRange kept.length).map (genus ∘ pick) = kept.map genus := by
  have hp : (pick : Fin kept.length → Fin n) = kept.get := funext hpick
  rw [hp, ← List.ofFn_eq_map, ← List.map_ofFn, List.ofFn_get]

theorem exists_retained_frontier_component_labels_with_reindexed_genera
    {X : Type*} [TopologicalSpace X] {n : ℕ} (S : Fin n → Set X)
    {L F : Set X} (x : X) (hFL : F ⊆ L)
    (hconn : ∀ i, IsConnected (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : (⋃ i, S i) = F)
    (hcomponents : ∀ i, ∀ y ∈ S i, connectedComponentIn F y = S i)
    (hne : (F ∩ connectedComponentIn L x).Nonempty) :
    ∃ (kept : List (Fin n)) (pick : Fin kept.length ↪ Fin n),
      kept.Sublist (List.finRange n) ∧ kept.Nodup ∧ 0 < kept.length ∧
      (∀ i, pick i = kept.get i) ∧
      (∀ i, i ∈ kept ↔ S i ⊆ connectedComponentIn L x) ∧
      (⋃ i, S (pick i)) = F ∩ connectedComponentIn L x ∧
      (Pairwise fun i j => Disjoint (S (pick i)) (S (pick j))) ∧
      (∀ i, ∀ y ∈ S (pick i),
        connectedComponentIn (F ∩ connectedComponentIn L x) y = S (pick i)) ∧
      ∀ genus : Fin n → ℕ,
        (kept.map genus).Sublist ((List.finRange n).map genus) ∧
        PoincareConjecture.M76.Wall.compressionComplexity (kept.map genus) ≤
          PoincareConjecture.M76.Wall.compressionComplexity ((List.finRange n).map genus) ∧
        (List.finRange kept.length).map (genus ∘ pick) = kept.map genus ∧
        ((List.finRange kept.length).map (genus ∘ pick)).Sublist
          ((List.finRange n).map genus) ∧
        PoincareConjecture.M76.Wall.compressionComplexity
          ((List.finRange kept.length).map (genus ∘ pick)) ≤
          PoincareConjecture.M76.Wall.compressionComplexity ((List.finRange n).map genus) := by
  obtain ⟨kept, pick, hsub, hnd, hpos, hpick, hmem, hcover', hdisj, hcomp, hg⟩ :=
    exists_retained_frontier_component_labels S x hFL hconn hdisjoint hcover hcomponents hne
  refine ⟨kept, pick, hsub, hnd, hpos, hpick, hmem, hcover', hdisj, hcomp, ?_⟩
  intro genus
  have heq := reindexed_genus_list_eq hpick genus
  obtain ⟨hsubg, hle⟩ := hg genus
  exact ⟨hsubg, hle, heq, heq.symm ▸ hsubg, heq.symm ▸ hle⟩

end Set
