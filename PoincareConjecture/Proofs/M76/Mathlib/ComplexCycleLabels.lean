import PoincareConjecture.Proofs.M76.Mathlib.FiniteCycleLabels
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

set_option autoImplicit false

namespace AbstractSimplicialComplex

variable {V : Type*} [DecidableEq V]

def edgeGraph (A : AbstractSimplicialComplex V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ {x, y} ∈ A.faces
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mem_faces_iff_singleton_or_edge (A : AbstractSimplicialComplex V)
    (hdim : ∀ s ∈ A.faces, s.card ≤ 2) (s : Finset V) :
    s ∈ A.faces ↔ (∃ x, s = {x}) ∨ ∃ x y, A.edgeGraph.Adj x y ∧ s = {x, y} := by
  constructor
  · intro hs
    have hpos : 0 < s.card := Finset.card_pos.mpr (A.isRelLowerSet_faces hs).1
    have hle := hdim s hs
    by_cases hone : s.card = 1
    · exact Or.inl (Finset.card_eq_one.mp hone)
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
      exact Or.inr ⟨x, y, ⟨hxy, hs⟩, rfl⟩
  · rintro (⟨x, rfl⟩ | ⟨x, y, hxy, rfl⟩)
    · exact A.singleton_mem x
    · exact hxy.2

variable [Finite V]

theorem exists_cyclic_face_labels (A : AbstractSimplicialComplex V)
    (hdim : ∀ s ∈ A.faces, s.card ≤ 2) (hc : A.edgeGraph.Connected)
    (hdegree : ∀ v, (A.edgeGraph.neighborSet v).ncard = 2) :
    ∃ (n : ℕ) (e : Fin (n + 3) ≃ V), ∀ s : Finset (Fin (n + 3)),
      s.map e.toEmbedding ∈ A.faces ↔ s.Nonempty ∧ ∃ i, s ⊆ {i, i + 1} := by
  obtain ⟨n, e, he⟩ := A.edgeGraph.exists_cyclic_labels_of_two_neighbors hc hdegree
  refine ⟨n, e, ?_⟩
  intro s
  constructor
  · intro hs
    have hne : s.Nonempty := Finset.map_nonempty.mp (A.isRelLowerSet_faces hs).1
    refine ⟨hne, ?_⟩
    rcases (A.mem_faces_iff_singleton_or_edge hdim _).mp hs with
      ⟨x, hx⟩ | ⟨x, y, hxy, hxyface⟩
    · have hsx : s = {e.symm x} := by
        apply Finset.map_injective e.toEmbedding
        simpa only [Finset.map_singleton, Equiv.coe_toEmbedding, e.apply_symm_apply] using hx
      exact ⟨e.symm x, hsx ▸ Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)⟩
    · obtain ⟨i, hi⟩ := (he x y).mp hxy
      have hpair : ({x, y} : Finset V) = {e i, e (i + 1)} := by
        rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Finset.pair_comm _ _
      have hsi : s = {i, i + 1} := by
        apply Finset.map_injective e.toEmbedding
        simpa only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] using
          hxyface.trans hpair
      exact ⟨i, hsi ▸ Finset.Subset.refl _⟩
  · rintro ⟨hne, i, hsi⟩
    have hi : A.edgeGraph.Adj (e i) (e (i + 1)) :=
      (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩
    apply (A.isRelLowerSet_faces hi.2).2 _ (Finset.map_nonempty.mpr hne)
    simpa only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] using
      (Finset.map_subset_map.mpr hsi : s.map e.toEmbedding ⊆
        ({i, i + 1} : Finset (Fin (n + 3))).map e.toEmbedding)

end AbstractSimplicialComplex
