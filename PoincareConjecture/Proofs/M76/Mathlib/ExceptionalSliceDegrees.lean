import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalNeighborCofaces
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem exceptionalSliceGraph_two_neighbors (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 → v = q)
    (hcofaces : ∀ e ∈ K.faces, A.StraddlesZero e →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (e : K.strictCrossingEdges A) :
    ((K.exceptionalSliceGraph A q).neighborSet (some e)).ncard = 2 := by
  classical
  obtain ⟨t, u, htu, hset⟩ := Set.ncard_eq_two.mp
    (hcofaces e.val e.property.1 e.property.2)
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t := by
    change t ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}
    rw [hset]
    exact mem_insert _ _
  have hu : u ∈ K.faces ∧ u.card = 3 ∧ e.val ⊆ u := by
    change u ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}
    rw [hset]
    exact mem_insert_of_mem _ (mem_singleton _)
  obtain ⟨v, hv, hvuniq⟩ := K.existsUnique_exceptional_neighbor_of_coface
    A hAq hzero e ht.1 ht.2.1 ht.2.2
  obtain ⟨w, hw, hwuniq⟩ := K.existsUnique_exceptional_neighbor_of_coface
    A hAq hzero e hu.1 hu.2.1 hu.2.2
  have hvw : v ≠ w := by
    intro h
    subst w
    exact htu (hv.symm.trans hw)
  have hneighbors : (K.exceptionalSliceGraph A q).neighborSet (some e) = {v, w} := by
    ext k
    rw [SimpleGraph.mem_neighborSet, K.exceptionalSliceGraph_adj_some_iff]
    constructor
    · intro hk
      have hkcoface : e.val ∪ K.exceptionalOriginalVertices A q k ∈
          {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t} :=
        ⟨hk.1, hk.2, Finset.subset_union_left⟩
      rw [hset] at hkcoface
      rcases mem_insert_iff.mp hkcoface with hkt | hku
      · exact Or.inl (hvuniq k hkt)
      · exact Or.inr (hwuniq k (mem_singleton_iff.mp hku))
    · rintro (rfl | rfl)
      · rw [hv]
        exact ⟨ht.1, ht.2.1⟩
      · rw [hw]
        exact ⟨hu.1, hu.2.1⟩
  rw [hneighbors]
  exact ncard_pair hvw

theorem exceptionalSliceGraph_even_neighbors (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) {q : E} (hAq : A q = 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 → v = q)
    (hcofaces : ∀ e ∈ K.faces, A.StraddlesZero e →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Even ((K.exceptionalSliceGraph A q).neighborSet none).ncard := by
  classical
  let := (K.finite_strictCrossingEdges A hK).fintype
  let G := K.exceptionalSliceGraph A q
  have hdeg (v : Option (K.strictCrossingEdges A)) :
      (G.neighborSet v).ncard = G.degree v := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    exact G.card_neighborSet_eq_degree v
  rw [hdeg]
  by_contra h
  obtain ⟨w, hw, hodd⟩ := G.exists_ne_odd_degree_of_exists_odd_degree none
    (Nat.not_even_iff_odd.mp h)
  cases w with
  | none => exact hw rfl
  | some e =>
    have he : G.degree (some e) = 2 := by
      rw [← hdeg]
      exact K.exceptionalSliceGraph_two_neighbors A hAq hzero hcofaces e
    rw [he] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd

end Geometry.SimplicialComplex
