import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeSides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

theorem subset_of_preconnected_avoids_frontier {X : Type*} [TopologicalSpace X]
    {S Y : Set X} (hS : IsPreconnected S)
    (havoid : Disjoint S (frontier Y)) (hmeet : (S ∩ Y).Nonempty) : S ⊆ Y := by
  have hcover : S ⊆ interior Y ∪ interior Yᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact fun x hx => Set.disjoint_left.mp havoid hx
  have hdis : Disjoint (interior Y) (interior Yᶜ) := by
    rw [Set.disjoint_left]
    exact fun x hx hy => interior_subset hy (interior_subset hx)
  rcases hS.subset_or_subset isOpen_interior isOpen_interior hdis hcover with h | h
  · exact h.trans interior_subset
  · obtain ⟨x, hxS, hxY⟩ := hmeet
    exact (interior_subset (h hxS) hxY).elim

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem exists_cylinder_tail_closure_subset (e : TerminalEnd K) (n : ℕ)
    {Y : Set (E.extended.slice T).carrier} (hY : IsClosed Y)
    (hfront : IsCompact (frontier Y)) (htail : Subtype.val '' e.tail n ⊆ Y)
    (tube : EpsilonTubeCertificate (E.extended.metric T) Y) :
    ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1,
      closure (tube.cylinder.tail side a) ⊆ Y ∧
      ∀ b ∈ Ioo (0 : ℝ) 1, ∃ k : ℕ, n ≤ k ∧
        ∀ m : ℕ, k ≤ m → Subtype.val '' e.tail m ⊆ tube.cylinder.tail side b := by
  let Q := tube.cylinder
  have hfrontU : frontier Y ⊆ tube.carrier :=
    (hY.closure_eq ▸ frontier_subset_closure).trans tube.contains_X
  obtain ⟨a, ha, hleft, hright, _, _⟩ := Q.exists_tails_disjoint_of_isCompact hfront hfrontU
  obtain ⟨side, hside⟩ := e.exists_tube_direction n
    { tube with contains_X := htail.trans tube.contains_X }
  let b : ℝ := if side then 1 - a else a
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    cases side <;> simp only [b, Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> linarith [ha.1, ha.2]
  have havoid : Disjoint (Q.tail side b) (frontier Y) := by
    cases side
    · exact hleft
    · exact hright
  obtain ⟨k, hnk, hk⟩ := hside b hb
  have hmeet : (Q.tail side b ∩ Y).Nonempty := by
    obtain ⟨x, hx⟩ := (e.tail_image_connected k).nonempty
    exact ⟨x, hk k le_rfl hx, htail (Set.image_mono (e.nested hnk) hx)⟩
  have hsub : Q.tail side b ⊆ Y :=
    SingularRegularLimit.subset_of_preconnected_avoids_frontier
      (Q.isConnected_tail side hb).isPreconnected havoid hmeet
  exact ⟨side, b, hb, closure_minimal hsub hY, hside⟩

end PoincareConjecture.TerminalEnd
