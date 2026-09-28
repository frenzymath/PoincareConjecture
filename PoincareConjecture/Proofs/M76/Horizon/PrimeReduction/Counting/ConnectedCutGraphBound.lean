import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphConnectivity
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CutGraphHomologyBound

set_option autoImplicit false

universe u

namespace PoincareConjecture.M76.CutGraph

variable {V I X : Type u} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  [TopologicalSpace X] [ConnectedSpace X]

theorem nonempty_vertices_of_map (ends : I → Bool → V) (q : C(X, carrier ends)) :
    Nonempty V := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  rcases (q x).property with ⟨v, _⟩ | hi
  · exact ⟨v⟩
  · obtain ⟨i, _⟩ := Set.mem_iUnion.mp hi
    exact ⟨ends i false⟩

theorem connected_cycle_rank_of_vertices_reached (ends : I → Bool → V)
    (q : C(X, carrier ends))
    (hq : ∀ v, ∃ x, (q x : Ambient V I) = vertex v) :
    Module.finrank (ZMod 2) (LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) +
      Fintype.card V = Fintype.card I + 1 := by
  let := nonempty_vertices_of_map ends q
  exact incidence_cycle_rank ends (incidence_connected_of_vertices_reached ends q hq)

theorem connected_edge_count_le_homology_rank_add_vertices (ends : I → Bool → V)
    (q : C(X, carrier ends)) (s : C(carrier ends, X))
    (hq : ∀ v, ∃ x, (q x : Ambient V I) = vertex v)
    (H : (q.comp s).Homotopic (ContinuousMap.id (carrier ends)))
    [Module.Finite (ZMod 2) ↑((TopCat.toSSet.obj (TopCat.of X)).homology
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1)] :
    Fintype.card I + 1 ≤ Module.finrank (ZMod 2)
      ↑((TopCat.toSSet.obj (TopCat.of X)).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) + Fintype.card V := by
  rw [← connected_cycle_rank_of_vertices_reached ends q hq]
  exact Nat.add_le_add_right
    (LinearMap.finrank_le_finrank_of_injective
      (sectionIncidenceHomology_injective ends q s H)) _

end PoincareConjecture.M76.CutGraph
