import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComponentCycleLabels
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Removing cycles from finite even graphs

A nonempty finite even graph contains a simple cycle: otherwise
an edge component is a finite tree with a leaf. Removing a cycle
preserves even neighbor counts. See Alexander 1924, p. 6 and the
exceptional-section argument in M76 derivation 149.
-/

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V : Type*}

/-- A finite graph with even neighbor counts and at least one
edge contains an actual simple cycle. See the finite-tree leaf
argument in M76 derivation 149, used for Alexander p. 6. -/
theorem exists_cycle_of_even_neighbors [Finite V] (G : SimpleGraph V) (hG : G ≠ ⊥)
    (heven : ∀ v, Even (G.neighborSet v).ncard) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  classical
  let := Fintype.ofFinite V
  by_contra h
  have hacyc : G.IsAcyclic := by
    intro v p hp
    exact h ⟨v, p, hp⟩
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hG
  let C := G.connectedComponentMk a
  have ha : a ∈ C := rfl
  have hb : b ∈ C := C.mem_supp_of_adj_mem_supp ha hab
  let a' : C := ⟨a, ha⟩
  let b' : C := ⟨b, hb⟩
  have hne : a' ≠ b' := fun heq => hab.ne (congrArg Subtype.val heq)
  let : Nontrivial C := ⟨⟨a', b', hne⟩⟩
  obtain ⟨v, hv⟩ := (hacyc.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  have hcard : (C.toSimpleGraph.neighborSet v).ncard = 1 := by
    rw [← Set.fintypeCard_eq_ncard, C.toSimpleGraph.card_neighborSet_eq_degree, hv]
  have he := heven v.val
  rw [← C.ncard_neighborSet G v, hcard] at he
  exact (by decide : ¬ Even (1 : ℕ)) he

/-- Every cycle graph has even neighbor counts, including zero
at isolated vertices. See M76 derivation 149 and Alexander p. 6. -/
theorem IsCycles.even_neighbors {G : SimpleGraph V} (hG : G.IsCycles) (v : V) :
    Even (G.neighborSet v).ncard := by
  by_cases hv : (G.neighborSet v).Nonempty
  · rw [hG hv]
    exact even_two
  · rw [Set.not_nonempty_iff_eq_empty.mp hv, Set.ncard_empty]
    exact Even.zero

/-- Subtracting a cycle subgraph preserves even neighbor counts.
The inclusion ensures that finite cardinal subtraction counts
the actual remaining edges. See M76 derivation 149, Alexander p. 6. -/
theorem even_neighbors_sdiff_of_isCycles [Finite V] (G H : SimpleGraph V) (hHG : H ≤ G)
    (heven : ∀ v, Even (G.neighborSet v).ncard) (hH : H.IsCycles) :
    ∀ v, Even ((G \ H).neighborSet v).ncard := by
  intro v
  have hsub : H.neighborSet v ⊆ G.neighborSet v := fun _ hv => hHG hv
  rw [neighborSet_sdiff, Set.ncard_sdiff' hsub]
  exact (Nat.even_sub (Set.ncard_le_ncard hsub)).mpr
    ⟨fun _ => hH.even_neighbors v, fun _ => heven v⟩

end SimpleGraph
