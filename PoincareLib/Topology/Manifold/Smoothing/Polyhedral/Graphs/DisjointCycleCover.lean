import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.GeometricGraphComponents
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Recognizing disjoint unions of cycle graphs

An exact edge cover by cycle graphs with pairwise disjoint
geometric carriers has degree two at every nonisolated vertex.
The realization need not be injective: every incident edge
contains the same realized endpoint, which already forces
its cover member to be unique. See Alexander 1924, pp. 6--7
and M76 derivation 248.
-/

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An exact edge cover by cycle graphs whose geometric
carriers are pairwise disjoint is itself a cycle graph.
No finiteness or injective realization is required.
See Alexander pp. 6--7 and M76 derivation 248. -/
theorem isCycles_of_pairwise_disjoint_segmentCarrier (G : SimpleGraph V) (p : V → E)
    (S : Set (SimpleGraph V)) (hcycles : ∀ H ∈ S, H.IsCycles)
    (hcover : ∀ v w, G.Adj v w ↔ ∃ H ∈ S, H.Adj v w)
    (hdisj : S.Pairwise (fun H J => Disjoint (H.segmentCarrier p) (J.segmentCarrier p))) :
    G.IsCycles := by
  classical
  intro v hv
  obtain ⟨w, hvw⟩ := hv
  obtain ⟨H, hH, hHvw⟩ := (hcover v w).mp hvw
  have hneighbors : G.neighborSet v = H.neighborSet v := by
    ext u
    constructor
    · intro hvu
      obtain ⟨J, hJ, hJvu⟩ := (hcover v u).mp hvu
      have hJH : J = H := by
        by_contra hne
        have hpJ : p v ∈ J.segmentCarrier p :=
          ⟨v, u, hJvu, left_mem_segment ℝ (p v) (p u)⟩
        have hpH : p v ∈ H.segmentCarrier p :=
          ⟨v, w, hHvw, left_mem_segment ℝ (p v) (p w)⟩
        exact Set.disjoint_left.mp (hdisj hJ hH hne) hpJ hpH
      exact hJH ▸ hJvu
    · intro hvu
      exact (hcover v u).mpr ⟨H, hH, hvu⟩
  rw [hneighbors]
  exact hcycles H hH ⟨w, hHvw⟩

/-- At each vertex of a cycle graph the neighbor count is
zero or two, including all isolated vertices.
See Alexander pp. 6--7 and M76 derivation 248. -/
theorem IsCycles.ncard_neighbors_eq_zero_or_two {G : SimpleGraph V}
    (hG : G.IsCycles) (v : V) :
    (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 2 := by
  by_cases hv : (G.neighborSet v).Nonempty
  · exact Or.inr (hG hv)
  · exact Or.inl (by rw [Set.not_nonempty_iff_eq_empty.mp hv, Set.ncard_empty])

end SimpleGraph
