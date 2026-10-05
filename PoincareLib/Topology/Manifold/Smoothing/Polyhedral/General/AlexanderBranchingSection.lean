import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.AlexanderComplexityCardinalityPolygons

/-!
# A branching polygon section is nonisolated at its common point

Two meeting polygons identify the common point, and a polygon
is the closure of its puncture. Thus the whole exceptional
section has the nonisolation needed by the actual cap supplier.
See Alexander 1924, pp. 6--7 and M76 derivation 260.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A branching family with intersections confined to q makes
q nonisolated in every set containing all its polygon boundaries.
No selected polygon or cap is assumed here. See Alexander
pp. 6--7 and derivation 260. -/
theorem mem_closure_punctured_section_of_branching
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (q : E) (hpair : Pairwise (fun i j =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (hbranch : ¬ Pairwise (fun i j =>
      Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {S : Set E} (hcover : ∀ i, (P i).boundary ℝ ⊆ S) :
    q ∈ closure (S \ {q}) := by
  classical
  change ¬ ∀ i j, i ≠ j → Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ) at hbranch
  push Not at hbranch
  obtain ⟨i, j, hij, hmeet⟩ := hbranch
  obtain ⟨x, hxi, hxj⟩ := not_disjoint_iff.mp hmeet
  have hxq : x = q := hpair hij ⟨hxi, hxj⟩
  have hqi : q ∈ (P i).boundary ℝ := hxq ▸ hxi
  obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hP i).2 (hP i).1
  have hconn : IsConnected ((P i).boundary ℝ) :=
    isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hpunc := isConnected_sdiff_singleton_of_homeomorph_circle ((P i).boundary ℝ) e q
  have hcl := hconn.isPreconnected.closure_sdiff_singleton_eq
    (P i).isClosed_boundary q hpunc.nonempty
  exact closure_mono (sdiff_subset_sdiff_left (hcover i)) (hcl.symm ▸ hqi)

end Polygon
