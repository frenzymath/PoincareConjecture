import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexCoreCollar

/-!
# Exact compact core and collar attachments

The inner convex core and its exterior collar cover the old body
and meet exactly along the new core frontier. A previously processed
carrier meeting only the original frontier remains disjoint from
the new core. See Cairns 1940, pp. 803--805 and M76 derivation 61.
-/

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X]

/-- The exterior collar of a closed inner set meets it exactly
along its frontier. See Cairns pp. 803--805 and M76 derivation 61. -/
theorem IsClosed.collar_inter_eq_frontier {C D : Set X} (hD : IsClosed D) (hDC : D ⊆ C) :
    (C \ interior D) ∩ D = frontier D := by
  rw [frontier, hD.closure_eq]
  ext x
  constructor
  · exact fun hx => ⟨hx.2, hx.1.2⟩
  · exact fun hx => ⟨⟨hDC hx.1, hx.2⟩, hx.1⟩

/-- The collar and its inner set cover the original body.
See Cairns pp. 803--805 and M76 derivation 61. -/
theorem collar_union_inner_eq {C D : Set X} (hDC : D ⊆ C) :
    (C \ interior D) ∪ D = C := by
  ext x
  constructor
  · exact fun hx => hx.elim And.left (fun h => hDC h)
  · intro hx
    by_cases hxd : x ∈ D
    · exact Or.inr hxd
    · exact Or.inl ⟨hx, fun hxi => hxd (interior_subset hxi)⟩

/-- A carrier meeting a body only on its frontier is disjoint
from every core in the body's interior.
See Cairns pp. 803--805 and M76 derivation 61. -/
theorem disjoint_innerCore_of_inter_subset_frontier {A C D : Set X}
    (hAC : A ∩ C ⊆ frontier C) (hD : D ⊆ interior C) : Disjoint A D := by
  apply disjoint_left.mpr
  intro x hxA hxD
  exact (hAC ⟨hxA, interior_subset (hD hxD)⟩).2 (hD hxD)

variable [AddCommGroup X] [Module ℝ X] [T2Space X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A compact convex body decomposes into an inner compact convex
core and a compact exterior collar inside any prescribed boundary
neighborhood, with exact common frontier and coverage.
See Cairns pp. 803--805 and M76 derivation 61. -/
theorem IsCompact.exists_convex_core_decomposition {C U : Set X} (hC : IsCompact C)
    (hc : Convex ℝ C) (hi : (interior C).Nonempty) (hU : IsOpen U)
    (hfront : frontier C ⊆ U) :
    ∃ D : Set X, IsCompact D ∧ Convex ℝ D ∧ (interior D).Nonempty ∧
      D ⊆ interior C ∧ IsCompact (C \ interior D) ∧ C \ interior D ⊆ U ∧
      (C \ interior D) ∩ D = frontier D ∧ (C \ interior D) ∪ D = C := by
  obtain ⟨D, hD, hDc, hDi, hDC, hcollar⟩ := hC.exists_convex_innerCore hc hi hU hfront
  have hDC' : D ⊆ C := hDC.trans interior_subset
  exact ⟨D, hD, hDc, hDi, hDC, hC.diff isOpen_interior, hcollar,
    hD.isClosed.collar_inter_eq_frontier hDC', collar_union_inner_eq hDC'⟩
