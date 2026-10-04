import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.Regions

/-!
# Containment of polygonal regions from boundary containment

The child-region inclusion required by Munkres (1960), Lemma 2.3,
p. 195. A child boundary in the original closed inside forces its
whole inside and closed inside to be contained there. The argument
uses the unbounded exterior and both exact Jordan frontier formulas.
See `smale/derivations/2026-09-21-region-nesting.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n m : ℕ} {p : Polygon E n} {q : Polygon E m}

/-- The closed exterior includes precisely its boundary; Munkres, Lemma 2.3, p. 195. -/
theorem IsSimplePolygon.closure_polygonExterior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    closure (polygonExterior p) = polygonExterior p ∪ p.boundary ℝ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hfront⟩ := hp.polygonRegions_spec hdim
  rw [closure_eq_self_union_frontier, hfront]

/-- The inside is the complement of the closed exterior; Munkres, Lemma 2.3, p. 195. -/
theorem IsSimplePolygon.polygonInterior_eq_compl_closure_exterior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    polygonInterior p = (closure (polygonExterior p))ᶜ := by
  obtain ⟨_, _, _, _, hdis, hcover, _⟩ := hp.polygonRegions_spec hdim
  rw [hp.closure_polygonExterior hdim]
  ext x
  constructor
  · intro hx hmem
    rcases hmem with hxO | hxB
    · exact Set.disjoint_left.mp hdis hx hxO
    · exact hx.1 hxB
  · intro hx
    have hxB : x ∉ p.boundary ℝ := fun hz => hx (Or.inr hz)
    have hxcover : x ∈ polygonInterior p ∪ polygonExterior p := hcover.symm ▸ hxB
    exact hxcover.resolve_right fun hz => hx (Or.inl hz)

/-- A boundary inside a closed region cannot reach its unbounded exterior;
the exterior comparison for Munkres, Lemma 2.3, p. 195. -/
theorem IsSimplePolygon.polygonExterior_subset_of_boundary_subset_closureInterior
    (hp : IsSimplePolygon p) (hq : IsSimplePolygon q) (hdim : Module.finrank ℝ E = 2)
    (hB : q.boundary ℝ ⊆ closure (polygonInterior p)) :
    polygonExterior p ⊆ polygonExterior q := by
  obtain ⟨_, _, _, hOp, _, _, _, hOb, _⟩ := hp.polygonRegions_spec hdim
  obtain ⟨hIq, hOq, _, _, hdis, hcover, hIb, _⟩ := hq.polygonRegions_spec hdim
  have havoid : polygonExterior p ⊆ polygonInterior q ∪ polygonExterior q := by
    rw [hcover]
    intro x hx hxB
    rw [hp.polygonExterior_eq_compl_closure_interior hdim] at hx
    exact hx (hB hxB)
  rcases hOp.isConnected.isPreconnected.subset_or_subset hIq hOq hdis havoid with h | h
  · exact (hOb (hIb.subset h)).elim
  · exact h

/-- Actual boundary containment gives containment of both inside and closed inside;
the child-region step in Munkres, Lemma 2.3, p. 195. -/
theorem IsSimplePolygon.polygonRegions_subset_of_boundary_subset_closureInterior
    (hp : IsSimplePolygon p) (hq : IsSimplePolygon q) (hdim : Module.finrank ℝ E = 2)
    (hB : q.boundary ℝ ⊆ closure (polygonInterior p)) :
    polygonInterior q ⊆ polygonInterior p ∧
      closure (polygonInterior q) ⊆ closure (polygonInterior p) := by
  have hO := hp.polygonExterior_subset_of_boundary_subset_closureInterior hq hdim hB
  have hI : polygonInterior q ⊆ polygonInterior p := by
    rw [hq.polygonInterior_eq_compl_closure_exterior hdim,
      hp.polygonInterior_eq_compl_closure_exterior hdim]
    exact compl_subset_compl.mpr (closure_mono hO)
  exact ⟨hI, closure_mono hI⟩

end Poincare.Manifold.Schoenflies.Plane
