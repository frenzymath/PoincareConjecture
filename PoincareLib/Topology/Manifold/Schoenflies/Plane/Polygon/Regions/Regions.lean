import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.ComponentCover
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.Jordan
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Canonical inside and outside of a simple planar polygon

The bounded region and its closure used in Munkres (1960), Definition 2.2
and Lemma 2.3, p. 195. Boundedness of actual complement components defines
the two regions without choosing Jordan witnesses. Their specification
follows from Cairns (1951), Theorem 2.1, pp. 860-861, as proved in Jordan.
See `smale/derivations/2026-09-21-polygon-regions.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Points outside the boundary in bounded complement components; the inside
of Munkres, Definition 2.2 and Lemma 2.3, p. 195, for simple planar polygons. -/
def polygonInterior (p : Polygon E n) : Set E :=
  {x | x ∉ p.boundary ℝ ∧ Bornology.IsBounded (connectedComponentIn (p.boundary ℝ)ᶜ x)}

/-- Points in unbounded complement components; the outside complementary to
Munkres's inside in Definition 2.2 and Lemma 2.3, p. 195. -/
def polygonExterior (p : Polygon E n) : Set E :=
  {x | x ∉ p.boundary ℝ ∧ ¬ Bornology.IsBounded (connectedComponentIn (p.boundary ℝ)ᶜ x)}

variable [FiniteDimensional ℝ E] {p : Polygon E n}

/-- The canonical regions have all polygonal Jordan properties; Cairns,
Theorem 2.1, pp. 860-861, and Munkres, Definition 2.2, p. 195. -/
theorem IsSimplePolygon.polygonRegions_spec (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    IsOpen (polygonInterior p) ∧ IsOpen (polygonExterior p) ∧
      IsPathConnected (polygonInterior p) ∧ IsPathConnected (polygonExterior p) ∧
      Disjoint (polygonInterior p) (polygonExterior p) ∧
      polygonInterior p ∪ polygonExterior p = (p.boundary ℝ)ᶜ ∧
      Bornology.IsBounded (polygonInterior p) ∧ ¬ Bornology.IsBounded (polygonExterior p) ∧
      frontier (polygonInterior p) = p.boundary ℝ ∧
      frontier (polygonExterior p) = p.boundary ℝ := by
  obtain ⟨U, V, hU, hV, hUp, hVp, hdis, hcover, hUb, hVb, hUf, hVf⟩ :=
    hp.exists_inside_outside hdim
  have hKU {x : E} (hx : x ∈ U) : connectedComponentIn (p.boundary ℝ)ᶜ x = U :=
    connectedComponentIn_eq_of_open_disjoint_cover hU hV hdis hcover
      hUp.isConnected.isPreconnected hx
  have hKV {x : E} (hx : x ∈ V) : connectedComponentIn (p.boundary ℝ)ᶜ x = V :=
    connectedComponentIn_eq_of_open_disjoint_cover hV hU hdis.symm
      ((union_comm V U).trans hcover) hVp.isConnected.isPreconnected hx
  have hI : polygonInterior p = U := by
    ext x
    constructor
    · intro hx
      have hxUV : x ∈ U ∪ V := hcover.symm ▸ hx.1
      rcases hxUV with hxU | hxV
      · exact hxU
      · exact (hVb (hKV hxV ▸ hx.2)).elim
    · intro hx
      refine ⟨show x ∈ (p.boundary ℝ)ᶜ from hcover ▸ Or.inl hx, ?_⟩
      rw [hKU hx]
      exact hUb
  have hO : polygonExterior p = V := by
    ext x
    constructor
    · intro hx
      have hxUV : x ∈ U ∪ V := hcover.symm ▸ hx.1
      rcases hxUV with hxU | hxV
      · exact (hx.2 ((hKU hxU).symm ▸ hUb)).elim
      · exact hxV
    · intro hx
      refine ⟨show x ∈ (p.boundary ℝ)ᶜ from hcover ▸ Or.inr hx, ?_⟩
      rw [hKV hx]
      exact hVb
  rw [hI, hO]
  exact ⟨hU, hV, hUp, hVp, hdis, hcover, hUb, hVb, hUf, hVf⟩

/-- The closed polygonal region is its inside together with its edge boundary;
the closure used in Munkres, Lemma 2.3, p. 195. -/
theorem IsSimplePolygon.closure_polygonInterior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    closure (polygonInterior p) = polygonInterior p ∪ p.boundary ℝ := by
  rw [closure_eq_self_union_frontier,
    (hp.polygonRegions_spec hdim).2.2.2.2.2.2.2.2.1]

/-- The outside is exactly the complement of the closed polygonal region;
auxiliary to Munkres, Lemma 2.3, p. 195. -/
theorem IsSimplePolygon.polygonExterior_eq_compl_closure_interior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    polygonExterior p = (closure (polygonInterior p))ᶜ := by
  obtain ⟨_, _, _, _, hdis, hcover, _⟩ := hp.polygonRegions_spec hdim
  rw [hp.closure_polygonInterior hdim]
  ext x
  constructor
  · intro hx hmem
    rcases hmem with hxI | hxC
    · exact Set.disjoint_left.mp hdis hxI hx
    · exact hx.1 hxC
  · intro hx
    have hxC : x ∉ p.boundary ℝ := fun hz => hx (Or.inr hz)
    have hxcover : x ∈ polygonInterior p ∪ polygonExterior p := hcover.symm ▸ hxC
    exact hxcover.resolve_left fun hz => hx (Or.inl hz)

/-- The closed bounded polygonal region is compact; the closure in Munkres,
Lemma 2.3, p. 195, using finite-dimensional Heine--Borel. -/
theorem IsSimplePolygon.isCompact_closure_polygonInterior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) : IsCompact (closure (polygonInterior p)) :=
  (hp.polygonRegions_spec hdim).2.2.2.2.2.2.1.isCompact_closure

end Poincare.Manifold.Schoenflies.Plane
