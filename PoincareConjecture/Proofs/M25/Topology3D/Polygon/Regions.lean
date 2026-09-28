import PoincareConjecture.Proofs.M25.Topology3D.Plane.ComponentCover
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.Jordan
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def polygonInterior (p : Polygon E n) : Set E :=
  {x | x ∉ p.boundary ℝ ∧ Bornology.IsBounded (connectedComponentIn (p.boundary ℝ)ᶜ x)}

def polygonExterior (p : Polygon E n) : Set E :=
  {x | x ∉ p.boundary ℝ ∧ ¬ Bornology.IsBounded (connectedComponentIn (p.boundary ℝ)ᶜ x)}

variable [FiniteDimensional ℝ E] {p : Polygon E n}

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

theorem IsSimplePolygon.closure_polygonInterior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    closure (polygonInterior p) = polygonInterior p ∪ p.boundary ℝ := by
  rw [closure_eq_self_union_frontier,
    (hp.polygonRegions_spec hdim).2.2.2.2.2.2.2.2.1]

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

theorem IsSimplePolygon.isCompact_closure_polygonInterior (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) : IsCompact (closure (polygonInterior p)) :=
  (hp.polygonRegions_spec hdim).2.2.2.2.2.2.1.isCompact_closure

end PoincareConjecture.M25.Topology3D
