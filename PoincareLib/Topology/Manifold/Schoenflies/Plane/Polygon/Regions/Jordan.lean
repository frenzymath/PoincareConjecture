import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.LocalSides
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Parity.ParitySeparation
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.ExteriorComponent
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Polygonal Jordan separation

The separation conclusion of Cairns (1951), Theorem 2.1, pp. 860-861.
Local sides, parity, and connected-component frontiers give exactly two
complement components. Ball exteriors identify the bounded inside and
unbounded outside, with the entire polygon as the frontier of each.
The simplicity predicate permits straight vertices, as in Munkres (1960),
Definition 2.2 and Lemma 2.3, p. 195.
See `smale/derivations/2026-09-21-polygon-jordan.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} {p : Polygon E n}

/-- Every complement component has the whole simple planar polygon as frontier;
the frontier conclusion of Cairns, Theorem 2.1, pp. 860-861. -/
theorem IsSimplePolygon.frontier_compl_component_eq (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) {x : E} (hx : x ∉ p.boundary ℝ) :
    frontier (connectedComponentIn (p.boundary ℝ)ᶜ x) = p.boundary ℝ := by
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le
  exact (hp.hasLocalTwoSides hdim).frontier_compl_component_eq
    (polygon_boundary_isClosed p) (polygon_boundary_isConnected p hn) hx

/-- The complement of a simple planar polygon consists of exactly two distinct
connected components; Cairns, Theorem 2.1, pp. 860-861. -/
theorem IsSimplePolygon.exists_two_compl_components (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ a ∉ p.boundary ℝ, ∃ b ∉ p.boundary ℝ,
      connectedComponentIn (p.boundary ℝ)ᶜ a ≠ connectedComponentIn (p.boundary ℝ)ᶜ b ∧
        connectedComponentIn (p.boundary ℝ)ᶜ a ∪ connectedComponentIn (p.boundary ℝ)ᶜ b =
          (p.boundary ℝ)ᶜ := by
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le
  exact (hp.hasLocalTwoSides hdim).exists_two_distinct_compl_components
    (polygon_boundary_isClosed p) (polygon_boundary_isConnected p hn)
    (hp.not_isPreconnected_compl hdim)

/-- A simple planar polygon separates a bounded inside from an unbounded
outside, both open and path connected with that frontier; Cairns, 2.1, pp. 860-861. -/
theorem IsSimplePolygon.exists_inside_outside (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ U V : Set E, IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ U ∪ V = (p.boundary ℝ)ᶜ ∧ Bornology.IsBounded U ∧
      ¬ Bornology.IsBounded V ∧ frontier U = p.boundary ℝ ∧ frontier V = p.boundary ℝ := by
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, hdim]
    norm_num
  obtain ⟨x, hx, hxnb, hbounded⟩ :=
    exists_unbounded_compl_component hrank (polygon_boundary_isBounded p)
  obtain ⟨a, ha, b, hb, hne, hcover⟩ := hp.exists_two_compl_components hdim
  let K := connectedComponentIn (p.boundary ℝ)ᶜ
  let P (U V : Set E) : Prop :=
    IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ U ∪ V = (p.boundary ℝ)ᶜ ∧ Bornology.IsBounded U ∧
      ¬ Bornology.IsBounded V ∧ frontier U = p.boundary ℝ ∧ frontier V = p.boundary ℝ
  change ∃ U V, P U V
  have hopen (z : E) : IsOpen (K z) :=
    (polygon_boundary_isClosed p).isOpen_compl.connectedComponentIn
  have hpath {z : E} (hz : z ∉ p.boundary ℝ) : IsPathConnected (K z) :=
    (hopen z).isConnected_iff_isPathConnected.mp (isConnected_connectedComponentIn_iff.mpr hz)
  have hbuild (a b : E) (ha : a ∉ p.boundary ℝ) (hb : b ∉ p.boundary ℝ)
      (hne : K a ≠ K b) (hcover : K a ∪ K b = (p.boundary ℝ)ᶜ)
      (hbext : K b = K x) : P (K a) (K b) := by
    have hane : K a ≠ K x := by rwa [← hbext]
    refine ⟨hopen a, hopen b, hpath ha, hpath hb, ?_, hcover,
      hbounded a ha hane, ?_, hp.frontier_compl_component_eq hdim ha,
      hp.frontier_compl_component_eq hdim hb⟩
    · exact Set.disjoint_left.mpr fun z hza hzb =>
        hne ((connectedComponentIn_eq hza).trans (connectedComponentIn_eq hzb).symm)
    · rw [hbext]
      exact hxnb
  have hxcover : x ∈ K a ∪ K b := hcover.symm ▸ hx
  rcases hxcover with hxa | hxb
  · exact ⟨K b, K a, hbuild b a hb ha hne.symm
      ((union_comm (K b) (K a)).trans hcover) (connectedComponentIn_eq hxa)⟩
  · exact ⟨K a, K b, hbuild a b ha hb hne hcover (connectedComponentIn_eq hxb)⟩

end Poincare.Manifold.Schoenflies.Plane
