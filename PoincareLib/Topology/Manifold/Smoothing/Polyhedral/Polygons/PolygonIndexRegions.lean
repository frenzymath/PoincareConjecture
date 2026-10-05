import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonExteriorIndex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonUnitJump

/-!
# The signed crossing index detects polygon regions

The index is zero outside and is a single value +1 or -1 inside.
No orientation is prescribed. See Erickson, Simple Polygons,
pp. 4--8 and M76 derivation 101.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
  (hnv : P.HasNonverticalEdges)

include hP hinj hnv

/-- The index of a simple nonvertical polygon is zero precisely
on its unbounded component and a constant +1 or -1 precisely on
its bounded component. See Erickson pp. 4--8 and derivation 101. -/
theorem exists_crossingIndex_region_value :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ∀ q ∈ (P.boundary ℝ)ᶜ,
      (P.crossingIndex q = c ↔ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)) ∧
      (P.crossingIndex q = 0 ↔ ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)) := by
  obtain ⟨a, ha, b, hb, habounded, hbunbounded, hcover⟩ :=
    P.exists_bounded_unbounded_complement_components hP hinj
  have hbzero := P.crossingIndex_eq_zero_of_unbounded_component hnv hb hbunbounded
  have hconstant {x q : ℝ × ℝ} (hx : x ∈ (P.boundary ℝ)ᶜ)
      (hq : q ∈ connectedComponentIn (P.boundary ℝ)ᶜ x) :
      P.crossingIndex q = P.crossingIndex x :=
    P.crossingIndex_eq_on_preconnected hnv isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hq (mem_connectedComponentIn hx)
  have hvalues (q : ℝ × ℝ) (hq : q ∈ (P.boundary ℝ)ᶜ) :
      P.crossingIndex q = P.crossingIndex a ∨ P.crossingIndex q = 0 := by
    rcases hcover ▸ hq with hqa | hqb
    · exact Or.inl (hconstant ha hqa)
    · exact Or.inr ((hconstant hb hqb).trans hbzero)
  obtain ⟨x, hx, y, hy, hjump⟩ := P.exists_crossingIndex_unit_jump hP hinj hnv
  have hxvalue := hvalues x hx
  have hyvalue := hvalues y hy
  have hc : P.crossingIndex a = 1 ∨ P.crossingIndex a = -1 := by omega
  have hcne : P.crossingIndex a ≠ 0 := by omega
  refine ⟨P.crossingIndex a, hc, ?_⟩
  intro q hq
  rcases hcover ▸ hq with hqa | hqb
  · have hqvalue := hconstant ha hqa
    have hqbound : Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q) := by
      rwa [← connectedComponentIn_eq hqa]
    simp [hqvalue, hqbound, hcne]
  · have hqvalue := (hconstant hb hqb).trans hbzero
    have hqunbound : ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q) := by
      rwa [← connectedComponentIn_eq hqb]
    simp [hqvalue, hqunbound, hcne.symm]

/-- Zero index characterizes the unbounded component of a simple
nonvertical polygon. Boundary queries are excluded.
See Erickson pp. 4--6 and M76 derivation 101. -/
theorem crossingIndex_eq_zero_iff_unbounded {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    P.crossingIndex q = 0 ↔ ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q) := by
  obtain ⟨_, _, h⟩ := P.exists_crossingIndex_region_value hP hinj hnv
  exact (h q hq).2

/-- Off a simple nonvertical polygon, the signed crossing index
takes only the values -1, 0, and +1. See Erickson pp. 4--8 and
M76 derivation 101. -/
theorem crossingIndex_mem_three {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    P.crossingIndex q = -1 ∨ P.crossingIndex q = 0 ∨ P.crossingIndex q = 1 := by
  classical
  obtain ⟨c, hc, h⟩ := P.exists_crossingIndex_region_value hP hinj hnv
  by_cases hbound : Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)
  · have hqvalue := (h q hq).1.mpr hbound
    omega
  · exact Or.inr (Or.inl ((h q hq).2.mpr hbound))

end Polygon
