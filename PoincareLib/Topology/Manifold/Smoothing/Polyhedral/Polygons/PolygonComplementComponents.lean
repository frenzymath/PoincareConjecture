import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonLocalLineModel
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonCircle
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonSeparation

/-!
# The two complementary components of a simple polygon

The boundary circle and explicit local sides give at most two
components, each with the whole polygon as frontier. For
nonvertical edges the crossing index makes them distinct.
See Erickson, Simple Polygons, pp. 2--4 and M76 derivation 97.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

/-- The boundary of a simple planar polygon is nonempty and
connected, by its checked circle homeomorphism.
See Erickson pp. 2--3 and M76 derivation 97. -/
theorem isConnected_boundary : IsConnected (P.boundary ℝ) := by
  obtain ⟨e⟩ := P.nonempty_boundary_homeomorph_circle hP hinj
  exact isConnected_iff_connectedSpace.mpr
    (e.connectedSpace_iff.mpr inferInstance)

/-- Every complementary component of a simple polygon has the
entire polygon as its frontier. No orientation restriction is
needed. See Erickson pp. 2--3 and M76 derivation 97. -/
theorem frontier_complement_component {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    frontier (connectedComponentIn (P.boundary ℝ)ᶜ q) = P.boundary ℝ :=
  (P.hasLocalComplementarySides_boundary hP hinj).frontier_component_eq
    P.isClosed_boundary (P.isConnected_boundary hP hinj) hq

/-- Two complementary components exhaust the complement of a
simple polygon. Distinctness is established separately using
the crossing index. See Erickson pp. 2--3 and M76 derivation 97. -/
theorem exists_two_complement_components :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ a ∪
        connectedComponentIn (P.boundary ℝ)ᶜ b := by
  obtain ⟨a, ha, b, hb, hcomponents⟩ :=
    (P.hasLocalComplementarySides_boundary hP hinj).exists_two_components
      P.isClosed_boundary (P.isConnected_boundary hP hinj)
  refine ⟨a, ha, b, hb, Subset.antisymm ?_ ?_⟩
  · intro q hq
    rcases hcomponents q hq with heq | heq
    · exact Or.inl (heq ▸ mem_connectedComponentIn hq)
    · exact Or.inr (heq ▸ mem_connectedComponentIn hq)
  · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)

/-- A nonvertical simple polygon separates the plane into exactly
two distinct components. Their openness and common frontier follow
from the preceding local-side results. See Erickson pp. 2--4 and
M76 derivation 97. -/
theorem exists_distinct_two_complement_components_of_nonvertical
    (hnv : P.HasNonverticalEdges) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      connectedComponentIn (P.boundary ℝ)ᶜ a ≠ connectedComponentIn (P.boundary ℝ)ᶜ b ∧
      (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ a ∪
        connectedComponentIn (P.boundary ℝ)ᶜ b := by
  obtain ⟨a, ha, b, hb, hcover⟩ := P.exists_two_complement_components hP hinj
  refine ⟨a, ha, b, hb, ?_, hcover⟩
  intro heq
  have hsingle : (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ b := by
    simpa only [heq, union_self] using hcover
  apply P.not_isPreconnected_compl_of_nonvertical hP hinj hnv
  rw [hsingle]
  exact isPreconnected_connectedComponentIn

end Polygon
