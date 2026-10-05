import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonCompactRegion

/-!
# Canonical inside and outside of a simple polygon

The bounded complementary component defines the inside; the
unbounded component defines the outside. See Erickson, Simple
Polygons, pp. 1--8 and M76 derivation 100.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Points in bounded components of the polygon complement.
For a simple planar polygon this is one component.
See Erickson pp. 1--4 and M76 derivation 100. -/
def inside (P : Polygon E n) : Set E :=
  {q | q ∈ (P.boundary ℝ)ᶜ ∧ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)}

/-- Points in unbounded components of the polygon complement.
See Erickson pp. 1--4 and M76 derivation 100. -/
def outside (P : Polygon E n) : Set E :=
  {q | q ∈ (P.boundary ℝ)ᶜ ∧ ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)}

/-- The inside and outside partition the boundary complement
for every polygon. See M76 derivation 100. -/
theorem compl_boundary_eq_inside_union_outside (P : Polygon E n) :
    (P.boundary ℝ)ᶜ = P.inside ∪ P.outside := by
  classical
  ext q
  simp only [inside, outside, mem_union, mem_ofPred_eq]
  tauto

/-- Inside and outside are disjoint by their complementary
boundedness conditions. See M76 derivation 100. -/
theorem disjoint_inside_outside (P : Polygon E n) : Disjoint P.inside P.outside :=
  Set.disjoint_left.mpr fun _ hi ho => ho.2 hi.2

/-- For a simple planar polygon, its canonical inside and outside
are the bounded and unbounded complementary components.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem exists_inside_outside_components (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      P.inside = connectedComponentIn (P.boundary ℝ)ᶜ a ∧
      P.outside = connectedComponentIn (P.boundary ℝ)ᶜ b ∧
      Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ b) := by
  obtain ⟨a, ha, b, hb, habound, hbunbound, hcover⟩ :=
    P.exists_bounded_unbounded_complement_components hP hinj
  refine ⟨a, ha, b, hb, ?_, ?_, habound, hbunbound⟩
  · apply Subset.antisymm
    · intro q hq
      rcases hcover ▸ hq.1 with hqa | hqb
      · exact hqa
      · exact (hbunbound (by rw [connectedComponentIn_eq hqb]; exact hq.2)).elim
    · intro q hq
      exact ⟨connectedComponentIn_subset _ _ hq, by rwa [← connectedComponentIn_eq hq]⟩
  · apply Subset.antisymm
    · intro q hq
      rcases hcover ▸ hq.1 with hqa | hqb
      · exact (hq.2 (by rwa [← connectedComponentIn_eq hqa])).elim
      · exact hqb
    · intro q hq
      exact ⟨connectedComponentIn_subset _ _ hq, by rwa [← connectedComponentIn_eq hq]⟩

variable (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

/-- The inside of a simple planar polygon is open.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem isOpen_inside : IsOpen P.inside := by
  obtain ⟨a, _, _, _, hI, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hI]
  exact P.isClosed_boundary.isOpen_compl.connectedComponentIn

/-- The outside of a simple planar polygon is open.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem isOpen_outside : IsOpen P.outside := by
  obtain ⟨_, _, b, _, _, hO, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hO]
  exact P.isClosed_boundary.isOpen_compl.connectedComponentIn

/-- The inside of a simple planar polygon is nonempty and
connected. See Erickson pp. 1--4 and M76 derivation 100. -/
theorem isConnected_inside : IsConnected P.inside := by
  obtain ⟨a, ha, _, _, hI, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hI]
  exact isConnected_connectedComponentIn_iff.mpr ha

/-- The outside of a simple planar polygon is nonempty and
connected. See Erickson pp. 1--4 and M76 derivation 100. -/
theorem isConnected_outside : IsConnected P.outside := by
  obtain ⟨_, _, b, hb, _, hO, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hO]
  exact isConnected_connectedComponentIn_iff.mpr hb

/-- The inside of a simple planar polygon is bounded.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem isBounded_inside : Bornology.IsBounded P.inside := by
  obtain ⟨_, _, _, _, hI, _, hbound, _⟩ := P.exists_inside_outside_components hP hinj
  rwa [hI]

/-- The outside of a simple planar polygon is unbounded.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem not_isBounded_outside : ¬ Bornology.IsBounded P.outside := by
  obtain ⟨_, _, _, _, _, hO, _, hunbound⟩ := P.exists_inside_outside_components hP hinj
  rwa [hO]

/-- The entire polygon is the frontier of its inside.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem frontier_inside : frontier P.inside = P.boundary ℝ := by
  obtain ⟨a, ha, _, _, hI, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hI]
  exact P.frontier_complement_component hP hinj ha

/-- The entire polygon is the frontier of its outside.
See Erickson pp. 1--4 and M76 derivation 100. -/
theorem frontier_outside : frontier P.outside = P.boundary ℝ := by
  obtain ⟨_, _, b, hb, _, hO, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hO]
  exact P.frontier_complement_component hP hinj hb

/-- The closed filled polygon is the complement of the outside.
See Erickson pp. 4, 6--8 and M76 derivation 100. -/
theorem closure_inside : closure P.inside = P.outsideᶜ :=
  closure_eq_compl_of_complementary_regions P.compl_boundary_eq_inside_union_outside
    P.disjoint_inside_outside (P.frontier_inside hP hinj)

/-- The inside is the exact interior of the closed filled polygon.
See Erickson pp. 4, 6--8 and M76 derivation 100. -/
theorem interior_closure_inside : interior (closure P.inside) = P.inside :=
  interior_closure_eq_of_complementary_regions P.compl_boundary_eq_inside_union_outside
    P.disjoint_inside_outside (P.frontier_inside hP hinj) (P.frontier_outside hP hinj)

/-- The closed filled polygon has exactly the polygon as frontier.
See Erickson pp. 4, 6--8 and M76 derivation 100. -/
theorem frontier_closure_inside : frontier (closure P.inside) = P.boundary ℝ :=
  frontier_closure_eq_of_complementary_regions P.compl_boundary_eq_inside_union_outside
    P.disjoint_inside_outside (P.frontier_inside hP hinj) (P.frontier_outside hP hinj)

/-- The closed filled polygon is compact.
See Erickson pp. 4, 6--8 and M76 derivation 100. -/
theorem isCompact_closure_inside : IsCompact (closure P.inside) :=
  (P.isBounded_inside hP hinj).isCompact_closure

end Polygon
