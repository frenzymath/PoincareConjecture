import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedronNeighborhoodRetraction
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralUnions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionIntrinsicDensity

/-!
# Finite residual polyhedra after removing an open collar strip

Align the closed strip with a finite ambient triangulation. The closures
of the remaining face interiors triangulate the closed complement;
adding the complete strip roof gives the precise residual carrier.
See Hudson 1969, pp.12--19, and Hatcher 2014, Corollary 3.2, p.57.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The closure of the complement of a finite subcomplex has its own
finite triangulation, including every limiting face on the interface. -/
theorem exists_triangulation_closed_subcomplex_complement
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      J.space = closure (K.space \ L.space) := by
  classical
  let I := {s : Finset E // s ∈ K.faces ∧ s ∉ L.faces}
  let : Finite I := (hK.subset (show {s | s ∈ K.faces ∧ s ∉ L.faces} ⊆ K.faces
    from fun _ hs ↦ hs.1)).to_subtype
  obtain ⟨J, hJ, hJs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun s : I ↦ s.val) (fun s ↦ K.indep s.property.1)
  refine ⟨J, hJ, Subset.antisymm ?_ ?_⟩
  · rw [hJs]
    intro x hx
    obtain ⟨s, hxs⟩ := mem_iUnion.mp hx
    have hrel : intrinsicInterior ℝ (convexHull ℝ (s.val : Set E)) ⊆
        K.space \ L.space := by
      intro y hy
      refine ⟨K.convexHull_subset_space s.property.1 (intrinsicInterior_subset hy), ?_⟩
      intro hyL
      obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp hyL
      have hst := K.subset_of_mem_intrinsicInterior_face s.property.1 (hLK ht) hy hyt
      exact s.property.2 (L.down_closed ht hst (K.nonempty_of_mem_faces s.property.1))
    exact closure_mono hrel
      ((convex_convexHull ℝ (s.val : Set E)).subset_closure_intrinsicInterior hxs)
  · apply closure_minimal ?_ (J.isCompact_space_of_finite hJ).isClosed
    rintro x ⟨hxK, hxL⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxK
    have hsL : s ∉ L.faces := fun hsL ↦ hxL (L.convexHull_subset_space hsL hxs)
    rw [hJs]
    exact mem_iUnion.mpr ⟨⟨s, hs, hsL⟩, hxs⟩

/-- The same closed-complement construction first aligns two actual
finite polyhedra; compatible input triangulations are unnecessary. -/
theorem exists_triangulation_closed_polyhedral_complement
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hLK : L.space ⊆ K.space) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      J.space = closure (K.space \ L.space) := by
  obtain ⟨R, A, hR, hRK, hAR, hAL⟩ :=
    K.exists_subdivision_with_polyhedron_subcomplex L hK hL hLK
  obtain ⟨J, hJ, hJs⟩ := exists_triangulation_closed_subcomplex_complement R A hR hAR
  exact ⟨J, hJ, by simpa only [hRK.space_eq, hAL] using hJs⟩

/-- Removing a relatively open strip from a finite carrier leaves a
finite residual, provided the closed strip and its exact roof are finite
polyhedra. This supplies the identity piece in inward collar compression. -/
theorem exists_triangulation_collar_residual
    (K C B : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hC : C.faces.Finite) (hB : B.faces.Finite)
    (hCK : C.space ⊆ K.space) {O : Set E} (hOC : O ⊆ C.space)
    (hroof : C.space \ O = B.space) (hclosed : IsClosed (K.space \ O)) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ J.space = K.space \ O := by
  obtain ⟨L, hL, hLs⟩ := exists_triangulation_closed_polyhedral_complement K C hK hC hCK
  obtain ⟨J, hJ, hJs⟩ := L.exists_finite_triangulation_union B hL hB
  refine ⟨J, hJ, hJs.trans ?_⟩
  rw [hLs, ← hroof]
  apply Subset.antisymm
  · apply union_subset
    · exact closure_minimal (sdiff_subset_sdiff_right hOC) hclosed
    · exact sdiff_subset_sdiff_left hCK
  · rintro x ⟨hxK, hxO⟩
    by_cases hxC : x ∈ C.space
    · exact Or.inr ⟨hxC, hxO⟩
    · exact Or.inl (subset_closure ⟨hxK, hxC⟩)

end PoincareMT.M76.Dehn
