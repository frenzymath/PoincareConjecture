import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricNeighborhoodRetraction
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralRefinement
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AlignedHalfspaceFaces

/-!
# Finite PL neighborhood retractions onto actual polyhedra

Barycentric subdivision first makes a subcomplex full. A second
subdivision gives its actual finite neighborhood and affine
retraction. Aligning an ambient triangulation with all target
simplices then gives a retraction from an ambient neighborhood
onto any prescribed finite polyhedron. See Hudson 1969,
pp. 8--9, 12--19 and M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every finite subcomplex has an actual finite relative
neighborhood with a finite PL retraction fixing its entire
carrier. Fullness is obtained internally by subdivision.
See Hudson pp. 8--9, 15--19 and M76 derivation 270. -/
theorem exists_subcomplex_neighborhood_retraction
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hLK : L ≤ K) :
    ∃ (N : SimplicialComplex ℝ E) (r : E → E) (U : Set E),
      N.faces.Finite ∧ N.space ⊆ K.space ∧ IsOpen U ∧ L.space ⊆ U ∧
      U ∩ K.space ⊆ N.space ∧ N.AffineOnFaces r ∧
      MapsTo r N.space L.space ∧ EqOn r id L.space := by
  classical
  let : Fintype K.faces := hK.fintype
  let : Fintype L.faces := hL.fintype
  let K' := K.barycentricSubdivision
  let L' := L.barycentricSubdivision
  let : Fintype K'.faces := K.barycentricSubdivision_finite.fintype
  let : Fintype L'.faces := L.barycentricSubdivision_finite.fintype
  have hLK' : L' ≤ K' := L.barycentricSubdivision_mono hLK
  have hfull : ∀ s ∈ K'.faces, (∀ v ∈ s, v ∈ L'.vertices) → s ∈ L'.faces :=
    fun _ hs hv => K.barycentricSubdivision_full hLK hs hv
  obtain ⟨r, hr, hmap, hfix⟩ := K'.exists_barycentricNeighborhood_retraction hLK' hfull
  obtain ⟨U, hU, hLU, hUN⟩ := K'.exists_open_barycentricNeighborhood hLK'
  let N := K'.barycentricNeighborhood L'
  have hK'space : K'.space = K.space := K.barycentricSubdivision_isSubdivision.space_eq
  have hL'space : L'.space = L.space := L.barycentricSubdivision_isSubdivision.space_eq
  refine ⟨N, r, U, K'.barycentricNeighborhood_finite L', ?_, hU, ?_, ?_, hr, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    have hx' : x ∈ K'.barycentricSubdivision.space :=
      K'.barycentricSubdivision.convexHull_subset_space
        (K'.barycentricNeighborhood_le L' hs) hxs
    rwa [K'.barycentricSubdivision_isSubdivision.space_eq, hK'space] at hx'
  · rwa [hL'space] at hLU
  · rwa [hK'space] at hUN
  · rwa [hL'space] at hmap
  · rwa [hL'space] at hfix

/-- A finite polyhedron inside a finite carrier becomes the
exact carrier of a subcomplex after subdividing the ambient
complex. All original ambient points are retained. See Hudson
pp. 12--14 and M76 derivation 270. -/
theorem exists_subdivision_with_polyhedron_subcomplex
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (hJK : J.space ⊆ K.space) :
    ∃ R L : SimplicialComplex ℝ E, R.faces.Finite ∧ R.IsSubdivision K ∧
      L ≤ R ∧ L.space = J.space := by
  classical
  let : Fintype J.faces := hJ.fintype
  choose H hH using fun t : J.faces =>
    t.val.exists_affine_halfspaces_convexHull (J.indep t.property)
  let Htotal := Finset.univ.biUnion H
  let n := hK.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨R, hR, hRK, _, hRH⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hn Htotal
  let L : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ R.faces ∧ convexHull ℝ (s : Set E) ⊆ J.space}
      indep := fun hs => R.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨R.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨R.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht => R.inter_subset_convexHull hs.1 ht.1 }
  refine ⟨R, L, hR, hRK, fun _ hs => hs.1, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact hs.2 hxs
  · intro hx
    have hxR : x ∈ R.space := hRK.space_eq.symm ▸ hJK hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    let i : J.faces := ⟨t, ht⟩
    have hHi : ∀ A ∈ H i, R.RespectsAffineHyperplane A := fun A hA =>
      hRH A (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩)
    have hxH : ∀ A ∈ H i, A x ≤ 0 := by
      change x ∈ {y | ∀ A ∈ H i, A y ≤ 0}
      rw [← hH i]
      exact hxt
    obtain ⟨s, hs, hxs, hsH⟩ := R.exists_face_in_halfspaces (H i) hHi hxR hxH
    have hst : (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
      intro v hv
      rw [hH i]
      exact hsH v hv
    have hsJ : convexHull ℝ (s : Set E) ⊆ J.space :=
      (convexHull_min hst (convex_convexHull ℝ _)).trans (J.convexHull_subset_space ht)
    exact mem_space_iff.mpr ⟨s, ⟨hs, hsJ⟩, hxs⟩

/-- A finite polyhedron has an actual compact polyhedral
neighborhood inside every prescribed open neighborhood, with
a finite PL retraction fixing the whole original polyhedron.
See Hudson pp. 8--9, 12--19 and M76 derivation 270. -/
theorem exists_finitePL_neighborhood_retraction
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) {W : Set E}
    (hW : IsOpen W) (hJW : J.space ⊆ W) :
    ∃ (N : SimplicialComplex ℝ E) (r : E → E),
      N.faces.Finite ∧ J.space ⊆ interior N.space ∧ N.space ⊆ W ∧
      N.AffineOnFaces r ∧ MapsTo r N.space J.space ∧ EqOn r id J.space := by
  obtain ⟨K, hK, hJK, hKW⟩ := exists_finite_neighborhood_subset_normed
    (J.isCompact_space_of_finite hJ) hW hJW
  obtain ⟨R, L, hR, hRK, hLR, hLJ⟩ :=
    K.exists_subdivision_with_polyhedron_subcomplex J hK hJ (hJK.trans interior_subset)
  have hL : L.faces.Finite := hR.subset hLR
  obtain ⟨N, r, U, hN, hNR, hU, hLU, hUN, hr, hmap, hfix⟩ :=
    R.exists_subcomplex_neighborhood_retraction L hR hL hLR
  refine ⟨N, r, hN, ?_, hNR.trans (hRK.space_eq.subset.trans hKW), hr, ?_, ?_⟩
  · have hinside : U ∩ interior R.space ⊆ N.space :=
      fun _ hx => hUN ⟨hx.1, interior_subset hx.2⟩
    intro x hx
    apply interior_maximal hinside (hU.inter isOpen_interior)
    refine ⟨hLU (hLJ.symm ▸ hx), ?_⟩
    rw [hRK.space_eq]
    exact hJK hx
  · rwa [hLJ] at hmap
  · rwa [hLJ] at hfix

end Geometry.SimplicialComplex
