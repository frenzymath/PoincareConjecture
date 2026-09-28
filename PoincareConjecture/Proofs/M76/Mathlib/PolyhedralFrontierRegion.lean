import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronNeighborhoodRetraction
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity
import PoincareConjecture.Proofs.M76.Mathlib.ConvexIntrinsicInterior
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_subcomplex_of_frontier
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hJK : J ≤ K) {S : Set E} (hS : IsClosed S)
    (hreg : closure (interior S) = S) (hSK : S ⊆ K.space)
    (hfront : J.space = frontier S) :
    ∃ L : SimplicialComplex ℝ E, L ≤ K ∧ J ≤ L ∧ L.space = S := by
  classical
  let L : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ S}
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }
  have hLK : L ≤ K := fun _ hs => hs.1
  have hLS : L.space ⊆ S := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact hs.2 hxs
  have hJL : J ≤ L := by
    intro s hs
    refine ⟨hJK hs, ?_⟩
    intro x hx
    exact hS.frontier_subset (hfront ▸ J.convexHull_subset_space hs hx)
  have hfi : frontier (interior S) = frontier S := by
    simp only [frontier, interior_interior, hreg, hS.closure_eq]
  have hinside : interior S ⊆ L.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK
      (hSK (interior_subset hx))
    have hdis : Disjoint (frontier (interior S))
        (intrinsicInterior ℝ (convexHull ℝ (s : Set E))) := by
      rw [hfi]
      apply disjoint_left.mpr
      intro y hy hyi
      obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp (hfront.symm ▸ hy)
      have hst := K.subset_of_mem_intrinsicInterior_face hs (hJK ht) hyi hyt
      have hxfront : x ∈ frontier S := hfront ▸
        J.convexHull_subset_space ht (convexHull_mono hst (intrinsicInterior_subset hxs))
      exact hxfront.2 hx
    have hrel : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ⊆ interior S :=
      (convex_convexHull ℝ (s : Set E)).intrinsicInterior.isPreconnected
        |>.m76_subset_of_disjoint_frontier isOpen_interior hdis ⟨x, hxs, hx⟩
    have hface : convexHull ℝ (s : Set E) ⊆ S :=
      (convex_convexHull ℝ (s : Set E)).subset_closure_intrinsicInterior.trans
        (closure_minimal (hrel.trans interior_subset) hS)
    exact mem_space_iff.mpr ⟨s, ⟨hs, hface⟩, intrinsicInterior_subset hxs⟩
  have hclosed : IsClosed L.space := (L.isCompact_space_of_finite (hK.subset hLK)).isClosed
  refine ⟨L, hLK, hJL, hLS.antisymm ?_⟩
  rw [← hreg]
  exact closure_minimal hinside hclosed

theorem exists_finite_triangulation_of_polyhedral_frontier
    {S : Set E} (hS : IsCompact S) (hreg : closure (interior S) = S)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hfront : J.space = frontier S) :
    ∃ K L : SimplicialComplex ℝ E, K.faces.Finite ∧ L ≤ K ∧
      K.space = S ∧ L.space = frontier S := by
  obtain ⟨T, hT, hST, _⟩ :=
    exists_finite_neighborhood_subset_normed hS isOpen_univ (subset_univ S)
  have hJT : J.space ⊆ T.space := by
    rw [hfront]
    exact hS.isClosed.frontier_subset.trans (hST.trans interior_subset)
  obtain ⟨R, L, hR, hRT, hLR, hLJ⟩ :=
    T.exists_subdivision_with_polyhedron_subcomplex J hT hJ hJT
  obtain ⟨K, hKR, hLK, hKS⟩ := R.exists_subcomplex_of_frontier L hR hLR
    hS.isClosed hreg
    ((hST.trans interior_subset).trans hRT.space_eq.symm.subset)
    (hLJ.trans hfront)
  exact ⟨K, L, hR.subset hKR, hLK, hKS, hLJ.trans hfront⟩

end Geometry.SimplicialComplex
