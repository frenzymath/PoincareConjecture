import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.ChartStars
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem subdivision_preserves_original_chart_stars
    {E X V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [DecidableEq E]
    {e : ι → OpenPartialHomeomorph X V}
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N.IsSubdivision K)
    (g : E → X)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g)) :
    ∀ p ∈ N.vertices, ∃ B : OpenPartialHomeomorph X V,
      MapsTo g (N.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V) ∧
      (N.closedStar p).AffineOnFaces (B ∘ g) := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := K.exists_face_intrinsicInterior_of_finite hK
    (hNK.space_eq.subset (N.vertices_subset_space hp))
  obtain ⟨q, hqa⟩ := K.nonempty_of_mem_faces ha
  obtain ⟨B, hmap, hB, hface⟩ := hstars q (K.face_subset_vertices ha hqa)
  have hcontain : ∀ s ∈ (N.closedStar p).faces, ∃ t ∈ (K.closedStar q).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hNK.face_subset (insert p s) hs.2
    have hpt : p ∈ convexHull ℝ (t : Set E) := hst (subset_convexHull ℝ _ (by simp))
    have hqt : q ∈ t := K.subset_of_mem_intrinsicInterior_face ha ht hpa hpt hqa
    exact ⟨t, ⟨ht, by simpa only [Finset.insert_eq_of_mem hqt] using ht⟩,
      (convexHull_mono (Finset.subset_insert p s)).trans hst⟩
  refine ⟨B, ?_, hB, hface.of_face_containment hcontain⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := hcontain s hs
  exact hmap ((K.closedStar q).convexHull_subset_space ht (hst hxs))

theorem subdivision_preserves_active_original_charts
    {E X V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V} {g : E → X} {mark : Set X}
    (K M N L : SimplicialComplex ℝ E) (hNK : N.IsSubdivision K)
    (hLN : L ≤ N) (hLs : L.space = M.space)
    (hcharts : ∀ s ∈ K.faces, s ∉ M.faces →
      ∃ (B : OpenPartialHomeomorph X V) (A : E →ᴬ[ℝ] V),
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V) ∧
        Disjoint B.source mark ∧ MapsTo g (convexHull ℝ (s : Set E)) B.source ∧
        EqOn (B ∘ g) A (convexHull ℝ (s : Set E))) :
    ∀ s ∈ N.faces, s ∉ L.faces →
      ∃ (B : OpenPartialHomeomorph X V) (A : E →ᴬ[ℝ] V),
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V) ∧
        Disjoint B.source mark ∧ MapsTo g (convexHull ℝ (s : Set E)) B.source ∧
        EqOn (B ∘ g) A (convexHull ℝ (s : Set E)) := by
  intro s hs hsL
  obtain ⟨t, ht, hst⟩ := hNK.face_subset s hs
  have htM : t ∉ M.faces := by
    intro htM
    obtain ⟨x, hxs⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
      (Finset.coe_nonempty.mpr (N.nonempty_of_mem_faces hs)).convexHull
    exact hsL (N.face_mem_subcomplex_of_intrinsicInterior L hLN hs hxs
      (hLs.symm.subset (M.convexHull_subset_space htM (hst (intrinsicInterior_subset hxs)))))
  obtain ⟨B, A, hB, hmark, hmap, hA⟩ := hcharts t ht htM
  exact ⟨B, A, hB, hmark, hmap.mono_left hst, hA.mono hst⟩

theorem protected_active_edge_subset_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K M : SimplicialComplex ℝ E) (hMK : M ≤ K)
    {z : E → ℝ} (hz : Continuous z) {c : ℝ}
    (hMs : M.space = K.space ∩ {x | z x ≤ c})
    {a s : Finset E} (ha : a ∈ M.faces) (hs : s ∈ K.faces)
    (hsM : s ∉ M.faces) (has : a ⊆ s) :
    convexHull ℝ (a : Set E) ⊆ {x | x ∈ K.space ∧ z x = c} := by
  intro x hx
  have hxM := M.convexHull_subset_space ha hx
  have hxc := (hMs.subset hxM).2
  refine ⟨(hMs.subset hxM).1, le_antisymm hxc ?_⟩
  by_contra hn
  have hlt : z x < c := lt_of_not_ge hn
  obtain ⟨y, hys, hy⟩ := (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
    (isOpen_lt hz continuous_const) ⟨x, convexHull_mono has hx, hlt⟩
  exact hsM (K.face_mem_subcomplex_of_intrinsicInterior M hMK hs hys
    (hMs.symm.subset ⟨K.convexHull_subset_space hs (intrinsicInterior_subset hys),
      (show z y ≤ c from le_of_lt hy)⟩))

end PoincareConjecture.M76
