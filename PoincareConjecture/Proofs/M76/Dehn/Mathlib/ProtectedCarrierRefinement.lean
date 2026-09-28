import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCompatibleUnion










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem mem_subcomplex_vertices_of_mem_space
    {J K : SimplicialComplex ℝ E} (hKJ : K ≤ J) {v : E}
    (hv : v ∈ J.vertices) (hvK : v ∈ K.space) : v ∈ K.vertices := by
  obtain ⟨s, hs, hvs⟩ := mem_space_iff.mp hvK
  exact K.down_closed hs
    (Finset.singleton_subset_iff.mpr ((J.vertex_mem_convexHull_iff hv (hKJ hs)).mp hvs))
    (Finset.singleton_nonempty v)




theorem exists_finite_convex_frontier_triangulation
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space) :
    ∃ B : SimplicialComplex ℝ E, B.faces.Finite ∧ B.space = frontier J.space := by
  have hclosed := (J.isCompact_space_of_finite hJ).isClosed
  by_cases hi : (interior J.space).Nonempty
  · exact ⟨J.frontierSubcomplex J.space, J.frontierSubcomplex_finite _ hJ,
      J.frontierSubcomplex_space hclosed hcv hi rfl⟩
  · have hempty : interior J.space = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    have hf : frontier J.space = J.space := by
      rw [frontier, hclosed.closure_eq, hempty, sdiff_empty]
    exact ⟨J, hJ, hf.symm⟩




theorem exists_protected_carrier_refinement [FiniteDimensional ℝ E]
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space) :
    ∃ R K K₀ Q : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ K ≤ R ∧ K.space = P.space ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      Q ≤ R ∧ Q.space = P₀.space ∪ frontier J.space ∧
      ∀ v ∈ K.vertices, v ∉ K₀.vertices → v ∉ Q.vertices := by
  classical
  obtain ⟨B, hB, hBs⟩ := J.exists_finite_convex_frontier_triangulation hJ hcv
  let M : Option Bool → SimplicialComplex ℝ E
    | none => B
    | some false => P₀
    | some true => P
  have hM : ∀ i, (M i).faces.Finite := by
    intro i
    cases i with
    | none => exact hB
    | some b => cases b <;> assumption
  have hMJ : ∀ i, (M i).space ⊆ J.space := by
    intro i
    cases i with
    | none =>
      change B.space ⊆ J.space
      rw [hBs]
      exact (J.isCompact_space_of_finite hJ).isClosed.frontier_subset
    | some b =>
      cases b
      · exact hP₀P.trans hPJ
      · exact hPJ
  obtain ⟨R, L, hR, hRJ, hL⟩ :=
    J.exists_subdivision_with_finite_full_polyhedra hJ M hM hMJ
  let K := L (some true)
  let K₀ := L (some false)
  let B' := L none
  have hK : K ≤ R := (hL (some true)).1
  have hK₀ : K₀ ≤ R := (hL (some false)).1
  have hB' : B' ≤ R := (hL none).1
  have hKs : K.space = P.space := (hL (some true)).2.1
  have hK₀s : K₀.space = P₀.space := (hL (some false)).2.1
  have hB's : B'.space = frontier J.space := (hL none).2.1.trans hBs
  have hK₀K : K₀ ≤ K := by
    intro s hs
    apply (hL (some true)).2.2 s (hK₀ hs)
    intro v hv
    apply mem_subcomplex_vertices_of_mem_space hK
    · exact R.down_closed (hK₀ hs) (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    · rw [hKs]
      exact hP₀P (hK₀s ▸ K₀.subset_space hs hv)
  have hcross : ∀ s ∈ K₀.faces, ∀ t ∈ B'.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) :=
    fun _ hs _ ht => R.inter_subset_convexHull (hK₀ hs) (hB' ht)
  let Q := K₀.unionOfCompatible B' hcross
  have hQ : Q ≤ R := fun _ hs => hs.elim (fun h => hK₀ h) (fun h => hB' h)
  have hQs : Q.space = P₀.space ∪ frontier J.space := by
    rw [space_unionOfCompatible, hK₀s, hB's]
  refine ⟨R, K, K₀, Q, hR, hRJ, hK, hKs, hK₀K, hK₀s,
    fun s hs => (hL (some false)).2.2 s (hK hs), hQ, hQs, ?_⟩
  intro v hv hv₀ hvQ
  change v ∈ K₀.vertices ∪ B'.vertices at hvQ
  rcases hvQ with hv₀' | hvB
  · exact hv₀ hv₀'
  · apply hv₀
    apply mem_subcomplex_vertices_of_mem_space hK₀ (hK hv)
    rw [hK₀s]
    exact hfront ⟨hKs ▸ K.vertices_subset_space hv,
      hB's ▸ B'.vertices_subset_space hvB⟩

end Geometry.SimplicialComplex
