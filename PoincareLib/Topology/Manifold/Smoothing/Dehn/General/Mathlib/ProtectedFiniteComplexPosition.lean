import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.FiniteProtectedVertexMotion
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FiniteAffineFacePosition
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ConnectedComplexGraph

/-!
# Actual protected general position for finitely many complexes

The selected vertices are precisely those of the source outside
its full protected subcomplex. All original and target vertices
enter the finite avoidance set. Each actual face pair then has
the literal full-span or disjoint-relative-interior alternative.
See Hudson1969, Lemma4.5, and Dehn029, sections3--4.
-/

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

/-- Construct an arbitrarily small actual ambient motion putting
every unprotected source face in general position with every
face of a finite family of target complexes. The whole protected
carrier and ambient frontier stay fixed. Targets remain their
original geometric carriers. See Dehn029, sections3--4. -/
theorem exists_protected_finite_complex_position
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (J Q K K₀ : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hcv : Convex ℝ J.space) (hQJ : Q ≤ J)
    (hfront : frontier J.space ⊆ Q.space) (hKJ : K ≤ J)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces)
    (hprotected : K₀.space ⊆ Q.space)
    (hfree : ∀ v ∈ K.vertices, v ∉ K₀.vertices → v ∉ Q.vertices)
    (L : ι → SimplicialComplex ℝ E) (hL : ∀ i, (L i).faces.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : PLCarrierMotion J.space Q.space ε,
      J.AffineOnFaces (H.map 1) ∧
      (∀ t x, x ∈ K₀.space → H.map t x = x) ∧
      ∀ i s, s ∈ K.faces → s ∉ K₀.faces → ∀ t, t ∈ (L i).faces →
        affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
            (convexHull ℝ (t : Set E)) := by
  classical
  have hK : K.faces.Finite := hJ.subset hKJ
  let V : Set E := K.vertices \ K₀.vertices
  have hV : V.Finite := (K.finite_vertices_of_finite_faces hK).sdiff
  let l : List E := hV.toFinset.toList
  have hmem (v : E) : v ∈ l ↔ v ∈ V := by
    simp only [l, Finset.mem_toList, hV.mem_toFinset]
  have hvertices (v : E) (hv : v ∈ l) : v ∈ J.vertices :=
    hKJ ((hmem v).mp hv).1
  have hfree' (v : E) (hv : v ∈ l) : v ∉ Q.vertices := by
    have h := (hmem v).mp hv
    exact hfree v h.1 h.2
  let T : Set E := J.vertices ∪ ⋃ i, (L i).vertices
  have hT : T.Finite := (J.finite_vertices_of_finite_faces hJ).union
    (Set.finite_iUnion fun i => (L i).finite_vertices_of_finite_faces (hL i))
  obtain ⟨H, hHaff, hHfixed, hHavoid⟩ :=
    exists_finite_protected_vertex_motion J Q hJ hcv hQJ hfront l
      hV.toFinset.nodup_toList hvertices hfree' T hT hε
  refine ⟨H, hHaff, fun t x hx => H.fixed_protected t x (hprotected hx), ?_⟩
  intro i s hs hs₀ t ht
  have hfaceVertex (w : E) (hw : w ∈ s) : w ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  have hexists : ∃ v ∈ s, v ∉ K₀.vertices := by
    by_contra h
    push Not at h
    exact hs₀ (hfull s hs h)
  have hselected : ∃ v ∈ l, v ∈ s := by
    obtain ⟨v, hv, hv₀⟩ := hexists
    exact ⟨v, (hmem v).mpr ⟨hfaceVertex v hv, hv₀⟩, hv⟩
  apply affine_span_eq_top_or_disjoint_of_ordered_vertex_avoidance l
    (H.map 1) T hHavoid s t hselected
  · intro w hw hwl
    have hwJ : w ∈ J.vertices := hKJ (hfaceVertex w hw)
    rw [hHfixed 1 w hwJ hwl]
    exact Or.inl hwJ
  · intro w hw
    exact Or.inr (mem_iUnion.mpr ⟨i, (L i).down_closed ht
      (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)⟩)

end Geometry.SimplicialComplex
