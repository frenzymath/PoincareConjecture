import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineLevelVertexMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLevelFacePosition
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

theorem exists_protected_affine_level_complex_position
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (J Q K K₀ : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hcv : Convex ℝ J.space) (hQJ : Q ≤ J)
    (hfront : frontier J.space ⊆ Q.space) (hKJ : K ≤ J)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces)
    (hprotected : K₀.space ⊆ Q.space)
    (hfree : ∀ v ∈ K.vertices, v ∉ K₀.vertices → v ∉ Q.vertices)
    (A : AffineSubspace ℝ E) (hKA : K.space ⊆ A)
    (L : ι → SimplicialComplex ℝ E) (hL : ∀ i, (L i).faces.Finite)
    (hLA : ∀ i, (L i).space ⊆ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : PLCarrierMotion J.space Q.space ε,
      J.AffineOnFaces (H.map 1) ∧
      (∀ t x, x ∈ K₀.space → H.map t x = x) ∧
      (∀ t x, H.map t x - x ∈ A.direction) ∧
      ∀ i s, s ∈ K.faces → s ∉ K₀.faces → ∀ t, t ∈ (L i).faces →
        affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = A ∨
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
  have hverticesA (v : E) (hv : v ∈ l) : v ∈ A :=
    hKA (K.vertices_subset_space ((hmem v).mp hv).1)
  have hfree' (v : E) (hv : v ∈ l) : v ∉ Q.vertices := by
    have h := (hmem v).mp hv
    exact hfree v h.1 h.2
  let T : Set E := K.vertices ∪ ⋃ i, (L i).vertices
  have hT : T.Finite := (K.finite_vertices_of_finite_faces hK).union
    (Set.finite_iUnion fun i => (L i).finite_vertices_of_finite_faces (hL i))
  have hTA : T ⊆ A := by
    intro x hx
    rcases hx with hx | hx
    · exact hKA (K.vertices_subset_space hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hLA i ((L i).vertices_subset_space hi)
  obtain ⟨H, hHaff, hHfixed, hHdir, hHavoid⟩ :=
    exists_finite_affine_level_vertex_motion J Q hJ hcv hQJ hfront A l
      hV.toFinset.nodup_toList hvertices hverticesA hfree' T hT hTA hε
  have hHlevel (x : E) (hx : x ∈ A) : H.map 1 x ∈ A := by
    simpa only [vadd_eq_add, sub_add_cancel] using
      A.vadd_mem_of_mem_direction (hHdir 1 x) hx
  refine ⟨H, hHaff, fun t x hx => H.fixed_protected t x (hprotected hx), hHdir, ?_⟩
  intro i s hs hs₀ t ht
  have hfaceVertex (w : E) (hw : w ∈ s) : w ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  have htargetVertex (w : E) (hw : w ∈ t) : w ∈ (L i).vertices :=
    (L i).down_closed ht (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  have hexists : ∃ v ∈ s, v ∉ K₀.vertices := by
    by_contra h
    push Not at h
    exact hs₀ (hfull s hs h)
  have hselected : ∃ v ∈ l, v ∈ s := by
    obtain ⟨v, hv, hv₀⟩ := hexists
    exact ⟨v, (hmem v).mpr ⟨hfaceVertex v hv, hv₀⟩, hv⟩
  apply affine_level_span_eq_or_disjoint A l (H.map 1) T hHavoid s t hselected
  · intro w hw hwl
    rw [hHfixed 1 w (hKJ (hfaceVertex w hw)) hwl]
    exact Or.inl (hfaceVertex w hw)
  · intro w hw
    exact Or.inr (mem_iUnion.mpr ⟨i, htargetVertex w hw⟩)
  · intro w hw
    exact hHlevel w (hKA (K.vertices_subset_space (hfaceVertex w hw)))
  · intro w hw
    exact hLA i ((L i).vertices_subset_space (htargetVertex w hw))

end Geometry.SimplicialComplex
