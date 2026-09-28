import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.RimArcPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointSigns



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem exists_subcomplexes_of_disjoint_closed_cover
    {ι : Type*} [Finite ι] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (S : ι → Set E) (hS : ∀ i, IsClosed (S i))
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hcover : (⋃ i, S i) = K.space) :
    ∃ B : ι → SimplicialComplex ℝ E,
      (∀ i, B i ≤ K) ∧ (∀ i, (B i).space = S i) ∧
      ∀ s, s ∈ K.faces ↔ ∃ i, s ∈ (B i).faces := by
  classical
  have hex (i : ι) : ∃ B : SimplicialComplex ℝ E,
      B ≤ K ∧ B.space = S i := by
    let V := ⋃ j : {j : ι // j ≠ i}, S j.val
    have hV : IsClosed V := isClosed_iUnion_of_finite (fun j ↦ hS j.val)
    have hc : S i ∪ V = K.space := by
      rw [← hcover]
      ext x
      simp only [V, mem_union, mem_iUnion, Subtype.exists]
      constructor
      · rintro (hi | ⟨j, _, hj⟩)
        · exact ⟨i, hi⟩
        · exact ⟨j, hj⟩
      · rintro ⟨j, hj⟩
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hj)
        · exact Or.inr ⟨j, hji, hj⟩
    have hi : S i ∩ V ⊆ K.vertices := by
      rintro x ⟨hx, hxV⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxV
      exact (disjoint_left.mp (hdis j.property.symm) hx hj).elim
    obtain ⟨B, hBK, hBS, _⟩ :=
      exists_subcomplex_of_closed_vertex_partition K hK (S i) V (hS i) hV hc hi
    exact ⟨B, hBK, hBS⟩
  choose B hBK hBS using hex
  refine ⟨B, hBK, hBS, ?_⟩
  intro s
  constructor
  · intro hs
    let : Fintype K.faces := hK.fintype
    have hx : s.centroid ℝ id ∈ K.space :=
      K.convexHull_subset_space hs (Finset.centroid_mem_convexHull _ (K.nonempty_of_mem_faces hs))
    rw [← hcover] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    let : Fintype (B i).faces := (hK.subset (hBK i)).fintype
    exact ⟨i, K.face_mem_subcomplex_of_centroid (B i) (hBK i) hs (hBS i ▸ hi)⟩
  · rintro ⟨i, hi⟩
    exact hBK i hi

end PoincareConjecture.M76.Dehn.Annuli
