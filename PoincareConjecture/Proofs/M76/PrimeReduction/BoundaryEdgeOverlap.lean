import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeFamily










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype L.faces]
  {T : BoundaryTriangleFibers K L}

local notation "I" => Icc (0 : ℝ) 1

omit [Fintype K.faces] [Fintype L.faces] in


theorem boundary_edge_union_triangle [DecidableEq E]
    (hLcard : ∀ u ∈ L.faces, u.card ≤ 3)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    {s t : Finset E} (hs : s ∈ L.faces) (ht : t ∈ L.faces)
    (hsc : s.card = 2) (htc : t.card = 2) (hne : s ≠ t)
    (hu : s ∪ t ∈ K.faces) : s ∪ t ∈ L.faces ∧ (s ∪ t).card = 3 := by
  have huL := hfull _ hu (fun p hp => (Finset.mem_union.mp hp).elim
    (fun hp => L.face_subset_vertices hs hp) (fun hp => L.face_subset_vertices ht hp))
  have hlo : 2 < (s ∪ t).card := by
    by_contra hn
    have hueq : s ∪ t = s := (Finset.eq_of_subset_of_card_le
      Finset.subset_union_left (by omega)).symm
    have hts : t ⊆ s := hueq ▸ Finset.subset_union_right
    exact hne (Finset.eq_of_subset_of_card_le hts (by omega)).symm
  exact ⟨huL, by have := hLcard _ huL; omega⟩



theorem boundary_triangle_base_singleton
    (hLcard : ∀ u ∈ L.faces, u.card ≤ 3) {u : Finset E}
    (hu : u ∈ L.faces) (huc : u.card = 3) :
    (L.barycentricDualBlock u).space = {u.centroid ℝ id} := by
  apply L.barycentricDualBlock_space_eq_singleton_of_maximal hu
  intro v hv huv
  exact (Finset.eq_of_subset_of_card_le huv (by rw [huc]; exact hLcard v hv)).symm



theorem BoundaryEdgeFamily.agrees (P : BoundaryEdgeFamily T)
    (hLK : L ≤ K) (hLcard : ∀ u ∈ L.faces, u.card ≤ 3)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    {s t : Finset E} (hs : s ∈ L.faces) (ht : t ∈ L.faces)
    (hsc : s.card = 2) (htc : t.card = 2)
    (x : E × ℝ) (hx : x ∈
      ((L.barycentricDualBlock s).space ∩ (L.barycentricDualBlock t).space) ×ˢ I) :
    P.map s x = P.map t x := by
  classical
  by_cases hst : s = t
  · rw [hst]
  have hxU : x.1 ∈ (L.barycentricDualBlock (s ∪ t)).space :=
    (L.barycentricDualBlock_space_inter s t).subset hx.1
  have huL : s ∪ t ∈ L.faces := by
    by_contra hn
    rw [L.barycentricDualBlock_space_eq_empty_of_not_face
      ((L.nonempty_of_mem_faces hs).mono Finset.subset_union_left) hn] at hxU
    exact hxU
  obtain ⟨_, huc⟩ := boundary_edge_union_triangle hLcard hfull hs ht hsc htc hst (hLK huL)
  have hxc : x.1 = (s ∪ t).centroid ℝ id :=
    (boundary_triangle_base_singleton hLcard huL huc).subset hxU
  have heq : x = ((s ∪ t).centroid ℝ id, x.2) := Prod.ext hxc rfl
  rw [heq, P.keep_triangle s hs hsc _ huL Finset.subset_union_left huc _ hx.2,
    P.keep_triangle t ht htc _ huL Finset.subset_union_right huc _ hx.2]



theorem BoundaryEdgeFamily.overlap_image (P : BoundaryEdgeFamily T)
    (hLK : L ≤ K) (hLcard : ∀ u ∈ L.faces, u.card ≤ 3)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    {s t : Finset E} (hs : s ∈ L.faces) (ht : t ∈ L.faces)
    (hsc : s.card = 2) (htc : t.card = 2) :
    P.map s '' (((L.barycentricDualBlock s).space ∩
      (L.barycentricDualBlock t).space) ×ˢ I) =
        (K.barycentricDualBlock s).space ∩ (K.barycentricDualBlock t).space := by
  classical
  by_cases hst : s = t
  · subst t
    simpa only [inter_self] using P.image_eq s hs hsc
  rw [L.barycentricDualBlock_space_inter, K.barycentricDualBlock_space_inter]
  by_cases hu : s ∪ t ∈ K.faces
  · obtain ⟨huL, huc⟩ := boundary_edge_union_triangle hLcard hfull hs ht hsc htc hst hu
    rw [boundary_triangle_base_singleton hLcard huL huc, ← T.image_eq _ huL huc]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxc : x.1 = (s ∪ t).centroid ℝ id := hx.1
      refine ⟨x.2, hx.2, ?_⟩
      have heq : x = ((s ∪ t).centroid ℝ id, x.2) := Prod.ext hxc rfl
      rw [heq]
      exact (P.keep_triangle s hs hsc _ huL Finset.subset_union_left huc _ hx.2).symm
    · rintro _ ⟨r, hr, rfl⟩
      exact ⟨((s ∪ t).centroid ℝ id, r), ⟨rfl, hr⟩,
        P.keep_triangle s hs hsc _ huL Finset.subset_union_left huc r hr⟩
  · have hne : (s ∪ t).Nonempty :=
      (L.nonempty_of_mem_faces hs).mono Finset.subset_union_left
    have huL : s ∪ t ∉ L.faces := fun h => hu (hLK h)
    rw [L.barycentricDualBlock_space_eq_empty_of_not_face hne huL,
      K.barycentricDualBlock_space_eq_empty_of_not_face hne hu]
    simp only [empty_prod, image_empty]

end Geometry.SimplicialComplex
