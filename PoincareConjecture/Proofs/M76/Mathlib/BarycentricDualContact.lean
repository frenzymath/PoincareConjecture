import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem cofaceCentroid_mem_dualBlock_link
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ⊆ t) (hne : s ≠ t) :
    t.centroid ℝ id ∈ ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  classical
  let N := K.barycentricDualBlock s
  have htN : t.centroid ℝ id ∈ N.vertices := by
    refine ⟨(K.mem_barycentricSubdivision_vertices_iff _).mpr ⟨t, ht, rfl⟩, ?_⟩
    intro x hx
    exact ⟨t, ht, hst, (Finset.mem_singleton.mp hx).symm⟩
  have htstar : {t.centroid ℝ id} ∈ (N.closedStar (s.centroid ℝ id)).faces :=
    (K.barycentricDualBlock_closedStar_faceCentroid hs).symm ▸ htN
  apply (N.link (s.centroid ℝ id)).vertices_subset_space
  refine ⟨htN, ?_, htstar.2⟩
  intro he
  have heq : (⟨s, hs⟩ : K.faces) = ⟨t, ht⟩ :=
    K.faceCentroid_injective (Finset.mem_singleton.mp he)
  exact hne (congrArg Subtype.val heq)

omit [DecidableEq E] [Fintype K.faces] in

theorem dualBlocks_inter_eq_centroid_of_no_common_coface
    [Finite K.faces]
    (L M : SimplicialComplex ℝ E) [Fintype L.faces] [Fintype M.faces]
    (hL : L ≤ K) (hM : M ≤ K) {s : Finset E}
    (hsL : s ∈ L.faces) (hsM : s ∈ M.faces)
    (hcommon : ∀ t ∈ L.faces, t ∈ M.faces → s ⊆ t → t = s) :
    (L.barycentricDualBlock s).space ∩ (M.barycentricDualBlock s).space =
      {s.centroid ℝ id} := by
  classical
  let : Fintype K.faces := Fintype.ofFinite K.faces
  apply Subset.antisymm
  · intro x hx
    obtain ⟨a, haL, haM, hxa⟩ := K.barycentricSubdivision.exists_common_face_of_mem_subcomplexes
      (L.barycentricDualBlock s) (M.barycentricDualBlock s)
      ((K.barycentricDualBlock_mono_of_subcomplex L hL s).trans
        (K.barycentricDualBlock_le s))
      ((K.barycentricDualBlock_mono_of_subcomplex M hM s).trans
        (K.barycentricDualBlock_le s)) hx
    have hverts : (a : Set E) ⊆ {s.centroid ℝ id} := by
      intro y hy
      obtain ⟨t, ht, hst, hty⟩ := haL.2 y hy
      obtain ⟨u, hu, _, huy⟩ := haM.2 y hy
      have he : (⟨t, hL ht⟩ : K.faces) = ⟨u, hM hu⟩ :=
        K.faceCentroid_injective (hty.trans huy.symm)
      have htu : t = u := congrArg Subtype.val he
      have hts : t = s := hcommon t ht (htu.symm ▸ hu) hst
      exact hty.symm.trans (congrArg (fun v : Finset E => v.centroid ℝ id) hts)
    simpa only [convexHull_singleton] using convexHull_mono hverts hxa
  · rintro x rfl
    exact ⟨(L.barycentricDualBlock s).vertices_subset_space
      (L.faceCentroid_mem_barycentricDualBlock_vertices hsL),
      (M.barycentricDualBlock s).vertices_subset_space
        (M.faceCentroid_mem_barycentricDualBlock_vertices hsM)⟩

end Geometry.SimplicialComplex
