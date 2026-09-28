import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetBoundary










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]




theorem barycentricDualBlock_singleton_eq_closedStar
    {p : E} (hp : p ∈ K.vertices) :
    K.barycentricDualBlock {p} = K.barycentricSubdivision.closedStar p := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨a, ha, hchain, hfa⟩ := (K.barycentricSubdivision_faces f).mp hf.1
    apply (K.barycentricSubdivision_closedStar_faces hp f).mpr
    refine ⟨a, ha, hchain, hfa, ?_⟩
    intro t ht
    obtain ⟨u, hu, hpu, hut⟩ := hf.2 _
      (hfa.symm ▸ Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    have he : (⟨u, hu⟩ : K.faces) = t := K.faceCentroid_injective hut
    exact congrArg Subtype.val he ▸ hpu (Finset.mem_singleton_self p)
  · intro hf
    obtain ⟨a, ha, hchain, hfa, hpa⟩ :=
      (K.barycentricSubdivision_closedStar_faces hp f).mp hf
    refine ⟨(K.barycentricSubdivision_faces f).mpr ⟨a, ha, hchain, hfa⟩, ?_⟩
    intro x hx
    obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp (hfa ▸ hx)
    exact ⟨t.val, t.property, Finset.singleton_subset_iff.mpr (hpa t ht), htx⟩

omit [DecidableEq E] in



theorem barycentricDualBlock_space_inter_subcomplex
    (L : SimplicialComplex ℝ E) [Fintype L.faces] (hLK : L ≤ K) (s : Finset E) :
    (K.barycentricDualBlock s).space ∩ L.space =
      (L.barycentricDualBlock s).space := by
  classical
  ext x
  constructor
  · intro hx
    have hxL : x ∈ L.barycentricSubdivision.space :=
      L.barycentricSubdivision_isSubdivision.space_eq.symm.subset hx.2
    obtain ⟨f, hfK, hfL, hxf⟩ :=
      K.barycentricSubdivision.exists_common_face_of_mem_subcomplexes
        (K.barycentricDualBlock s) L.barycentricSubdivision
        (K.barycentricDualBlock_le s) (L.barycentricSubdivision_mono hLK) ⟨hx.1, hxL⟩
    refine (L.barycentricDualBlock s).convexHull_subset_space ⟨hfL, ?_⟩ hxf
    intro v hv
    obtain ⟨u, hu, hsu, huv⟩ := hfK.2 v hv
    obtain ⟨t, ht, htv⟩ := (L.mem_barycentricSubdivision_vertices_iff v).mp
      (L.barycentricSubdivision.face_subset_vertices hfL hv)
    have hut : u = t := by
      have he : (⟨u, hu⟩ : K.faces) = ⟨t, hLK ht⟩ :=
        K.faceCentroid_injective (huv.trans htv.symm)
      exact congrArg Subtype.val he
    exact ⟨t, ht, hut ▸ hsu, htv⟩
  · intro hx
    exact ⟨space_subset_of_le (K.barycentricDualBlock_mono_of_subcomplex L hLK s) hx,
      L.barycentricSubdivision_isSubdivision.space_eq.subset
        (space_subset_of_le (L.barycentricDualBlock_le s) hx)⟩

end Geometry.SimplicialComplex
