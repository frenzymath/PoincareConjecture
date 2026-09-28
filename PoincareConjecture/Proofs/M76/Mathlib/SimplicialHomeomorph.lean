import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

private theorem mapsTo_vertices_of_face_images {f : E → F}
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo f K.vertices L.vertices := by
  intro x hx
  obtain ⟨t, ht, hst⟩ := hfaces {x} hx
  exact L.down_closed ht
    (Finset.singleton_subset_iff.mpr (hst ⟨x, by simp, rfl⟩)) (Finset.singleton_nonempty _)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]





theorem exists_homeomorph_of_vertex_maps (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite) (v : E → F) (w : F → E)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F))
    (hw : ∀ t ∈ L.faces, ∃ s ∈ K.faces, w '' (t : Set F) ⊆ (s : Set E))
    (hleft : LeftInvOn w v K.vertices) (hright : RightInvOn w v L.vertices) :
    ∃ (f : E → F) (g : F → E) (e : K.space ≃ₜ L.space),
      K.AffineOnFaces f ∧ L.AffineOnFaces g ∧
      EqOn f v K.vertices ∧ EqOn g w L.vertices ∧
      (∀ x : K.space, (e x : F) = f x) ∧
      (∀ y : L.space, (e.symm y : E) = g y) := by
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices v
  obtain ⟨g, hg, hgw⟩ := L.exists_affineOnFaces_eqOn_vertices w
  have hfacesF : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hv s hs
    have hvS : (s : Set E) ⊆ K.vertices := by
      rw [vertices_eq]
      exact subset_biUnion_of_mem hs
    exact ⟨t, ht, ((hfv.mono hvS).image_eq).subset.trans hst⟩
  have hfacesG : ∀ t ∈ L.faces, ∃ s ∈ K.faces, g '' (t : Set F) ⊆ (s : Set E) := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := hw t ht
    have hwT : (t : Set F) ⊆ L.vertices := by
      rw [vertices_eq]
      exact subset_biUnion_of_mem ht
    exact ⟨s, hs, ((hgw.mono hwT).image_eq).subset.trans hts⟩
  have hfv_map := mapsTo_vertices_of_face_images hfacesF
  have hgw_map := mapsTo_vertices_of_face_images hfacesG
  have hgf : LeftInvOn g f K.space :=
    (hf.comp_of_face_images hg hfacesF).eqOn_of_eqOn_vertices
      (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)) fun x hx => by
        change g (f x) = x
        rw [hgw (hfv_map hx), hfv hx]
        exact hleft hx
  have hfg : RightInvOn g f L.space :=
    (hg.comp_of_face_images hf hfacesG).eqOn_of_eqOn_vertices
      (L.affineOnFaces_affine (ContinuousAffineMap.id ℝ F)) fun y hy => by
        change f (g y) = y
        rw [hfv (hgw_map hy), hgw hy]
        exact hright hy
  have hbij : BijOn f K.space L.space :=
    ⟨hf.mapsTo_space hfacesF, hgf.injOn,
      fun y hy => ⟨g y, hg.mapsTo_space hfacesG hy, hfg hy⟩⟩
  let e := hf.homeomorphOfBijOn hK hbij
  refine ⟨f, g, e, hf, hg, hfv, hgw, fun _ => rfl, ?_⟩
  intro y
  have hval : f (e.symm y) = (y : F) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  exact (hgf (e.symm y).property).symm.trans (congrArg g hval)

end Geometry.SimplicialComplex
