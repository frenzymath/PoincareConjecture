import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import PoincareConjecture.Proofs.M76.Mathlib.LocallyFinitePolyhedralPatches











set_option autoImplicit false

open Set Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem vertex_mapsTo_of_faces {K : SimplicialComplex ℝ E}
    {L : SimplicialComplex ℝ F} {v : E → F}
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo v K.vertices L.vertices := by
  intro x hx
  obtain ⟨t, ht, hst⟩ := hv {x} hx
  exact L.down_closed ht
    (Finset.singleton_subset_iff.mpr (hst ⟨x, by simp, rfl⟩)) (Finset.singleton_nonempty _)




theorem exists_inverse_affineOnFaces_of_vertex_maps (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (v : E → F) (w : F → E)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F))
    (hw : ∀ t ∈ L.faces, ∃ s ∈ K.faces, w '' (t : Set F) ⊆ (s : Set E))
    (hleft : LeftInvOn w v K.vertices) (hright : RightInvOn w v L.vertices) :
    ∃ (f : E → F) (g : F → E), K.AffineOnFaces f ∧ L.AffineOnFaces g ∧
      EqOn f v K.vertices ∧ EqOn g w L.vertices ∧
      MapsTo f K.space L.space ∧ MapsTo g L.space K.space ∧
      LeftInvOn g f K.space ∧ RightInvOn g f L.space := by
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
  refine ⟨f, g, hf, hg, hfv, hgw, hf.mapsTo_space hfacesF, hg.mapsTo_space hfacesG,
    ?_, ?_⟩
  · apply (hf.comp_of_face_images hg hfacesF).eqOn_of_eqOn_vertices
      (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E))
    intro x hx
    change g (f x) = x
    rw [hgw (vertex_mapsTo_of_faces hfacesF hx), hfv hx]
    exact hleft hx
  · apply (hg.comp_of_face_images hf hfacesG).eqOn_of_eqOn_vertices
      (L.affineOnFaces_affine (ContinuousAffineMap.id ℝ F))
    intro y hy
    change f (g y) = y
    rw [hfv (vertex_mapsTo_of_faces hfacesG hy), hgw hy]
    exact hright hy





theorem exists_homeomorph_of_local_vertex_maps (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hKopen : IsOpen K.space) (hLopen : IsOpen L.space)
    (hK : ∀ x ∈ K.space, ∃ U ∈ 𝓝 x,
      {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}.Finite)
    (hL : ∀ y ∈ L.space, ∃ V ∈ 𝓝 y,
      {t : L.faces | (convexHull ℝ (t.val : Set F) ∩ V).Nonempty}.Finite)
    (v : E → F) (w : F → E)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F))
    (hw : ∀ t ∈ L.faces, ∃ s ∈ K.faces, w '' (t : Set F) ⊆ (s : Set E))
    (hleft : LeftInvOn w v K.vertices) (hright : RightInvOn w v L.vertices) :
    ∃ (f : E → F) (g : F → E) (e : K.space ≃ₜ L.space),
      K.AffineOnFaces f ∧ L.AffineOnFaces g ∧
      EqOn f v K.vertices ∧ EqOn g w L.vertices ∧
      LocallyPiecewiseAffineOn f K.space ∧ LocallyPiecewiseAffineOn g L.space ∧
      (∀ x : K.space, (e x : F) = f x) ∧
      (∀ y : L.space, (e.symm y : E) = g y) := by
  obtain ⟨f, g, hf, hg, hfv, hgw, hfmap, hgmap, hgf, hfg⟩ :=
    K.exists_inverse_affineOnFaces_of_vertex_maps L v w hv hw hleft hright
  have hfPL : LocallyPiecewiseAffineOn f K.space := by
    rw [← hKopen.interior_eq]
    exact hf.locallyPiecewiseAffineOn_of_local_faces fun x hx => hK x (interior_subset hx)
  have hgPL : LocallyPiecewiseAffineOn g L.space := by
    rw [← hLopen.interior_eq]
    exact hg.locallyPiecewiseAffineOn_of_local_faces fun y hy => hL y (interior_subset hy)
  let e : K.space ≃ₜ L.space :=
    { toEquiv :=
        { toFun := fun x => ⟨f x, hfmap x.property⟩
          invFun := fun y => ⟨g y, hgmap y.property⟩
          left_inv := fun x => Subtype.ext (hgf x.property)
          right_inv := fun y => Subtype.ext (hfg y.property) }
      continuous_toFun := hfPL.continuousOn.domRestrict.subtype_mk _
      continuous_invFun := hgPL.continuousOn.domRestrict.subtype_mk _ }
  exact ⟨f, g, e, hf, hg, hfv, hgw, hfPL, hgPL, fun _ => rfl, fun _ => rfl⟩

end Geometry.SimplicialComplex
