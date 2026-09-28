import PoincareConjecture.Proofs.M76.Mathlib.BarycentricStarFaces
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem barycentric_closedStar_face_containment
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {p : E} (hp : p ∈ K.vertices) :
    ∀ s ∈ (K.barycentricSubdivision.closedStar p).faces,
      ∃ t ∈ (K.closedStar p).faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  intro s hs
  obtain ⟨a, ha, hchain, rfl, hpa⟩ :=
    (K.barycentricSubdivision_closedStar_faces hp s).mp hs
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  refine ⟨m.val, ⟨m.property, ?_⟩, convexHull_min ?_ (convex_convexHull ℝ _)⟩
  · simpa only [Finset.insert_eq_of_mem (hpa m hm)] using m.property
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have him : i.val ⊆ m.val := by
      rcases hchain i hi m hm with h | h
      · exact h
      · exact hmax hi h
    exact convexHull_mono him
      (i.val.centroid_mem_convexHull (K.nonempty_of_mem_faces i.property))

theorem barycentric_closedStar_space_subset
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {p : E} (hp : p ∈ K.vertices) :
    (K.barycentricSubdivision.closedStar p).space ⊆ (K.closedStar p).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := K.barycentric_closedStar_face_containment hp s hs
  exact (K.closedStar p).convexHull_subset_space ht (hst hxs)

theorem mem_interior_image_barycentric_closedStar [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {p : E} (hp : p ∈ K.vertices) {f : E → F}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    f p ∈ interior (f '' (K.barycentricSubdivision.closedStar p).space) := by
  have hK : K.faces.Finite := Set.toFinite _
  have hpbar := K.vertices_subset_barycentricSubdivision_vertices hp
  obtain ⟨ε, hε, hnear⟩ := K.barycentricSubdivision.exists_ball_inter_space_subset_closedStar
    K.barycentricSubdivision_finite hpbar
  let D := (K.closedStar p).space ∩ (ball p ε)ᶜ
  have hD : IsCompact D :=
    ((K.closedStar p).isCompact_space_of_finite (finite_closedStar_faces hK p)).inter_right
      isOpen_ball.isClosed_compl
  have hfD : IsClosed (f '' D) :=
    (hD.image_of_continuousOn ((hf.continuousOn (finite_closedStar_faces hK p)).mono
      inter_subset_left)).isClosed
  have hpstar : p ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    exact ⟨hp, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      using (show {p} ∈ K.faces from hp)⟩
  have hfpD : f p ∉ f '' D := by
    rintro ⟨x, hx, hxp⟩
    have he := hinj hx.1 hpstar hxp
    exact hx.2 (he ▸ mem_ball_self hε)
  apply interior_maximal (t := interior (f '' (K.closedStar p).space) \ f '' D)
    ?_ (isOpen_interior.inter hfD.isOpen_compl) ⟨hint, hfpD⟩
  rintro y ⟨hy, hyD⟩
  obtain ⟨x, hx, rfl⟩ := interior_subset hy
  refine ⟨x, hnear ⟨?_, ?_⟩, rfl⟩
  · rw [K.barycentricSubdivision_isSubdivision.space_eq]
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact K.convexHull_subset_space hs.1 hxs
  · by_contra h
    exact hyD ⟨x, ⟨hx, h⟩, rfl⟩

end Geometry.SimplicialComplex
