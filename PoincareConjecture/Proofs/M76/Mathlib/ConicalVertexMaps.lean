import PoincareConjecture.Proofs.M76.Mathlib.ConicalStar
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHomeomorph









set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}



theorem coneAtZero_face_images
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (v : E → F) (hv0 : v 0 = 0)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F)) :
    ∀ s ∈ (K.coneAtZero hlinK hinjK).faces,
      ∃ t ∈ (L.coneAtZero hlinL hinjL).faces, v '' (s : Set E) ⊆ (t : Set F) := by
  intro s hs
  rcases hs.2 with he | hface
  · refine ⟨{0}, zero_mem_coneAtZero_vertices hlinL hinjL, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x = 0 := by
      by_contra hx0
      have hmem := Finset.mem_erase.mpr ⟨hx0, hx⟩
      rw [he] at hmem
      exact Finset.notMem_empty x hmem
    simp [hx0, hv0]
  · obtain ⟨t, ht, hst⟩ := hv _ hface
    refine ⟨insert (0 : F) t, insert_zero_mem_coneAtZero_faces hlinL hinjL ht, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · simp [hx0, hv0]
    · exact Finset.mem_insert_of_mem (hst ⟨x, Finset.mem_erase.mpr ⟨hx0, hx⟩, rfl⟩)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]




theorem exists_cone_homeomorph_of_vertex_maps (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (v : E → F) (w : F → E) (hv0 : v 0 = 0) (hw0 : w 0 = 0)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F))
    (hw : ∀ t ∈ L.faces, ∃ s ∈ K.faces, w '' (t : Set F) ⊆ (s : Set E))
    (hleft : LeftInvOn w v K.vertices) (hright : RightInvOn w v L.vertices) :
    ∃ (f : E → F) (g : F → E)
      (e : (K.coneAtZero hlinK hinjK).space ≃ₜ (L.coneAtZero hlinL hinjL).space),
      (K.coneAtZero hlinK hinjK).AffineOnFaces f ∧
      (L.coneAtZero hlinL hinjL).AffineOnFaces g ∧
      EqOn f v (K.coneAtZero hlinK hinjK).vertices ∧
      EqOn g w (L.coneAtZero hlinL hinjL).vertices ∧
      (∀ x : (K.coneAtZero hlinK hinjK).space, (e x : F) = f x) ∧
      (∀ y : (L.coneAtZero hlinL hinjL).space, (e.symm y : E) = g y) := by
  apply (K.coneAtZero hlinK hinjK).exists_homeomorph_of_vertex_maps
    (L.coneAtZero hlinL hinjL) (finite_coneAtZero_faces hK hlinK hinjK) v w
    (coneAtZero_face_images hlinK hinjK hlinL hinjL v hv0 hv)
    (coneAtZero_face_images hlinL hinjL hlinK hinjK w hw0 hw)
  · intro x hx
    rw [coneAtZero_vertices] at hx
    rcases hx with hx | hx
    · rw [hx, hv0, hw0]
    · exact hleft hx
  · intro y hy
    rw [coneAtZero_vertices] at hy
    rcases hy with hy | hy
    · rw [hy, hw0, hv0]
    · exact hright hy

end Geometry.SimplicialComplex
