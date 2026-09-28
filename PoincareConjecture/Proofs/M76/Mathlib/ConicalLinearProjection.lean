import PoincareConjecture.Proofs.M76.Mathlib.ConicalVertexMaps










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

omit [DecidableEq E] in


theorem vertices_image_of_faces {v : E → F}
    (hfaces : L.faces = (fun s : Finset E => s.image v) '' K.faces) :
    L.vertices = v '' K.vertices := by
  ext y
  constructor
  · intro hy
    change {y} ∈ L.faces at hy
    rw [hfaces] at hy
    obtain ⟨s, hs, he⟩ := hy
    dsimp only at he
    have hmem : y ∈ s.image v := by rw [he]; simp
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
    exact ⟨x, K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _), hxy⟩
  · rintro ⟨x, hx, rfl⟩
    change {v x} ∈ L.faces
    rw [hfaces]
    exact ⟨{x}, hx, by simp⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]




theorem exists_cone_homeomorph_of_linear_map (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (Q : E →L[ℝ] F) (hQ : InjOn Q K.vertices)
    (hfaces : L.faces = (fun s : Finset E => s.image Q) '' K.faces) :
    ∃ (g : F → E)
      (e : (K.coneAtZero hlinK hinjK).space ≃ₜ (L.coneAtZero hlinL hinjL).space),
      (L.coneAtZero hlinL hinjL).AffineOnFaces g ∧
      (∀ x : (K.coneAtZero hlinK hinjK).space, (e x : F) = Q x) ∧
      (∀ y : (L.coneAtZero hlinL hinjL).space, (e.symm y : E) = g y) := by
  let w : F → E := fun y => if y = 0 then 0 else Function.invFunOn Q K.vertices y
  have hvertices := vertices_image_of_faces hfaces
  have hleft : LeftInvOn w Q K.vertices := by
    intro x hx
    have hvx : Q x ∈ L.vertices := hvertices ▸ mem_image_of_mem Q hx
    have hne : Q x ≠ 0 := by
      intro he
      apply (hlinL {Q x} hvx).zero_notMem_convexHull
      simp [he]
    dsimp only [w]
    rw [if_neg hne]
    exact hQ.leftInvOn_invFunOn hx
  have hvfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces,
      Q '' (s : Set E) ⊆ (t : Set F) := by
    intro s hs
    exact ⟨s.image Q, hfaces ▸ mem_image_of_mem _ hs, by simp⟩
  have hwfaces : ∀ t ∈ L.faces, ∃ s ∈ K.faces,
      w '' (t : Set F) ⊆ (s : Set E) := by
    intro t ht
    rw [hfaces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s, hs, ?_⟩
    rw [Finset.coe_image]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [hleft (K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _))]
    exact hx
  have hright : RightInvOn w Q L.vertices := by
    intro y hy
    rw [hvertices] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hleft hx]
  obtain ⟨f, g, e, hf, hg, hfv, _, hef, heg⟩ :=
    K.exists_cone_homeomorph_of_vertex_maps L hK hlinK hinjK hlinL hinjL
      Q w (map_zero Q) (by simp [w]) hvfaces hwfaces hleft hright
  have hfQ : EqOn f Q (K.coneAtZero hlinK hinjK).space :=
    hf.eqOn_of_eqOn_vertices
      ((K.coneAtZero hlinK hinjK).affineOnFaces_affine Q.toContinuousAffineMap) hfv
  exact ⟨g, e, hg, fun x => (hef x).trans (hfQ x.property), heg⟩



theorem linear_injOn_cone_of_face_images (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (Q : E →L[ℝ] F) (hQ : InjOn Q K.vertices)
    (hfaces : L.faces = (fun s : Finset E => s.image Q) '' K.faces) :
    InjOn Q (K.coneAtZero hlinK hinjK).space := by
  obtain ⟨_, e, _, he, _⟩ := K.exists_cone_homeomorph_of_linear_map L hK
    hlinK hinjK hlinL hinjL Q hQ hfaces
  intro x hx y hy hxy
  have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
    Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm))
  exact congrArg Subtype.val (e.injective hexy)

end Geometry.SimplicialComplex
