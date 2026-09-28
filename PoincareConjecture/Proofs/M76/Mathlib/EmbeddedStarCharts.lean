import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [DecidableEq E] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {f : E → F}

theorem AffineOnFaces.exists_embeddedImage_closedFaceStar_chart
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    {s : Finset E} (hs : s ∈ K.faces) {h : E → G}
    (hh : (K.closedFaceStar s).AffineOnFaces h)
    (hhinj : InjOn h (K.closedFaceStar s).space) :
    ∃ k : F → G,
      ((hf.embeddedImage hinj).closedFaceStar (s.image f)).AffineOnFaces k ∧
      InjOn k ((hf.embeddedImage hinj).closedFaceStar (s.image f)).space ∧
      k '' ((hf.embeddedImage hinj).closedFaceStar (s.image f)).space =
        h '' (K.closedFaceStar s).space := by
  classical
  let g := Function.invFunOn f K.space
  have hleft : LeftInvOn g f K.space := hinj.leftInvOn_invFunOn
  have hsub : (K.closedFaceStar s).space ⊆ K.space :=
    space_subset_of_le (K.closedFaceStar_le s)
  have hg : ((hf.embeddedImage hinj).closedFaceStar (s.image f)).AffineOnFaces g :=
    fun t ht => hf.invFunOn_embeddedImage hinj t ht.1
  have hspace := hf.embeddedImage_closedFaceStar_space hinj hs
  refine ⟨h ∘ g, hg.comp_of_face_images hh ?_, ?_, ?_⟩
  · intro t ht
    rw [hf.embeddedImage_closedFaceStar_faces hinj hs] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨u, hu, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    rw [Finset.coe_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hleft (K.subset_space hu.1 hx)]
    exact hx
  · intro y hy z hz hyz
    rw [hspace] at hy hz
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hz
    have he : h x = h w := by
      simpa only [Function.comp_apply, hleft (hsub hx), hleft (hsub hw)] using hyz
    exact congrArg f (hhinj hx hw he)
  · rw [hspace, image_image]
    apply EqOn.image_eq
    intro x hx
    simp only [Function.comp_apply, hleft (hsub hx)]

end Geometry.SimplicialComplex
