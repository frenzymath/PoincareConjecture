import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {f : E → F} {g : E → G} {u : F → E}

theorem AffineOnFaces.comp_inverse_on_embeddedImage
    (hf : K.AffineOnFaces f) (hg : K.AffineOnFaces g)
    (hinj : InjOn f K.space) (hleft : LeftInvOn u f K.space) :
    (hf.embeddedImage hinj).AffineOnFaces (g ∘ u) := by
  classical
  apply (hf.inverse_on_embeddedImage hinj hleft).comp_of_face_images hg
  intro t ht
  rw [hf.embeddedImage_faces hinj] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨s, hs, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  rw [hleft (K.subset_space hs hx)]
  exact hx

omit [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in

theorem AffineOnFaces.injOn_comp_inverse_on_embeddedImage
    (hf : K.AffineOnFaces f) (hinjf : InjOn f K.space)
    (hinjg : InjOn g K.space) (hleft : LeftInvOn u f K.space) :
    InjOn (g ∘ u) (hf.embeddedImage hinjf).space := by
  rw [hf.embeddedImage_space hinjf]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  change g (u (f x)) = g (u (f y)) at hxy
  rw [hleft hx, hleft hy] at hxy
  exact congrArg f (hinjg hx hy hxy)

theorem AffineOnFaces.embeddedImage_comp_inverse
    (hf : K.AffineOnFaces f) (hg : K.AffineOnFaces g)
    (hinjf : InjOn f K.space) (hinjg : InjOn g K.space)
    (hleft : LeftInvOn u f K.space)
    (hcomp : (hf.embeddedImage hinjf).AffineOnFaces (g ∘ u))
    (hinjcomp : InjOn (g ∘ u) (hf.embeddedImage hinjf).space) :
    hcomp.embeddedImage hinjcomp = hg.embeddedImage hinjg := by
  classical
  have hfaces (s : Finset E) (hs : s ∈ K.faces) :
      (s.image f).image (g ∘ u) = s.image g := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    change g (u (f x)) = g x
    rw [hleft (K.subset_space hs hx)]
  ext t
  rw [hcomp.embeddedImage_faces hinjcomp, hf.embeddedImage_faces hinjf,
    hg.embeddedImage_faces hinjg]
  constructor
  · rintro ⟨s, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (hfaces r hr).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.image f, ⟨s, hs, rfl⟩, hfaces s hs⟩

end Geometry.SimplicialComplex
