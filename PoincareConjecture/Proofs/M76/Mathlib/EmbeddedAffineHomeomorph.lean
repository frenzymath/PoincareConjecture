import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}




noncomputable def AffineOnFaces.embeddedHomeomorph (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) :
    K.space ≃ₜ (hf.embeddedImage hinj).space :=
  (hf.homeomorphImage hK hinj).trans (Homeomorph.setCongr (hf.embeddedImage_space hinj).symm)



theorem AffineOnFaces.embeddedHomeomorph_apply (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) (x : K.space) :
    (hf.embeddedHomeomorph hinj hK x : F) = f x := rfl




theorem AffineOnFaces.embeddedHomeomorph_symm_apply (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) (y : (hf.embeddedImage hinj).space) :
    ((hf.embeddedHomeomorph hinj hK).symm y : E) = Function.invFunOn f K.space (y : F) := by
  let e := hf.embeddedHomeomorph hinj hK
  have he : f (e.symm y) = (y : F) := congrArg Subtype.val (e.apply_symm_apply y)
  have hleft := hinj.leftInvOn_invFunOn (e.symm y).property
  rw [he] at hleft
  exact hleft.symm



theorem AffineOnFaces.inverse_on_embeddedImage [FiniteDimensional ℝ F]
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) {g : F → E}
    (hleft : LeftInvOn g f K.space) : (hf.embeddedImage hinj).AffineOnFaces g := by
  classical
  apply hf.inverse_of_face_images hleft
  intro t ht
  rw [hf.embeddedImage_faces hinj] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨s, hs, Finset.coe_image.symm⟩




theorem AffineOnFaces.invFunOn_embeddedImage [FiniteDimensional ℝ F]
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) :
    (hf.embeddedImage hinj).AffineOnFaces (Function.invFunOn f K.space) :=
  hf.inverse_on_embeddedImage hinj hinj.leftInvOn_invFunOn

end Geometry.SimplicialComplex
