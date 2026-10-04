import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialEmbeddedAffineImage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineFaceInverse
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedronMaps

/-!
# Polyhedral homeomorphisms to geometric embedding images

The carrier-image homeomorphism takes values in the actual image
complex, and its inverse has affine formulas on the image faces.
See Hudson 1969, pp. 15--17 and M76 derivation 77.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

/-- A finite face-affine embedding identifies the original carrier
with the carrier of its geometric image complex. See Hudson
pp. 15--17 and M76 derivation 77. -/
noncomputable def AffineOnFaces.embeddedHomeomorph (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) :
    K.space ≃ₜ (hf.embeddedImage hinj).space :=
  (hf.homeomorphImage hK hinj).trans (Homeomorph.setCongr (hf.embeddedImage_space hinj).symm)

/-- The embedded carrier homeomorphism evaluates by the given
face-affine map. See Hudson pp. 15--17 and M76 derivation 77. -/
theorem AffineOnFaces.embeddedHomeomorph_apply (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) (x : K.space) :
    (hf.embeddedHomeomorph hinj hK x : F) = f x := rfl

/-- The inverse carrier homeomorphism agrees with the inverse
restricted to the original carrier. See Hudson pp. 15--17 and
M76 derivation 77. -/
theorem AffineOnFaces.embeddedHomeomorph_symm_apply (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) (y : (hf.embeddedImage hinj).space) :
    ((hf.embeddedHomeomorph hinj hK).symm y : E) = Function.invFunOn f K.space (y : F) := by
  let e := hf.embeddedHomeomorph hinj hK
  have he : f (e.symm y) = (y : F) := congrArg Subtype.val (e.apply_symm_apply y)
  have hleft := hinj.leftInvOn_invFunOn (e.symm y).property
  rw [he] at hleft
  exact hleft.symm

/-- Any carrier left inverse is affine on the image faces.
See Hudson pp. 15--17 and M76 derivations 09, 77. -/
theorem AffineOnFaces.inverse_on_embeddedImage [FiniteDimensional ℝ F]
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) {g : F → E}
    (hleft : LeftInvOn g f K.space) : (hf.embeddedImage hinj).AffineOnFaces g := by
  classical
  apply hf.inverse_of_face_images hleft
  intro t ht
  rw [hf.embeddedImage_faces hinj] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨s, hs, Finset.coe_image.symm⟩

/-- The carrier inverse of a face-affine embedding is face-affine
on its actual image complex. See Hudson pp. 15--17 and
M76 derivation 77. -/
theorem AffineOnFaces.invFunOn_embeddedImage [FiniteDimensional ℝ F]
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) :
    (hf.embeddedImage hinj).AffineOnFaces (Function.invFunOn f K.space) :=
  hf.inverse_on_embeddedImage hinj hinj.leftInvOn_invFunOn

end Geometry.SimplicialComplex
