import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {f : E → F}

noncomputable def AffineOnFaces.faceLinkHomeomorphEmbeddedImage
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    (hK : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces) :
    (K.faceLink s).space ≃ₜ ((hf.embeddedImage hinj).faceLink (s.image f)).space := by
  let hfL : (K.faceLink s).AffineOnFaces f := fun t ht => hf t ht.1
  have hle : K.faceLink s ≤ K := fun _ ht => ht.1
  let hinjL : InjOn f (K.faceLink s).space := hinj.mono (space_subset_of_le hle)
  exact (hfL.homeomorphImage (finite_faceLink_faces hK s) hinjL).trans
    (Homeomorph.setCongr (hf.embeddedImage_faceLink_carrier_vertices hinj hs).1.symm)

theorem AffineOnFaces.faceLinkHomeomorphEmbeddedImage_apply
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    (hK : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces)
    (x : (K.faceLink s).space) :
    (hf.faceLinkHomeomorphEmbeddedImage hinj hK hs x : F) = f x := rfl

end Geometry.SimplicialComplex
