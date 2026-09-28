import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces
import Mathlib.Topology.Homeomorph.Lemmas











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem isCompact_space_of_finite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space :=
  hK.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ

variable {K : SimplicialComplex ℝ E} {f : E → F}



noncomputable def AffineOnFaces.homeomorphImage (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) : K.space ≃ₜ f '' K.space := by
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite K hK)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn f K.space hinj)
    ((hf.continuousOn hK).domRestrict.subtype_mk _)



theorem AffineOnFaces.homeomorphImage_apply (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) (x : K.space) :
    (hf.homeomorphImage hK hinj x : F) = f x := rfl



noncomputable def AffineOnFaces.homeomorphOfBijOn (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) : K.space ≃ₜ S :=
  (hf.homeomorphImage hK hbij.injOn).trans (Homeomorph.setCongr hbij.image_eq)



theorem AffineOnFaces.homeomorphOfBijOn_apply (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) (x : K.space) :
    (hf.homeomorphOfBijOn hK hbij x : F) = f x := rfl

end Geometry.SimplicialComplex
