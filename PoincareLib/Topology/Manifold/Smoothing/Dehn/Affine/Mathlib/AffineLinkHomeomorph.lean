import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedronMaps

/-!
# The actual homeomorphism on an entire embedded face link

The exact image-face correspondence and compact carrier map give the
homeomorphism with its original pointwise values. See Cairns
pp. 799--800 and Dehn derivation 015.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {f : E → F}

/-- The actual finite face-affine embedding identifies the whole
source face link with the whole image face link. See derivation 015. -/
noncomputable def AffineOnFaces.faceLinkHomeomorphEmbeddedImage
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    (hK : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces) :
    (K.faceLink s).space ≃ₜ ((hf.embeddedImage hinj).faceLink (s.image f)).space := by
  let hfL : (K.faceLink s).AffineOnFaces f := fun t ht => hf t ht.1
  have hle : K.faceLink s ≤ K := fun _ ht => ht.1
  let hinjL : InjOn f (K.faceLink s).space := hinj.mono (space_subset_of_le hle)
  exact (hfL.homeomorphImage (finite_faceLink_faces hK s) hinjL).trans
    (Homeomorph.setCongr (hf.embeddedImage_faceLink_carrier_vertices hinj hs).1.symm)

/-- Every forward value is the original map, on the complete link.
See Dehn derivation 015. -/
theorem AffineOnFaces.faceLinkHomeomorphEmbeddedImage_apply
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    (hK : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces)
    (x : (K.faceLink s).space) :
    (hf.faceLinkHomeomorphEmbeddedImage hinj hK hs x : F) = f x := rfl

end Geometry.SimplicialComplex
