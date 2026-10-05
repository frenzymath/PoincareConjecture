import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineOnFaces
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms from finite polyhedron maps

A finite complex has compact carrier. An injective map affine on its faces
therefore identifies that carrier homeomorphically with its image. This is
the topological component of the PL maps in Hamilton 1976, pp. 64, 69, and
Cairns 1940, pp. 797--798. See M76 derivation 08. No claim about an affine
or PL inverse is made here.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The carrier of a finite geometric complex is compact.
See Hamilton p. 69 and M76 derivation 08. -/
theorem isCompact_space_of_finite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space :=
  hK.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ

variable {K : SimplicialComplex ℝ E} {f : E → F}

/-- An injective map affine on the faces of a finite complex is a homeomorphism
onto its image, with the subspace topologies. See M76 derivation 08. -/
noncomputable def AffineOnFaces.homeomorphImage (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) : K.space ≃ₜ f '' K.space := by
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite K hK)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn f K.space hinj)
    ((hf.continuousOn hK).domRestrict.subtype_mk _)

/-- The induced homeomorphism has the original function as its forward map.
See M76 derivation 08. -/
theorem AffineOnFaces.homeomorphImage_apply (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) (x : K.space) :
    (hf.homeomorphImage hK hinj x : F) = f x := rfl

/-- A face-affine bijection from a finite complex to a prescribed subset is
a homeomorphism for the subspace topology. See M76 derivation 08. -/
noncomputable def AffineOnFaces.homeomorphOfBijOn (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) : K.space ≃ₜ S :=
  (hf.homeomorphImage hK hbij.injOn).trans (Homeomorph.setCongr hbij.image_eq)

/-- The homeomorphism onto a prescribed target agrees with the original map.
See M76 derivation 08. -/
theorem AffineOnFaces.homeomorphOfBijOn_apply (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) (x : K.space) :
    (hf.homeomorphOfBijOn hK hbij x : F) = f x := rfl

end Geometry.SimplicialComplex
