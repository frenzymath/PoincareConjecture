import PoincareLib.Topology.Manifold.Surgery.Event.Components.Components
import PoincareLib.Topology.Manifold.Surgery.Event.Region.RegionEquivalences

/-!
# Ambient equivalences from open-submanifold diffeomorphisms

The inherited open carriers give total extensions that are smooth on the
specified regions, with fallback values only outside them. The extensions
retain the original diffeomorphism at every point of their actual domains.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- Reverse the exact two maps of a smooth region equivalence. -/
def reverseRegions {A B : GeneralizedSliceCarrier.{u}}
    {U : Set A.carrier} {V : Set B.carrier}
    (e : SurgeryRegionEquivalence A B U V) : SurgeryRegionEquivalence B A V U where
  map := e.inverse
  inverse := e.map
  map_image := e.inverse_image
  inverse_image := e.map_image
  left_inverse := e.right_inverse
  right_inverse := e.left_inverse
  map_smooth := e.inverse_smooth
  inverse_smooth := e.map_smooth

/-- A diffeomorphism of nonempty open carriers gives an ambient region
equivalence. The source point and its image are only off-region fallback values. -/
noncomputable def openDiffeomorphRegions {A B : GeneralizedSliceCarrier.{u}}
    (U : TopologicalSpace.Opens A.carrier) (V : TopologicalSpace.Opens B.carrier)
    (e : U ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ V) (x : U) :
    SurgeryRegionEquivalence A B U V := by
  let d : SurgeryRegionEquivalence (openCarrier A U) (openCarrier B V) Set.univ Set.univ := {
    map := e
    inverse := e.symm
    map_image := Set.image_univ_of_surjective e.surjective
    inverse_image := Set.image_univ_of_surjective e.symm.surjective
    left_inverse := fun y _ => e.symm_apply_apply y
    right_inverse := fun y _ => e.apply_symm_apply y
    map_smooth := e.contMDiff.contMDiffOn
    inverse_smooth := e.symm.contMDiff.contMDiffOn }
  exact composeRegions (reverseRegions (openRegionEquivalence A U x))
    (composeRegions d (openRegionEquivalence B V (e x)))

/-- On the source region the total map is the literal supplied diffeomorphism. -/
theorem openDiffeomorphRegions_apply {A B : GeneralizedSliceCarrier.{u}}
    (U : TopologicalSpace.Opens A.carrier) (V : TopologicalSpace.Opens B.carrier)
    (e : U ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ V) (x : U) (y : A.carrier) (hy : y ∈ U) :
    (openDiffeomorphRegions U V e x).map y = (e ⟨y, hy⟩).val := by
  change (e ((openRegionEquivalence A U x).inverse y)).val = (e ⟨y, hy⟩).val
  apply congrArg (fun z : U => (e z).val)
  apply Subtype.ext
  exact (openRegionEquivalence A U x).right_inverse hy

/-- The inverse also retains the original diffeomorphism on its exact region. -/
theorem openDiffeomorphRegions_inverse {A B : GeneralizedSliceCarrier.{u}}
    (U : TopologicalSpace.Opens A.carrier) (V : TopologicalSpace.Opens B.carrier)
    (e : U ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ V) (x : U) (y : B.carrier) (hy : y ∈ V) :
    (openDiffeomorphRegions U V e x).inverse y = (e.symm ⟨y, hy⟩).val := by
  change (e.symm ((openRegionEquivalence B V (e x)).inverse y)).val =
    (e.symm ⟨y, hy⟩).val
  apply congrArg (fun z : V => (e.symm z).val)
  apply Subtype.ext
  exact (openRegionEquivalence B V (e x)).right_inverse hy

end PoincareMT.M38
