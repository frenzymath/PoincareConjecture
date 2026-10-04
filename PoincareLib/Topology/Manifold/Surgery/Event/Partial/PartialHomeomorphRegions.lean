import PoincareLib.Topology.Manifold.Surgery.Event.Open.OpenRegionEquivalences

/-!
# Region maps from smooth partial homeomorphisms

Both total maps are retained. This allows the M38 event comparison to use
the actual discarded component inside the canonical coordinate domain.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- Smooth partial homeomorphism coordinates give a region equivalence
with precisely their original source, target, and two maps. -/
def partialHomeomorphRegions {A B : GeneralizedSliceCarrier.{u}}
    (e : OpenPartialHomeomorph A.carrier B.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    SurgeryRegionEquivalence A B e.source e.target where
  map := e
  inverse := e.symm
  map_image := e.image_source_eq_target
  inverse_image := e.symm.image_source_eq_target
  left_inverse := fun _ hx => e.left_inv hx
  right_inverse := fun _ hx => e.right_inv hx
  map_smooth := he
  inverse_smooth := hi

end PoincareMT.M38
