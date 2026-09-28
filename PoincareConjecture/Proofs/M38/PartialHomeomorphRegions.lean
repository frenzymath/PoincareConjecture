import PoincareConjecture.Proofs.M38.OpenRegionEquivalences

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

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

end PoincareConjecture.M38
