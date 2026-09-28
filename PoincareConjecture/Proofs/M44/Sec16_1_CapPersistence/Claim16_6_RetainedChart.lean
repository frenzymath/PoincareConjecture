import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M44.Mathlib.SmoothImageInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}




theorem regionEquivalence_isOpen_image_interior (e : SurgeryRegionEquivalence A B U V) :
    IsOpen (e.map '' interior U) := by
  have himage : e.map '' interior U ⊆ V := by
    exact (image_mono interior_subset).trans e.map_image.subset
  exact Poincare.isOpen_image_of_smooth_leftInvOn isOpen_interior
    (e.map_smooth.mono interior_subset) (e.inverse_smooth.mono himage)
    (e.left_inverse.mono interior_subset)




theorem regionEquivalence_isOpen_inverse_image_interior (e : SurgeryRegionEquivalence A B U V) :
    IsOpen (e.inverse '' interior V) := by
  have himage : e.inverse '' interior V ⊆ U := by
    exact (image_mono interior_subset).trans e.inverse_image.subset
  exact Poincare.isOpen_image_of_smooth_leftInvOn isOpen_interior
    (e.inverse_smooth.mono interior_subset) (e.map_smooth.mono himage)
    (e.right_inverse.mono interior_subset)




theorem regionEquivalence_image_interior (e : SurgeryRegionEquivalence A B U V) :
    e.map '' interior U = interior V := by
  have hmap : e.map '' interior U ⊆ V := by
    exact (image_mono interior_subset).trans e.map_image.subset
  have hinv : e.inverse '' interior V ⊆ U := by
    exact (image_mono interior_subset).trans e.inverse_image.subset
  have hmapInt := interior_maximal hmap (regionEquivalence_isOpen_image_interior e)
  have hinvInt := interior_maximal hinv (regionEquivalence_isOpen_inverse_image_interior e)
  refine subset_antisymm hmapInt ?_
  intro y hy
  exact ⟨e.inverse y, hinvInt (mem_image_of_mem _ hy), e.right_inverse (interior_subset hy)⟩




noncomputable def regionEquivalenceInteriorChart (e : SurgeryRegionEquivalence A B U V) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞ where
  toFun := e.map
  invFun := e.inverse
  source := interior U
  target := interior V
  map_source' _ hx := regionEquivalence_image_interior e ▸ mem_image_of_mem e.map hx
  map_target' y hy := by
    have hsub : e.inverse '' interior V ⊆ U := by
      exact (image_mono interior_subset).trans e.inverse_image.subset
    exact interior_maximal hsub (regionEquivalence_isOpen_inverse_image_interior e)
      (mem_image_of_mem _ hy)
  left_inv' _ hx := e.left_inverse (interior_subset hx)
  right_inv' _ hy := e.right_inverse (interior_subset hy)
  open_source := isOpen_interior
  open_target := isOpen_interior
  contMDiffOn_toFun := e.map_smooth.mono interior_subset
  contMDiffOn_invFun := e.inverse_smooth.mono interior_subset




theorem limit_identify_chart_domains
    {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (event : SurgeryEventData g0 K P slice metric T) :
    (regionEquivalenceInteriorChart event.limit_identify).source = event.regular_limit ∧
      (regionEquivalenceInteriorChart event.limit_identify).target = univ := by
  exact ⟨event.regular_limit_open.interior_eq, interior_univ⟩

end PoincareConjecture.M44
