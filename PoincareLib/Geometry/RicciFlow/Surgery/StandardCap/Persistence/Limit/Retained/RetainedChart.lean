import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Charts.SmoothImageInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual smooth chart across a retained surgery interior

The primitive smooth region equivalence sends interiors exactly onto
interiors. Its unchanged maps form a partial diffeomorphism there,
including for the retained and regular-limit identifications of an
actual surgery event. Morgan--Tian, Proposition 16.5, pp. 374-375;
see M44 derivation 47.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}

/-- The image of the source interior under the actual region map
is open, by its smooth within-image inverse. Source: Proposition
16.5's retained transport; M44 derivation 47. -/
theorem regionEquivalence_isOpen_image_interior (e : SurgeryRegionEquivalence A B U V) :
    IsOpen (e.map '' interior U) := by
  have himage : e.map '' interior U ⊆ V := by
    exact (image_mono interior_subset).trans e.map_image.subset
  exact Poincare.isOpen_image_of_smooth_leftInvOn isOpen_interior
    (e.map_smooth.mono interior_subset) (e.inverse_smooth.mono himage)
    (e.left_inverse.mono interior_subset)

/-- The inverse also has an open image of the displayed target
interior. Source: retained transport in Proposition 16.5;
M44 derivation 47. -/
theorem regionEquivalence_isOpen_inverse_image_interior (e : SurgeryRegionEquivalence A B U V) :
    IsOpen (e.inverse '' interior V) := by
  have himage : e.inverse '' interior V ⊆ U := by
    exact (image_mono interior_subset).trans e.inverse_image.subset
  exact Poincare.isOpen_image_of_smooth_leftInvOn isOpen_interior
    (e.inverse_smooth.mono interior_subset) (e.map_smooth.mono himage)
    (e.right_inverse.mono interior_subset)

/-- The actual region maps identify exactly the two interiors;
no openness of the original displayed sets is assumed. Source:
Proposition 16.5, pp. 374-375; M44 derivation 47. -/
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

/-- The supplied retention maps, restricted only to interiors,
form an actual partial diffeomorphism. Source: Proposition 16.5,
pp. 374-375; M44 derivation 47. -/
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

/-- The regular-limit chart has the exact primitive regular domain
and the whole terminal target. Source: Proposition 16.5's retained
transport; M44 derivation 47. -/
theorem limit_identify_chart_domains
    {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (event : SurgeryEventData g0 K P slice metric T) :
    (regionEquivalenceInteriorChart event.limit_identify).source = event.regular_limit ∧
      (regionEquivalenceInteriorChart event.limit_identify).target = univ := by
  exact ⟨event.regular_limit_open.interior_eq, interior_univ⟩

end PoincareMT.M44
