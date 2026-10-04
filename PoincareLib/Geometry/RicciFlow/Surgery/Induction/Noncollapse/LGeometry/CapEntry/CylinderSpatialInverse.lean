import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderSpatial
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.SliceMap

/-!
# Smooth spatial inverses of the actual cap cylinder

Proposition 16.13, pp. 377-378. The raw cylinder has a smooth inverse
within its image. Its actual injective spatial differential has full
rank, so that image is open and the supplied inverse is smooth there.
Together with M12's local product factorization, this is the local
regularity input for the physical inverse-cylinder curve.
-/

set_option autoImplicit false
-- The actual spatial tangent models have the same finite dimension.
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

/-- The actual raw spatial map is a local diffeomorphism on its open
physical source. Source: Definition 3.38 and Proposition 16.13,
pp. 61 and 377-378. -/
theorem rawCylinder_spatial_localDiffeomorph [Nonempty U] (s : J.domain) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (rawSpatialMap e s) := by
  apply isLocalDiffeomorph_of_contMDiff_mfderiv_bijective (rawSpatialMap_smooth e s)
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg (e.inverse s.val s.property) hxy
    exact (e.left_inverse s.val s.property x.property).symm.trans
      (h.trans (e.left_inverse s.val s.property y.property))
  · intro x
    let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      LinearEquiv.ofInjectiveEndo
        (mfderiv (𝓡 3) (𝓡 3) (rawSpatialMap e s) x).toLinearMap
        (rawSpatialMap_differential_injective e s x)
    exact L.bijective

/-- The spatial image at every included cap time is open in the
actual selected slice. Source: Proposition 16.13, pp. 377-378. -/
theorem rawCylinder_spatial_image_isOpen [Nonempty U] (s : J.domain) :
    IsOpen (e.forward s.val s.property '' U) := by
  have heq : range (rawSpatialMap e s) = e.forward s.val s.property '' U := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← heq]
  exact (rawCylinder_spatial_localDiffeomorph e s).isOpen_range

/-- The supplied actual inverse, with its original physical codomain,
is smooth at each point in the tracked ball image. Source: Proposition
16.13, pp. 377-378. -/
theorem rawCylinder_inverse_contMDiffAt (s : J.domain) (x : U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (e.inverse s.val s.property)
      (e.forward s.val s.property x.val) := by
  let : Nonempty U := ⟨x⟩
  exact (e.inverse_smooth s.val s.property _ (mem_image_of_mem _ x.property)).contMDiffAt
    ((rawCylinder_spatial_image_isOpen e s).mem_nhds (mem_image_of_mem _ x.property))

end PoincareMT.Proofs.M46
