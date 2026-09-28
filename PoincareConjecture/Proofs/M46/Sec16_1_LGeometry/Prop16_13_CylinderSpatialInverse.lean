import PoincareConjecture.Proofs.M12.GeneralizedCylinderSpatial
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SliceMap











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)




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




theorem rawCylinder_inverse_contMDiffAt (s : J.domain) (x : U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (e.inverse s.val s.property)
      (e.forward s.val s.property x.val) := by
  let : Nonempty U := ⟨x⟩
  exact (e.inverse_smooth s.val s.property _ (mem_image_of_mem _ x.property)).contMDiffAt
    ((rawCylinder_spatial_image_isOpen e s).mem_nhds (mem_image_of_mem _ x.property))

end PoincareConjecture.Proofs.M46
