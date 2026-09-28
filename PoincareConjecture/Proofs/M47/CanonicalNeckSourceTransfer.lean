import PoincareConjecture.Proofs.M47.CanonicalNeckOpenSource
import PoincareConjecture.Proofs.M47.CanonicalNeckPartialIsometry









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_full_open_source_neck
    {C : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 C.carrier}
    (N : EpsilonNeck g) (U : TopologicalSpace.Opens C.carrier)
    (hU : (U : Set C.carrier) = N.carrier)
    (gU : RiemannianMetric 3 (neckOpenSourceCarrier U).carrier) (D : LeviCivitaData gU)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      gU.inner x v w = g.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) :
    ∃ N0 : EpsilonNeck gU, N0.epsilon = N.epsilon ∧ N0.scale = N.scale ∧
      N0.connection = D ∧ N0.center.val = N.center ∧ N0.carrier = univ ∧
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        (N0.coordinate_map z).val = N.coordinate_map z := by
  have hcenter : N.center ∈ (U : Set C.carrier) := by
    rw [hU]
    exact N.central_sphere_subset N.center_on_central_sphere
  let q : U := ⟨N.center, hcenter⟩
  let inclusion := neckOpenSourceInclusion U q
  have htarget : inclusion.target = (U : Set C.carrier) :=
    U.openPartialHomeomorphSubtypeCoe_target ⟨q⟩
  have hm : ∀ x ∈ inclusion.source, ∀ v w : TangentSpace (𝓡 3) x,
      gU.inner x v w = g.inner (inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) inclusion x w) := fun x _hx v w => hmetric x v w
  have hsource : N.carrier ⊆ inclusion.symm.source := by
    change N.carrier ⊆ inclusion.target
    rw [htarget, hU]
  obtain ⟨N0, hepsilon, hscale, hcenter0, hconnection, hcarrier, _hsphere,
    hcoordinate, _hregions⟩ := exists_partialIsometry_neck_image N inclusion.symm
      hsource (partialIsometry_metric_symm inclusion hm) D
  refine ⟨N0, hepsilon, hscale, hconnection, ?_, ?_, ?_⟩
  · rw [hcenter0]
    exact inclusion.right_inv (htarget.symm ▸ hcenter)
  · rw [hcarrier]
    apply Subset.antisymm (subset_univ _)
    intro y _hy
    refine ⟨y.val, ?_, ?_⟩
    · rw [← hU]
      exact y.property
    · exact inclusion.left_inv (mem_univ y)
  · intro z hz
    rw [hcoordinate]
    apply inclusion.right_inv
    rw [htarget, hU]
    exact N.coordinatePartialDiffeomorph.map_source ⟨mem_univ _, hz⟩

end PoincareConjecture.Proofs.M47
