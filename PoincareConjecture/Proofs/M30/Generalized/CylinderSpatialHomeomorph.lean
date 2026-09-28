import PoincareConjecture.Proofs.M12.GeneralizedCylinderSpatial
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30.Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)



theorem isOpen_spatial_image (s : J.domain) :
    IsOpen (e.forward s.1 s.2 '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  have hi := Proofs.M12.rawForward_differential_injective e s ⟨x, hx⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (e.forward s.1 s.2 x)) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
  have hbij : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (e.forward s.1 s.2) x) :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    ((e.forward_smooth s.1 s.2 x hx).contMDiffAt (U.isOpen.mem_nhds hx)) hbij]
  exact image_mem_map (U.isOpen.mem_nhds hx)



def spatialHomeomorph (s : J.domain) :
    OpenPartialHomeomorph C.carrier (F.slice (a + s.1 / q)).carrier where
  toFun := e.forward s.1 s.2
  invFun := e.inverse s.1 s.2
  source := U
  target := e.forward s.1 s.2 '' U
  map_source' x hx := mem_image_of_mem _ hx
  map_target' y hy := by
    rcases hy with ⟨x, hx, rfl⟩
    rw [e.left_inverse s.1 s.2 hx]
    exact hx
  left_inv' := e.left_inverse s.1 s.2
  right_inv' := e.right_inverse s.1 s.2
  open_source := U.isOpen
  open_target := isOpen_spatial_image e s
  continuousOn_toFun := (e.forward_smooth s.1 s.2).continuousOn
  continuousOn_invFun := (e.inverse_smooth s.1 s.2).continuousOn



theorem spatialHomeomorph_contMDiffAt (s : J.domain) {x : C.carrier}
    (hx : x ∈ (spatialHomeomorph e s).source) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (spatialHomeomorph e s) x :=
  (e.forward_smooth s.1 s.2 x hx).contMDiffAt (U.isOpen.mem_nhds hx)



theorem spatialHomeomorph_symm_contMDiffAt (s : J.domain)
    {y : (F.slice (a + s.1 / q)).carrier}
    (hy : y ∈ (spatialHomeomorph e s).target) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (spatialHomeomorph e s).symm y :=
  (e.inverse_smooth s.1 s.2 y hy).contMDiffAt
    ((isOpen_spatial_image e s).mem_nhds hy)

end PoincareConjecture.M30.Cylinder
