import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def cylinderDomainOpen : Opens RoundCylinderSpace :=
  ⟨N.cylinderDomain, N.cylinderDomain_open⟩

def carrierOpen : Opens M := ⟨N.carrier, N.carrier_open⟩

def coordinateDiffeomorph : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    N.cylinderDomainOpen N.carrierOpen ∞ where
  toFun z := ⟨N.coordinate_map z, N.coordinate_map_mem z.property⟩
  invFun x := ⟨N.coordinate_inverse x, N.coordinate_inverse_mem x x.property⟩
  left_inv z := Subtype.ext (N.coordinate_inverse_coordinate_map z.property)
  right_inv x := Subtype.ext (N.coordinate_map_coordinate_inverse x.property)
  contMDiff_toFun := by
    rw [← ContMDiff.subtypeVal_comp_iff N.carrierOpen]
    exact N.coordinate_map_smooth.comp_contMDiff contMDiff_subtype_val fun z => z.property
  contMDiff_invFun := by
    rw [← ContMDiff.subtypeVal_comp_iff N.cylinderDomainOpen]
    exact N.coordinate_inverse_smooth.comp_contMDiff contMDiff_subtype_val fun x => x.property

@[simp] theorem coordinateDiffeomorph_apply (z : N.cylinderDomainOpen) :
    (N.coordinateDiffeomorph z : M) = N.coordinate_map z := rfl

@[simp] theorem coordinateDiffeomorph_symm_apply (x : N.carrierOpen) :
    (N.coordinateDiffeomorph.symm x : RoundCylinderSpace) = N.coordinate_inverse x := rfl

end PoincareConjecture.EpsilonNeck
