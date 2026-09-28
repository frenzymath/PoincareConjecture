import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCap
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapDegrees







set_option autoImplicit false

open CategoryTheory

universe u

namespace Poincare.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X]

private theorem projection_d (A : Set X) (i j : Nat) (c : (integralChains X).X i) :
    (integralRelativeChains A).d i j ((integralRelativeProjection A).f i c) =
      (integralRelativeProjection A).f j ((integralChains X).d i j c) :=
  congrArg (fun f => f c) ((integralRelativeProjection A).comm i j)

private theorem dual_projection_d (A : Set X) (i j : Nat)
    (phi : (integralRelativeCochains A).X i) :
    (integralDualMap (integralRelativeProjection A)).f j
      ((integralRelativeCochains A).d i j phi) =
    (integralCochains X).d i j
      ((integralDualMap (integralRelativeProjection A)).f i phi) :=
  (congrArg (fun f => f phi) ((integralDualMap (integralRelativeProjection A)).comm i j)).symm

theorem integralSupportCap_three_zero_boundary (A : Set X)
    (c : (integralRelativeChains A).X 3) (phi : (integralRelativeCochains A).X 0) :
    (integralChains X).d 3 2 (integralSupportCap A 3 0 c phi) =
      integralSupportCap A 2 0 ((integralRelativeChains A).d 3 2 c) phi -
        integralSupportCap A 2 1 c ((integralRelativeCochains A).d 0 1 phi) := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 3)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_three_zero_boundary b _

theorem integralSupportCap_three_one_boundary (A : Set X)
    (c : (integralRelativeChains A).X 3) (phi : (integralRelativeCochains A).X 1) :
    (integralChains X).d 2 1 (integralSupportCap A 2 1 c phi) =
      integralSupportCap A 1 2 c ((integralRelativeCochains A).d 1 2 phi) -
        integralSupportCap A 1 1 ((integralRelativeChains A).d 3 2 c) phi := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 3)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_three_one_boundary b _

theorem integralSupportCap_three_two_boundary (A : Set X)
    (c : (integralRelativeChains A).X 3) (phi : (integralRelativeCochains A).X 2) :
    (integralChains X).d 1 0 (integralSupportCap A 1 2 c phi) =
      integralSupportCap A 0 2 ((integralRelativeChains A).d 3 2 c) phi -
        integralSupportCap A 0 3 c ((integralRelativeCochains A).d 2 3 phi) := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 3)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_three_two_boundary b _

theorem integralSupportCap_four_zero_boundary (A : Set X)
    (c : (integralRelativeChains A).X 4) (phi : (integralRelativeCochains A).X 0) :
    (integralChains X).d 4 3 (integralSupportCap A 4 0 c phi) =
      integralSupportCap A 3 0 ((integralRelativeChains A).d 4 3 c) phi -
        integralSupportCap A 3 1 c ((integralRelativeCochains A).d 0 1 phi) := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 4)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_four_zero_boundary b _

theorem integralSupportCap_four_one_boundary (A : Set X)
    (c : (integralRelativeChains A).X 4) (phi : (integralRelativeCochains A).X 1) :
    (integralChains X).d 3 2 (integralSupportCap A 3 1 c phi) =
      integralSupportCap A 2 2 c ((integralRelativeCochains A).d 1 2 phi) -
        integralSupportCap A 2 1 ((integralRelativeChains A).d 4 3 c) phi := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 4)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_four_one_boundary b _

theorem integralSupportCap_four_two_boundary (A : Set X)
    (c : (integralRelativeChains A).X 4) (phi : (integralRelativeCochains A).X 2) :
    (integralChains X).d 2 1 (integralSupportCap A 2 2 c phi) =
      integralSupportCap A 1 2 ((integralRelativeChains A).d 4 3 c) phi -
        integralSupportCap A 1 3 c ((integralRelativeCochains A).d 2 3 phi) := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 4)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_four_two_boundary b _

theorem integralSupportCap_four_three_boundary (A : Set X)
    (c : (integralRelativeChains A).X 4) (phi : (integralRelativeCochains A).X 3) :
    (integralChains X).d 1 0 (integralSupportCap A 1 3 c phi) =
      integralSupportCap A 0 4 c ((integralRelativeCochains A).d 3 4 phi) -
        integralSupportCap A 0 3 ((integralRelativeChains A).d 4 3 c) phi := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((integralRelativeProjection A).f 4)).mp inferInstance c
  rw [projection_d, integralSupportCap_projection, integralSupportCap_projection,
    integralSupportCap_projection, dual_projection_d]
  exact integralCap_four_three_boundary b _

end

end Poincare.Topology
