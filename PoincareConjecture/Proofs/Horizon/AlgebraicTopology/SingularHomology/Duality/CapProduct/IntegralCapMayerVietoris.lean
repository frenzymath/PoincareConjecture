import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralLocalizedCap
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.Support.IntegralSupportCohomologyMV








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSubspaceChains_range_mono {A B : Set X} (h : A ⊆ B) (n : Nat) :
    LinearMap.range ((integralSubspaceChains A).f n).hom ≤
      LinearMap.range ((integralSubspaceChains B).f n).hom := by
  rintro _ ⟨c, rfl⟩
  exact ⟨(integralNestedChains h).f n c,
    congrArg (fun f => f.f n c) (integralNestedChains_subspaceChains h)⟩

theorem integralCochainPullback_pushforward {K L : Set X} (h : K ⊆ L)
    (q : Nat) (phi : (integralSupportCochains K).X q) :
    (integralDualMap (integralRelativeProjection Lᶜ)).f q
      ((integralSupportCochainPushforward h).f q phi) =
      (integralDualMap (integralRelativeProjection Kᶜ)).f q phi := by
  have he : integralSupportCochainPushforward h ≫
      integralDualMap (integralRelativeProjection Lᶜ) =
      integralDualMap (integralRelativeProjection Kᶜ) := by
    rw [integralSupportCochainPushforward, ← integralDualMap_comp,
      integralSupportRestriction_projection]
  exact congrArg (fun f => f.f q phi) he

theorem integralLocalizedCap_nested {U V K L : Set X}
    (hU : U ⊆ V) (hK : K ⊆ L) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hcU : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) (p + q))
    (hcV : c ∈ integralSmallChains (integralBinaryCover V Lᶜ) (p + q))
    (phi : (integralSupportCochains K).X q) :
    (integralNestedChains hU).f p (integralLocalizedCap U K p q c hcU phi) =
      integralLocalizedCap V L p q c hcV
        ((integralSupportCochainPushforward hK).f q phi) := by
  let := integralSubspaceChains_mono V
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains V).f p)).mp inferInstance
  have hcomp := congrArg (fun f => f.f p (integralLocalizedCap U K p q c hcU phi))
    (integralNestedChains_subspaceChains hU)
  refine hcomp.trans ?_
  rw [integralLocalizedCap_inclusion, integralLocalizedCap_inclusion,
    integralCochainPullback_pushforward]

theorem integralLocalizedCap_three_one_boundary (U K : Set X)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (phi : (integralSupportCochains K).X 1) :
    (integralChains U).d 2 1 (integralLocalizedCap U K 2 1 c hc phi) =
      integralLocalizedCap U K 1 2 c hc ((integralSupportCochains K).d 1 2 phi) := by
  let := integralSubspaceChains_mono U
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains U).f 1)).mp inferInstance
  have hcomm := congrArg (fun f => f (integralLocalizedCap U K 2 1 c hc phi))
    ((integralSubspaceChains U).comm 2 1)
  change (integralChains X).d 2 1
    ((integralSubspaceChains U).f 2 (integralLocalizedCap U K 2 1 c hc phi)) =
      (integralSubspaceChains U).f 1
        ((integralChains U).d 2 1 (integralLocalizedCap U K 2 1 c hc phi)) at hcomm
  rw [← hcomm, integralLocalizedCap_inclusion, integralLocalizedCap_inclusion,
    integralCap_three_one_boundary]
  have hphi := congrArg (fun f => f phi)
    ((integralDualMap (integralRelativeProjection Kᶜ)).comm 1 2)
  change (integralCochains X).d 1 2
    ((integralDualMap (integralRelativeProjection Kᶜ)).f 1 phi) =
      (integralDualMap (integralRelativeProjection Kᶜ)).f 2
        ((integralSupportCochains K).d 1 2 phi) at hphi
  rw [hphi, integralCap_relative_cochain_zero Kᶜ 1 1 _ hdc, sub_zero]

theorem integralLocalizedCap_three_two_cycle (U K : Set X)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (phi : (integralSupportCochains K).X 2)
    (hphi : (integralSupportCochains K).d 2 3 phi = 0) :
    (integralChains U).d 1 0 (integralLocalizedCap U K 1 2 c hc phi) = 0 := by
  let := integralSubspaceChains_mono U
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains U).f 0)).mp inferInstance
  have hcomm := congrArg (fun f => f (integralLocalizedCap U K 1 2 c hc phi))
    ((integralSubspaceChains U).comm 1 0)
  change (integralChains X).d 1 0
    ((integralSubspaceChains U).f 1 (integralLocalizedCap U K 1 2 c hc phi)) =
      (integralSubspaceChains U).f 0
        ((integralChains U).d 1 0 (integralLocalizedCap U K 1 2 c hc phi)) at hcomm
  rw [← hcomm, integralLocalizedCap_inclusion, map_zero, integralCap_three_two_boundary]
  have hpull := congrArg (fun f => f phi)
    ((integralDualMap (integralRelativeProjection Kᶜ)).comm 2 3)
  change (integralCochains X).d 2 3
    ((integralDualMap (integralRelativeProjection Kᶜ)).f 2 phi) =
      (integralDualMap (integralRelativeProjection Kᶜ)).f 3
        ((integralSupportCochains K).d 2 3 phi) at hpull
  rw [hpull, hphi, map_zero, integralCap_relative_cochain_zero Kᶜ 0 2 _ hdc,
    map_zero, sub_zero]

theorem integralLocalizedCap_three_two_boundary (U K : Set X)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (phi : (integralSupportCochains K).X 2) :
    (integralChains U).d 1 0 (integralLocalizedCap U K 1 2 c hc phi) =
      -integralLocalizedCap U K 0 3 c hc
        ((integralSupportCochains K).d 2 3 phi) := by
  let := integralSubspaceChains_mono U
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains U).f 0)).mp inferInstance
  have hcomm := congrArg (fun f => f (integralLocalizedCap U K 1 2 c hc phi))
    ((integralSubspaceChains U).comm 1 0)
  change (integralChains X).d 1 0
    ((integralSubspaceChains U).f 1 (integralLocalizedCap U K 1 2 c hc phi)) =
      (integralSubspaceChains U).f 0
        ((integralChains U).d 1 0 (integralLocalizedCap U K 1 2 c hc phi)) at hcomm
  rw [← hcomm, integralLocalizedCap_inclusion, map_neg,
    integralLocalizedCap_inclusion, integralCap_three_two_boundary]
  have hpull := congrArg (fun f => f phi)
    ((integralDualMap (integralRelativeProjection Kᶜ)).comm 2 3)
  change (integralCochains X).d 2 3
    ((integralDualMap (integralRelativeProjection Kᶜ)).f 2 phi) =
      (integralDualMap (integralRelativeProjection Kᶜ)).f 3
        ((integralSupportCochains K).d 2 3 phi) at hpull
  rw [hpull, integralCap_relative_cochain_zero Kᶜ 0 2 _ hdc, zero_sub]

end Poincare.Topology
