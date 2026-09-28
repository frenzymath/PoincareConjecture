import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import PoincareConjecture.Statements.Ch01.Topology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def ReparameterizedLoops (γ₁ γ₂ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ r : CircleReparameterization, ∀ z : LoopCircle,
    γ₁ z = γ₂ (r.map z)

structure LoopSpaceWidthPredecessors where
  manifold : CompactConnectedThreeManifold (M := M)
  metric : RiemannianMetric 3 M
  basepoint : M
  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)

structure LoopSpaceWidthConclusions (P : LoopSpaceWidthPredecessors (M := M)) where

  identity_component_null_homotopic :
    ∀ γ : C1FreeLoopSpace (M := M),
      InIdentityComponent P.basepoint γ ↔ IsNullHomotopicLoop γ

  pi_two_loop_equiv_pi_three :
    Nonempty (HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop P.basepoint) ≃* HomotopyGroup.Pi 3 M P.basepoint)

  class_representative :
    ∀ α : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop P.basepoint),
      ∃ Γ : FreeTwoSphereFamily (M := M),
        familySigmaClass Γ = ⟨P.basepoint, α⟩

  filling_area_well_defined :
    ∀ γ : C1FreeLoopSpace (M := M), IsNullHomotopicLoop γ →
      FillingAreaData P.metric γ

  filling_area_reparameterization_invariant :
    ∀ γ₁ γ₂ : C1FreeLoopSpace (M := M), ReparameterizedLoops γ₁ γ₂ →
      fillingArea P.metric γ₁ = fillingArea P.metric γ₂

  filling_area_continuous_on_component :
    ContinuousOn (fun γ : C1FreeLoopSpace (M := M) => fillingArea P.metric γ)
      {γ | IsNullHomotopicLoop γ}

  family_width_is_maximum :
    ∀ Γ : FreeTwoSphereFamily (M := M), FamilyWidthData P.metric Γ

  class_width_is_infimum :
    ∀ ξ : FreeTwoSphereFamily (M := M), ClassWidthData P.metric ξ

  width_nonnegative :
    ∀ Γ : FreeTwoSphereFamily (M := M), 0 ≤ familyWidth P.metric Γ
  class_width_nonnegative :
    ∀ ξ : FreeTwoSphereFamily (M := M), 0 ≤ classWidth P.metric ξ

end PoincareConjecture
