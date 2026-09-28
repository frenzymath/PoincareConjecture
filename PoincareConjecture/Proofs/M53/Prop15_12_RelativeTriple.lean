import PoincareConjecture.Proofs.M02.Topology.IntegralMayerVietorisExcision

set_option autoImplicit false

noncomputable section

open CategoryTheory
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

variable {X : Type u} [TopologicalSpace X] (A B : Set X) (h : B ⊆ A)

def integralTripleBoundary (n : Nat) : integralRelativeHomology A (n + 1) ⟶
    integralRelativeHomology ((Subtype.val : A → X) ⁻¹' B) n :=
  (integralNestedRelativePairSequence_shortExact B A h).δ (n + 1) n rfl

def integralPairToTriple :
    integralPairSequence A ⟶ integralNestedRelativePairSequence B A h where
  τ₁ := integralRelativeProjection ((Subtype.val : A → X) ⁻¹' B)
  τ₂ := integralRelativeProjection B
  τ₃ := 𝟙 _
  comm₁₂ := integralPairInclusion_projection B A
  comm₂₃ := by
    change integralRelativeProjection B ≫ integralRelativeRestriction h =
      integralRelativeProjection A ≫ 𝟙 _
    rw [integralRelativeRestriction_projection, Category.comp_id]

theorem integralTripleBoundary_eq_pair (n : Nat) :
    integralTripleBoundary A B h n = integralRelativeBoundary A n ≫
      integralToRelativeHomology ((Subtype.val : A → X) ⁻¹' B) n := by
  have hn := HomologicalComplex.HomologySequence.δ_naturality
    (integralPairToTriple A B h) (integralPairSequence_shortExact A)
    (integralNestedRelativePairSequence_shortExact B A h) (n + 1) n rfl
  change integralRelativeBoundary A n ≫
      integralToRelativeHomology ((Subtype.val : A → X) ⁻¹' B) n =
    HomologicalComplex.homologyMap (𝟙 (integralRelativeChains A)) (n + 1) ≫
      integralTripleBoundary A B h n at hn
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at hn
  exact hn.symm

end PoincareConjecture.Proofs.M53
