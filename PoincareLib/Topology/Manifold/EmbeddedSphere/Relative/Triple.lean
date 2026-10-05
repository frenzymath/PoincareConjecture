import PoincareLib.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralMayerVietorisExcision

/-!
# The boundary map for an integral relative triple

For `B ⊆ A ⊆ X`, the connecting map of the actual M02 triple sequence
is the ordinary pair boundary followed by the relative projection on `A`.
This is the naturality of Hatcher's homology sequence, Theorem 2.16 and
the triple sequence, pp. 117-118. It supplies the algebraic part of the
local jump needed by the sphere-separation repair of Morgan--Tian,
Proposition 15.12 and Remark 15.13, p. 365; see M53 derivation 03.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {X : Type u} [TopologicalSpace X] (A B : Set X) (h : B ⊆ A)

/-- The connecting map `H_(n+1)(X,A) -> H_n(A,B)` of the actual relative
triple sequence; Hatcher, Theorem 2.16 and triple sequence, pp. 117-118. -/
def integralTripleBoundary (n : Nat) : integralRelativeHomology A (n + 1) ⟶
    integralRelativeHomology ((Subtype.val : A → X) ⁻¹' B) n :=
  (integralNestedRelativePairSequence_shortExact B A h).δ (n + 1) n rfl

/-- Quotienting the pair sequence by `B` gives the triple sequence, with
identity on `C(X,A)`; Hatcher, pp. 117-118. -/
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

/-- The triple boundary is the ordinary pair boundary followed by projection
to relative homology of `A`; naturality in Hatcher's sequence, pp. 117-118. -/
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

end PoincareMT.Topology.EmbeddedSphere
