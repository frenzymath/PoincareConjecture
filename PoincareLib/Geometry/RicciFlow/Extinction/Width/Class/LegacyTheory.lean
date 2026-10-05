import PoincareLib.Geometry.Riemannian.LoopSpace.Width
import PoincareLib.Topology.Manifold.ThreeDimensional.Conclusion

/-!
# Loop-space width milestone

The proposition layer records Claim 18.16 and Definition 18.17 with all
regularity and compactness interfaces made explicit.  The filling and width
infima are over the concrete disk and family types in the definitions file.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Two loops differ only by an explicit circle reparameterization. -/
def ReparameterizedLoops (γ₁ γ₂ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ r : CircleReparameterization, ∀ z : LoopCircle,
    γ₁ z = γ₂ (r.map z)

/-- Inputs supplied by the preceding geometric and variational milestones. -/
structure LoopSpaceWidthPredecessors where
  manifold : CompactConnectedThreeManifold (M := M)
  metric : RiemannianMetric 3 M
  basepoint : M
  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)

/-- Complete conclusions of Claim 18.16 and Definition 18.17. -/
structure LoopSpaceWidthConclusions (P : LoopSpaceWidthPredecessors (M := M)) where
  /-- The identity component is exactly the null-homotopic loop component. -/
  identity_component_null_homotopic :
    ∀ γ : C1FreeLoopSpace (M := M),
      InIdentityComponent P.basepoint γ ↔ IsNullHomotopicLoop γ
  /-- Claim 18.16's based homotopy-group identification. -/
  pi_two_loop_equiv_pi_three :
    Nonempty (HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop P.basepoint) ≃* HomotopyGroup.Pi 3 M P.basepoint)
  /-- Every based class admits the displayed regular sphere-family model. -/
  class_representative :
    ∀ α : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop P.basepoint),
      ∃ Γ : FreeTwoSphereFamily (M := M),
        familySigmaClass Γ = ⟨P.basepoint, α⟩
  /-- The admissible filling class is nonempty and its area infimum is finite. -/
  filling_area_well_defined :
    ∀ γ : C1FreeLoopSpace (M := M), IsNullHomotopicLoop γ →
      FillingAreaData P.metric γ
  /-- Filling area is invariant under the allowed circle reparameterizations. -/
  filling_area_reparameterization_invariant :
    ∀ γ₁ γ₂ : C1FreeLoopSpace (M := M), ReparameterizedLoops γ₁ γ₂ →
      fillingArea P.metric γ₁ = fillingArea P.metric γ₂
  /-- Continuity of filling area on the null-homotopic component. -/
  filling_area_continuous_on_component :
    ContinuousOn (fun γ : C1FreeLoopSpace (M := M) => fillingArea P.metric γ)
      {γ | IsNullHomotopicLoop γ}
  /-- Every free sphere family has a finite maximum width. -/
  family_width_is_maximum :
    ∀ Γ : FreeTwoSphereFamily (M := M), FamilyWidthData P.metric Γ
  /-- Class width is the infimum over all free representatives of the class. -/
  class_width_is_infimum :
    ∀ ξ : FreeTwoSphereFamily (M := M), ClassWidthData P.metric ξ
  /-- The zero/nonzero alternative is left to the later extinction milestone. -/
  width_nonnegative :
    ∀ Γ : FreeTwoSphereFamily (M := M), 0 ≤ familyWidth P.metric Γ
  class_width_nonnegative :
    ∀ ξ : FreeTwoSphereFamily (M := M), 0 ≤ classWidth P.metric ξ

end PoincareMT
