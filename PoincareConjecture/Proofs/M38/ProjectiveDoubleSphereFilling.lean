import PoincareConjecture.Proofs.M38.ProjectiveDoubleCover
import PoincareConjecture.Proofs.M38.CylinderCarrier
import PoincareConjecture.Proofs.M38.CylinderCoverFilling
import Mathlib.Algebra.Module.ULift











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] cylinderDihedralAction cylinderLiftChartedSpace


@[instance_reducible]
noncomputable def cylinderCarrierDihedralAction :
    MulAction (DihedralGroup 0) cylinderCarrier.{u}.carrier where
  smul g p := ULift.up (g • p.down)
  one_smul p := by
    apply ULift.ext
    exact one_smul _ p.down
  mul_smul g h p := by
    apply ULift.ext
    exact mul_smul g h p.down

attribute [local instance] cylinderCarrierDihedralAction


theorem cylinderDihedral_lifted_quotient_cover
    {Q : GeneralizedSliceCarrier.{u}} (q : RoundCylinderSpace → Q.carrier)
    (h : IsQuotientCoveringMap q (DihedralGroup 0)) :
    IsQuotientCoveringMap (fun p : cylinderCarrier.{u}.carrier => q p.down) (DihedralGroup 0) := by
  refine {
    toIsQuotientMap := h.toIsQuotientMap.comp
      (Homeomorph.ulift : cylinderCarrier.{u}.carrier ≃ₜ RoundCylinderSpace).isQuotientMap
    continuous_const_smul := ?_
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro g
    change Continuous (fun p : cylinderCarrier.{u}.carrier => ULift.up (g • p.down))
    exact continuous_uliftUp.comp ((h.continuous_const_smul g).comp continuous_uliftDown)
  · intro x y
    rw [h.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply ULift.ext
      exact hg
    · rintro ⟨g, hg⟩
      exact ⟨g, congrArg (fun p : cylinderCarrier.{u}.carrier => p.down) hg⟩
  · intro p
    obtain ⟨U, hU, hsep⟩ := h.disjoint p.down
    refine ⟨ULift.down ⁻¹' U, continuous_uliftDown.continuousAt.preimage_mem_nhds hU, ?_⟩
    intro g hg
    apply hsep g
    obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := hg
    change g • y.down ∈ U at hx
    exact ⟨g • y.down, ⟨y.down, hy, rfl⟩, hx⟩




theorem projectiveDouble_sphere_filling_or_lifted_coordinates
    (Q : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel Q.carrier)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source) :
    (∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (fun z : UnitTwoSphere => c (z, 0))) ∨
    (∃ q : RoundCylinderSpace → Q.carrier,
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q ∧
      Function.Surjective q ∧
      (∀ x y, q x = q y ↔
        ∃ n : ℤ, x = cylinderIntegerTranslation n y ∨ x = cylinderIntegerReflection n y) ∧
      ∃ η : ℝ, 0 < η ∧ η < δ ∧
        ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
            RoundCylinderSpace RoundCylinderSpace ∞,
          ∀ p, |p.2| < η → q (D p) = c p) := by
  obtain ⟨q, hq, hsurj, _, hfibers, hcover, _⟩ := exists_projectiveDouble_cylinder_cover Q C
  let q' : cylinderCarrier.{u}.carrier → Q.carrier := fun p => q p.down
  have hq' : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q' := fun p =>
    (cylinderCarrierDiffeomorph.symm.isLocalDiffeomorph p).comp (𝓡 3) Q.carrier (hq p.down)
  rcases cylinder_quotient_sphere_filling_or_lifted_coordinates cylinderCarrierDiffeomorph q' hq'
      (cylinderDihedral_lifted_quotient_cover q hcover) c hc hci hδ hsource
      with hfill | ⟨η, hη, hηδ, D, hD⟩
  · exact Or.inl hfill
  · exact Or.inr ⟨q, hq, hsurj, hfibers, η, hη, hηδ,
      D.trans cylinderCarrierDiffeomorph.symm, hD⟩

end PoincareConjecture.M38
