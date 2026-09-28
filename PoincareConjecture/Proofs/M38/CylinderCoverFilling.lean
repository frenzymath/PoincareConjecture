import PoincareConjecture.Proofs.M38.CollarCoverLift
import PoincareConjecture.Proofs.M38.CylinderSphereFilling
import PoincareConjecture.Proofs.M38.ProperDeckBallSeparation

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem cylinder_quotient_sphere_filling_or_lifted_coordinates_of_source_eq
    {A Q : GeneralizedSliceCarrier.{u}}
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrier ∞)
    {G : Type*} [Group G] [MulAction G A.carrier]
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hcover : IsQuotientCoveringMap q G)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : c.source = univ ×ˢ Ioo (-δ) δ) :
    (∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (fun z : UnitTwoSphere => c (z, 0))) ∨
    (∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrier ∞,
        ∀ p : RoundCylinderSpace, |p.2| < η → q (D p) = c p) := by
  classical
  let z₀ : UnitTwoSphere := Classical.choice inferInstance
  obtain ⟨a₀, ha₀⟩ := hcover.surjective (c (z₀, 0))
  obtain ⟨C, hCs, _, hC, hCi, hqC⟩ :=
    exists_smooth_collar_lift q hq hcover.isCoveringMap c hc hci hδ hsource z₀ a₀ ha₀
  rcases cylinder_sphere_filling_or_collar_coordinates_of_source_eq A T C hC hCi
    hδ (hCs.trans hsource) with ⟨B, hB⟩ | ⟨η, hη, hηδ, D, hD⟩
  · have hA : IsPreconnected (univ : Set A.carrier) := by
      have heq : T '' (univ : Set RoundCylinderSpace) = univ :=
        image_univ_of_surjective T.surjective
      rw [← heq]
      exact isPreconnected_univ.image T T.contMDiff.continuous.continuousOn
    have hnoncompact : ¬ IsCompact (univ : Set A.carrier) := by
      intro hcompact
      apply noncompact_univ RoundCylinderSpace
      have heq : T.symm '' (univ : Set A.carrier) = univ :=
        image_univ_of_surjective T.symm.surjective
      rw [← heq]
      exact hcompact.image T.symm.contMDiff.continuous
    have hzero (z : UnitTwoSphere) : (z, (0 : ℝ)) ∈ c.source := by
      rw [hsource]
      exact ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
    have hinj : Function.Injective (fun z : UnitTwoSphere => c (z, 0)) := by
      intro z w hzw
      exact congrArg Prod.fst (c.injOn (hzero z) (hzero w) hzw)
    obtain ⟨B', _, _, hB'⟩ := exists_surgeryBall_descend_lifted_sphere hA hnoncompact
      q hq hcover (fun z : UnitTwoSphere => c (z, 0)) hinj
      (fun z : UnitTwoSphere => C (z, 0)) (fun z => hqC _ (hzero z)) B hB
    exact Or.inl ⟨B', hB'⟩
  · right
    refine ⟨η, hη, hηδ, D, fun p hp => ?_⟩
    rw [hD p hp]
    apply hqC p
    rw [hsource]
    exact ⟨mem_univ _, abs_lt.mp (hp.trans hηδ)⟩

theorem cylinder_quotient_sphere_filling_or_lifted_coordinates
    {A Q : GeneralizedSliceCarrier.{u}}
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrier ∞)
    {G : Type*} [Group G] [MulAction G A.carrier]
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hcover : IsQuotientCoveringMap q G)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source) :
    (∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (fun z : UnitTwoSphere => c (z, 0))) ∨
    (∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrier ∞,
        ∀ p : RoundCylinderSpace, |p.2| < η → q (D p) = c p) := by
  let V : Set RoundCylinderSpace := univ ×ˢ Ioo (-δ) δ
  let d := c.restr V
  have hV : IsOpen V := isOpen_univ.prod isOpen_Ioo
  have hds : d.source = V :=
    (c.restr_source' V hV).trans (inter_eq_right.mpr hsource)
  exact cylinder_quotient_sphere_filling_or_lifted_coordinates_of_source_eq T q hq hcover d
    (hc.mono (fun _ h => h.1)) (hci.mono (fun _ h => h.1)) hδ hds

end PoincareConjecture.M38
