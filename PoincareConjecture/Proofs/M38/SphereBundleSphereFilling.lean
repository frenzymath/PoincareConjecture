import PoincareConjecture.Proofs.M38.SphereBundleCylinder
import PoincareConjecture.Proofs.M38.CylinderCoverFilling

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

theorem sphereBundle_sphere_filling_or_lifted_coordinates
    (Q : GeneralizedSliceCarrier) [CompactSpace Q.carrier] (B : SurgerySphereBundle Q)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source) :
    (∃ D : SurgeryBallEmbedding Q,
      frontier D.closedBall = range (fun z : UnitTwoSphere => c (z, 0))) ∨
    (let A := circlePullbackCarrier Q B.projection B.projection_smooth
      ∃ η : ℝ, 0 < η ∧ η < δ ∧
        ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            RoundCylinderSpace A.carrier ∞,
          ∀ p, |p.2| < η →
            circlePullbackProjection Q B.projection B.projection_smooth (D p) = c p) := by
  let A := circlePullbackCarrier Q B.projection B.projection_smooth
  let : AddAction ℤ A.carrier := inferInstanceAs (AddAction ℤ (CirclePullback B.projection))
  obtain ⟨D, _⟩ := exists_sphereBundle_pullback_cylinder Q B
  exact cylinder_quotient_sphere_filling_or_lifted_coordinates D
    (circlePullbackProjection Q B.projection B.projection_smooth)
    (circlePullback_projection_localDiffeomorph Q B.projection B.projection_smooth)
    (IsAddQuotientCoveringMap.toMultiplicative
      (circlePullbackProjection Q B.projection B.projection_smooth) ℤ
      (CirclePullback.projection_isAddQuotientCoveringMap
        B.projection B.projection_continuous)) c hc hci hδ hsource

end PoincareConjecture.M38
