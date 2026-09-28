import PoincareConjecture.Proofs.M47.LimitAncientIdentification
import PoincareConjecture.Proofs.M47.LimitRP2Transfer
import PoincareConjecture.Definitions.M45ControlledSchedules

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem limitCanonical_ancient_alternative
    (h04 : RicciFlowCurvatureTheory.{u}) (S : RepairedControlledSchedulesData.{u})
    {V : GeneralizedBlowupSequence.{u}}
    (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification h04 G.limit kappa hkappa hnc).certificate.solution
    M27StrongCanonicalNeighborhood K 0 G.limit.base S.setup.epsilon S.calibration.Ckappa ∧
      S.calibration.Ckappa ≤ S.setup.C := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
    (limitAncientIdentification h04 G.limit kappa hkappa hnc).certificate.solution
  have hnot : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) :=
    limitRP2_no_projectivePlaneLine G F R K
  refine ⟨S.calibration.kappa_canonical K hnot _ (Or.inl rfl) 0 le_rfl G.limit.base, ?_⟩
  rw [S.calibration.setup_C_eq]
  exact le_max_left _ _

end PoincareConjecture.M47
