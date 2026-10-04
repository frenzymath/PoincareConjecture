import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Ancient.LimitAncientIdentification
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.R.LimitRP2Transfer
import PoincareLib.Geometry.RicciFlow.Surgery.Control.Calibration

/-!
# The actual calibrated ancient canonical alternative

The infinite-horizon limit is identified on its own carrier. Physical
regular histories exclude the RP2-line exception before the calibrated
Corollary 9.94 is applied. MT Proposition 17.1, pp. 407-408;
limit-canonical-transfer.md, A.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

/-- The same ancient solution has the original calibrated accuracy and
constant at the actual limit basepoint. MT Corollary 9.94 and pp. 407-408. -/
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

end PoincareMT.M47
