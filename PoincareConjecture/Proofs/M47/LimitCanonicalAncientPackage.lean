import PoincareConjecture.Proofs.M47.LimitCanonicalControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitCanonical_eventually_selected_control_of_ancient_package
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (F : ℕ → SurgeryFlowData.{u})
    (W : ∀ k, M33RegularHistoryWindow (F k))
    (history : ∀ k, M33RegularHistoryData (W k))
    (baseTime : ℕ → ℝ)
    (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
    (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
    (hPositive : ∀ k,
      0 < ((F k).connection (baseTime k)).scalarCurvature
        ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
    (hDiverges : Tendsto
      (fun k => ((F k).connection (baseTime k)).scalarCurvature
        ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
      atTop atTop)
    (_C : M30GeometricLongControls
      (regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges) ⊤)
    (G : GeneralizedBlowupConvergence
      (regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges)
      (blowupBackwardInterval ⊤))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    ∀ᶠ k in atTop,
      SurgeryCanonicalControl (F (G.subsequence k))
        (baseTime (G.subsequence k))
        ((history (G.subsequence k)).history.forward
          (baseTime (G.subsequence k))
          (hbaseTime (G.subsequence k))
          (basePoint (G.subsequence k)))
        S.setup.epsilon S.setup.C := by
  exact limitCanonical_eventually_selected_control
    (F := F) (W := W) (history := history) (baseTime := baseTime)
    (hbaseTime := hbaseTime) (basePoint := basePoint)
    (hPositive := hPositive) (hDiverges := hDiverges) (G := G)
    P S hkappa hnc

end PoincareConjecture.M47
