import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalControl
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Limit.SeedLimitNoncollapsed
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Common.TerminalCommonIntervalReindex

/-!
# The ancient horizon contradicts the original first failures

The selected geometric controls produce convergence through the registered
M30 field. Buffered physical volume gives the same limit's all-scale density,
and the four canonical alternatives contradict its original bad point.
Morgan--Tian Proposition 17.1, pp. 407-408.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareMT.Proofs.M47

open PoincareMT.M47

/-- An actual first-failure family cannot have selected geometric controls
on the infinite backward horizon. Convergence and limit noncollapse are
derived here from the original predecessor and physical volume fields. -/
theorem firstFailure_infinite_controls_false
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
    (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
    (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
    (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
    (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
      ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
    (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
      ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma)
    (controls : M30GeometricLongControls
      (terminalCommonInterval_reindex
        (regularHistoryBlowupSequence F W history baseTime hbaseTime
          basePoint hPositive hDiverges) sigma hsigma) ⊤)
    {a w kappa : ℝ} (hw : 0 < w) (hkappa : 0 < kappa)
    (hbase : ∀ k, a ≤ baseTime k)
    (hParameters : ∀ k, (F k).parameters.epsilon = S.setup.epsilon ∧
      (F k).parameters.C = S.setup.C)
    (hvolume : ∀ᶠ k in atTop,
      SurgeryVolumeControlOn (F k) (Icc (a - w) (baseTime k)) kappa (fun _ _ => True))
    (hbad : ∀ k, ¬ SurgeryCanonicalControl (F k) (baseTime k)
      ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))
      (F k).parameters.epsilon (F k).parameters.C) : False := by
  obtain ⟨selected⟩ := P.geometric_limits _ ⊤ controls
  let G := terminalCommonInterval_compSubsequence hsigma selected
  have hcutoff (k : ℕ) : S.setup.epsilon ≤ (F k).parameters.epsilon := by
    rw [(hParameters k).1]
  have hnc := seedLimit_noncollapsed_of_buffered_physical_volume
    P F W history baseTime hbaseTime basePoint hPositive hDiverges G
    hw S.setup.epsilon_pos hkappa hbase hcutoff hvolume
  have hcanonical := limitCanonical_eventually_selected_control
    F W history baseTime hbaseTime basePoint hPositive hDiverges G P S hkappa hnc
  obtain ⟨k, hk⟩ := hcanonical.exists
  apply hbad (G.subsequence k)
  simpa only [(hParameters (G.subsequence k)).1,
    (hParameters (G.subsequence k)).2] using hk

end PoincareMT.Proofs.M47
