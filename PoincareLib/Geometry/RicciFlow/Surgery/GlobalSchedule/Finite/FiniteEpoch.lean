import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Epoch.EpochEventCount

/-!
# A finite number of actual restarts reaches the epoch boundary

Morgan--Tian Section 17.2 and Lemma 17.12, pp. 409-411. Each unsuccessful
step inserts its old excluded horizon into a finite ledger of observed
surgery times. One fixed M49 bound rules out N+1 such insertions.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M51

open M51Numerical

/-- Repeat the actual calibrated restart until the right epoch boundary.
The integer bound is uniform over stages of the same starting flow; it is
produced by `uniformEpochEventCount` from the retained M49 service. -/
theorem EpochStage.reachBoundary
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S} {C : RepairedCanonicalInductionData S N}
    {n : ℕ} {F : SurgeryFlowData.{u}} (X₀ : EpochStage S N C n F)
    (calibration : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (delta : ℝ → ℝ)
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j)
    (bound : ℕ)
    (hbound : ∀ X : EpochStage S N C n F, ∀ A : Finset ℝ,
      (↑A : Set ℝ) ⊆ X.extension.extended.surgery_times ∩
        surgeryObservationInterval X.observation → A.card ≤ bound) :
    ∃ Y : EpochStage S N C n F,
      Y.observation.H = surgeryEpochStart ((prefixAt S N C n).i + 1) := by
  classical
  have finite_ledger (k : ℕ) :
      ∃ X : EpochStage S N C n F,
        X.observation.H = surgeryEpochStart ((prefixAt S N C n).i + 1) ∨
        ∃ A : Finset ℝ, A.card = k ∧
          (↑A : Set ℝ) ⊆ X.extension.extended.surgery_times ∩
            surgeryObservationInterval X.observation := by
    induction k with
    | zero => exact ⟨X₀, Or.inr ⟨∅, rfl, by simp⟩⟩
    | succ k ih =>
        obtain ⟨X, hsuccess | ⟨A, hcard, hledger⟩⟩ := ih
        · exact ⟨X, Or.inl hsuccess⟩
        · by_cases hsuccess : X.observation.H = surgeryEpochStart ((prefixAt S N C n).i + 1)
          · exact ⟨X, Or.inl hsuccess⟩
          · obtain ⟨Y, hprogress, hnew, hold⟩ := X.advance calibration P
              hdelta hprofiles hcut (lt_of_le_of_ne X.horizon_le hsuccess)
            have hfresh : X.observation.H ∉ A := by
              intro hmem
              exact lt_irrefl _ (hledger hmem).2.2
            refine ⟨Y, Or.inr ⟨insert X.observation.H A, ?_, ?_⟩⟩
            · simp only [Finset.card_insert_of_notMem hfresh, hcard]
            · intro t ht
              rcases Finset.mem_insert.mp ht with hnewtime | hprevious
              · subst t
                exact ⟨hnew, X.observation.H_pos.le, hprogress⟩
              · have htold := hledger hprevious
                exact ⟨hold htold.1, htold.2.1, htold.2.2.trans hprogress⟩
  obtain ⟨Y, hsuccess | ⟨A, hcard, hledger⟩⟩ := finite_ledger (bound + 1)
  · exact ⟨Y, hsuccess⟩
  · have hle := hbound Y A hledger
    rw [hcard] at hle
    exact (Nat.not_succ_le_self bound hle).elim

end PoincareMT.M51
