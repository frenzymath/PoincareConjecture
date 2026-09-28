import PoincareConjecture.Proofs.M47.TerminalRegularCommonBudget
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalHorizon











set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47


theorem terminalSource_common_slab_of_physical_ceiling
    (F : ℕ → SurgeryFlowData.{u}) (W : ∀ n, M33RegularHistoryWindow (F n))
    (H : ∀ n, M33RegularHistoryData (W n)) (base : ℕ → ℝ)
    (ht : ∀ n, base n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (base n)).carrier)
    (hPositive : ∀ n, 0 < ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n)))
    (hDiverges : Tendsto (fun n => ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n))) atTop atTop)
    (duration : ℕ → ℝ) (hDuration : ∀ m, 0 < duration m)
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma) (K : ℝ) :
    let V := regularHistoryBlowupSequence F W H base ht x hPositive hDiverges
    (∀ (rho : ℕ → ℕ) (hrho : StrictMono rho) (m : ℕ),
      (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        ∀ z ∈ ((F (rho k)).metric (base (rho k))).ball
            ((H (rho k)).history.forward (base (rho k)) (ht (rho k)) (x (rho k)))
            (a / Real.sqrt (V.scale (rho k))),
          ((F (rho k)).connection (base (rho k))).scalarCurvature z ≤
            (2 * ((m : ℝ) + 1)) * V.scale (rho k)) →
      TerminalCommonIntervalSlab (terminalCommonInterval_reindex V rho hrho)
        (duration m / 2)) →
    (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
      ∀ z ∈ ((F (sigma k)).metric (base (sigma k))).ball
          ((H (sigma k)).history.forward (base (sigma k)) (ht (sigma k)) (x (sigma k)))
          (a / Real.sqrt (V.scale (sigma k))),
        ((F (sigma k)).connection (base (sigma k))).scalarCurvature z ≤
          (2 * K) * V.scale (sigma k)) →
    ∃ delta : ℝ, 0 < delta ∧
      TerminalCommonIntervalSlab (terminalCommonInterval_reindex V sigma hsigma) delta := by
  intro V budget ceiling
  obtain ⟨m, hm⟩ := exists_nat_ge K
  refine ⟨duration m / 2, half_pos (hDuration m), budget sigma hsigma m ?_⟩
  intro a ha
  filter_upwards [ceiling a ha] with k hk
  intro z hz
  exact (hk z hz).trans (mul_le_mul_of_nonneg_right
    (by linarith : 2 * K ≤ 2 * ((m : ℝ) + 1)) (V.base_scalar_pos (sigma k)).le)


theorem terminalSource_common_maximal_selected_limit
    (P : M47Predecessors.{u}) (V : GeneralizedBlowupSequence.{u})
    {delta : ℝ} (hdelta : 0 < delta) (hslab : TerminalCommonIntervalSlab V delta)
    (hcompact : BlowupBaseBallsCompact V)
    (hvolume : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale k)) ^ 3) ≤
        calibratedMetricVolume ((V.flow k).metric (V.base k).1) (V.baseBall k rho)) :
    ∃ (sigma : ℕ → ℕ) (hsigma : StrictMono sigma),
      let D := terminalCommonInterval_reindex V sigma hsigma
      TerminalCommonIntervalDecided D ∧
        M30GeometricLongControls D (terminalCommonIntervalHorizon D) ∧
        (∀ (rho : ℕ → ℕ) (hrho : StrictMono rho) (Horizon : ℝ≥0∞),
          M30GeometricLongControls (terminalCommonInterval_reindex D rho hrho) Horizon →
          Horizon ≤ terminalCommonIntervalHorizon D) ∧
        Nonempty (GeneralizedBlowupConvergence D
          (blowupBackwardInterval (terminalCommonIntervalHorizon D))) := by
  obtain ⟨sigma, hsigma, hdec⟩ := terminalCommonInterval_exists_decided V
  let D := terminalCommonInterval_reindex V sigma hsigma
  have hslab' : TerminalCommonIntervalSlab D delta :=
    terminalCommonInterval_slab_reindex hslab hsigma
  have hcompact' : BlowupBaseBallsCompact D :=
    terminalCommonInterval_reindex_compact hcompact hsigma
  have hvolume' : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (D.scale k)) ^ 3) ≤
        calibratedMetricVolume ((D.flow k).metric (D.base k).1) (D.baseBall k rho) := by
    obtain ⟨rho, v, hrho, hv, hc⟩ := hvolume
    exact ⟨rho, v, hrho, hv, hsigma.tendsto_atTop.eventually hc⟩
  have controls := terminalCommonInterval_maximalControls D hdelta hslab' hcompact' hvolume'
  exact ⟨sigma, hsigma, hdec, controls,
    fun _ hrho _ C => terminalCommonInterval_maximal hdec hrho C,
    P.geometric_limits D (terminalCommonIntervalHorizon D) controls⟩

end PoincareConjecture.M47
