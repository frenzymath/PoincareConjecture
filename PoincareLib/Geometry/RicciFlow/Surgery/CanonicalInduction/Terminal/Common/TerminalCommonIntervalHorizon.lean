import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Common.TerminalCommonIntervalSlabs
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory

/-!
# The maximal controlled open-left horizon

The supremum is over durations, never over curvature bounds. Its positive
initial slab, actual compactness and actual terminal volume are upstream
outputs, not additional M47 entry premises. Source: common-interval C5.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareMT.M47

/-- The controlled horizon is defined even before its positivity is proved. -/
noncomputable def terminalCommonIntervalHorizon (V : GeneralizedBlowupSequence.{u}) :
    ℝ≥0∞ := sSup (TerminalCommonIntervalHorizons V)

/-- Each strictly smaller slab is supplied by one member of the supremum. -/
theorem terminalCommonInterval_horizon_mem (V : GeneralizedBlowupSequence.{u}) :
    terminalCommonIntervalHorizon V ∈ TerminalCommonIntervalHorizons V := by
  intro T hT hTH
  obtain ⟨H, hH, hTH'⟩ := lt_sSup_iff.mp hTH
  exact hH T hT hTH'

/-- The actual first common slab makes the maximal horizon positive. -/
theorem terminalCommonInterval_horizon_pos
    {V : GeneralizedBlowupSequence.{u}} {delta : ℝ} (hdelta : 0 < delta)
    (hslab : TerminalCommonIntervalSlab V delta) :
    0 < terminalCommonIntervalHorizon V := by
  have hmem : ENNReal.ofReal delta ∈ TerminalCommonIntervalHorizons V := by
    intro T _hT hTd
    exact terminalCommonInterval_slab_mono hslab
      ((ENNReal.ofReal_lt_ofReal_iff hdelta).mp hTd).le
  exact (ENNReal.ofReal_pos.mpr hdelta).trans_le (le_sSup hmem)

/-- Countable decision makes the entire maximal horizon refinement-stable. -/
theorem terminalCommonInterval_horizon_reindex
    {V : GeneralizedBlowupSequence.{u}} (hdec : TerminalCommonIntervalDecided V)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) :
    terminalCommonIntervalHorizon (terminalCommonInterval_reindex V sigma hsigma) =
      terminalCommonIntervalHorizon V := by
  unfold terminalCommonIntervalHorizon
  rw [terminalCommonInterval_horizons_reindex hdec hsigma]

/-- Assemble the literal M30 controls from the actual three upstream outputs. -/
theorem terminalCommonInterval_maximalControls
    (V : GeneralizedBlowupSequence.{u}) {delta : ℝ} (hdelta : 0 < delta)
    (hslab : TerminalCommonIntervalSlab V delta)
    (hcompact : BlowupBaseBallsCompact V)
    (hvolume : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale k)) ^ 3) ≤
        calibratedMetricVolume ((V.flow k).metric (V.base k).1) (V.baseBall k rho)) :
    M30GeometricLongControls V (terminalCommonIntervalHorizon V) := {
  horizon_pos := terminalCommonInterval_horizon_pos hdelta hslab
  balls_compact := hcompact
  terminal_volume := hvolume
  cylinders := terminalCommonInterval_horizon_mem V }

/-- Reindex every M30 field on the same actual selected family. -/
theorem terminalCommonInterval_reindexControls
    {V : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
    (C : M30GeometricLongControls V H)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) :
    M30GeometricLongControls (terminalCommonInterval_reindex V sigma hsigma) H := {
  horizon_pos := C.horizon_pos
  balls_compact := terminalCommonInterval_reindex_compact C.balls_compact hsigma
  terminal_volume := by
    obtain ⟨rho, v, hrho, hv, hc⟩ := C.terminal_volume
    exact ⟨rho, v, hrho, hv, hsigma.tendsto_atTop.eventually hc⟩
  cylinders := fun T hT hTH =>
    terminalCommonInterval_slab_reindex (C.cylinders T hT hTH) hsigma }

/-- No subsequent strict selection can have a larger controlled horizon. -/
theorem terminalCommonInterval_maximal
    {V : GeneralizedBlowupSequence.{u}} (hdec : TerminalCommonIntervalDecided V)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) {H : ℝ≥0∞}
    (C : M30GeometricLongControls (terminalCommonInterval_reindex V sigma hsigma) H) :
    H ≤ terminalCommonIntervalHorizon V := by
  have hmem : H ∈ TerminalCommonIntervalHorizons
      (terminalCommonInterval_reindex V sigma hsigma) := C.cylinders
  rw [terminalCommonInterval_horizons_reindex hdec hsigma] at hmem
  exact le_sSup hmem

/-- Apply the literal M30 field once, after constructing all three controls.
The selected limit, maps and metric jets survive composition unchanged. -/
theorem terminalCommonInterval_extract
    (P : M47Predecessors.{u}) (V : GeneralizedBlowupSequence.{u})
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) {delta : ℝ} (hdelta : 0 < delta)
    (hslab : TerminalCommonIntervalSlab
      (terminalCommonInterval_reindex V sigma hsigma) delta)
    (hcompact : BlowupBaseBallsCompact (terminalCommonInterval_reindex V sigma hsigma))
    (hvolume : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale (sigma k))) ^ 3) ≤
        calibratedMetricVolume ((V.flow (sigma k)).metric (V.base (sigma k)).1)
          (V.baseBall (sigma k) rho)) :
    Nonempty (GeneralizedBlowupConvergence V (blowupBackwardInterval
      (terminalCommonIntervalHorizon (terminalCommonInterval_reindex V sigma hsigma)))) := by
  let D := terminalCommonInterval_reindex V sigma hsigma
  let C := terminalCommonInterval_maximalControls D hdelta hslab hcompact hvolume
  obtain ⟨G⟩ := P.geometric_limits D (terminalCommonIntervalHorizon D) C
  exact ⟨terminalCommonInterval_compSubsequence hsigma G⟩

/-- Decide the actual tests, construct the maximal controls, and extract one
limit. The three geometric inputs are the prior C3, compactness and N7 outputs. -/
theorem terminalCommonInterval_select_and_extract
    (P : M47Predecessors.{u}) (V : GeneralizedBlowupSequence.{u})
    {delta : ℝ} (hdelta : 0 < delta) (hslab : TerminalCommonIntervalSlab V delta)
    (hcompact : BlowupBaseBallsCompact V)
    (hvolume : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale k)) ^ 3) ≤
        calibratedMetricVolume ((V.flow k).metric (V.base k).1) (V.baseBall k rho)) :
    ∃ (sigma : ℕ → ℕ) (hsigma : StrictMono sigma),
      TerminalCommonIntervalDecided (terminalCommonInterval_reindex V sigma hsigma) ∧
      0 < terminalCommonIntervalHorizon (terminalCommonInterval_reindex V sigma hsigma) ∧
      (∀ (rho : ℕ → ℕ) (hrho : StrictMono rho) (H : ℝ≥0∞),
        M30GeometricLongControls (terminalCommonInterval_reindex
          (terminalCommonInterval_reindex V sigma hsigma) rho hrho) H →
        H ≤ terminalCommonIntervalHorizon (terminalCommonInterval_reindex V sigma hsigma)) ∧
      Nonempty (GeneralizedBlowupConvergence V (blowupBackwardInterval
        (terminalCommonIntervalHorizon (terminalCommonInterval_reindex V sigma hsigma)))) := by
  obtain ⟨sigma, hsigma, hdec⟩ := terminalCommonInterval_exists_decided V
  have hslab' := terminalCommonInterval_slab_reindex hslab hsigma
  have hcompact' := terminalCommonInterval_reindex_compact hcompact hsigma
  have hvolume' : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale (sigma k))) ^ 3) ≤
        calibratedMetricVolume ((V.flow (sigma k)).metric (V.base (sigma k)).1)
          (V.baseBall (sigma k) rho) := by
    obtain ⟨rho, v, hrho, hv, hc⟩ := hvolume
    exact ⟨rho, v, hrho, hv, hsigma.tendsto_atTop.eventually hc⟩
  exact ⟨sigma, hsigma, hdec, terminalCommonInterval_horizon_pos hdelta hslab',
    fun _ hrho _ C => terminalCommonInterval_maximal hdec hrho C,
    terminalCommonInterval_extract P V hsigma hdelta hslab' hcompact' hvolume'⟩

end PoincareMT.M47
