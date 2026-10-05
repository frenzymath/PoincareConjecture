import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Closed.StripSliceJets
import Mathlib.Algebra.Field.Periodic

/-!
# Uniform convergence of actual periodic strip jets

Joint continuity on one compact period rectangle and literal periodicity
give a common radial tolerance at every angular parameter. Source:
MT2007 Lemma 19.31, pp. 464-466; ramp transport trimming derivation.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff

namespace PoincareMT.M64.RampTransport

local notation "S" => Set.prod (univ : Set ℝ) (Icc (0 : ℝ) 1)

/-- Every continuous periodic strip family is uniformly close to a fixed slice when the
radial parameters are sufficiently close. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem exists_periodic_strip_uniform_tolerance
    {Z : Type*} [MetricSpace Z] {f : ℝ × ℝ → Z}
    (hf : ContinuousOn f S) {period : ℝ} (hperiod : 0 < period)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1, Function.Periodic (fun x => f (x, s)) period)
    {s0 : ℝ} (hs0 : s0 ∈ Icc (0 : ℝ) 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc (0 : ℝ) 1, |s - s0| < delta →
      ∀ x, dist (f (x, s)) (f (x, s0)) < epsilon := by
  have hK : IsCompact (Icc (0 : ℝ) period ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont := hf.mono (show Icc (0 : ℝ) period ×ˢ Icc (0 : ℝ) 1 ⊆ S from
    fun _ hp => ⟨mem_univ _, hp.2⟩)
  obtain ⟨delta, hdelta, hnear⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hcont) epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hdist x
  have herrorPeriod : Function.Periodic
      (fun y => dist (f (y, s)) (f (y, s0))) period := by
    intro y
    exact congrArg₂ dist (hp s hs y) (hp s0 hs0 y)
  obtain ⟨y, hy, hxy⟩ := herrorPeriod.exists_mem_Ico₀ hperiod x
  rw [hxy]
  have hydom : y ∈ Icc (0 : ℝ) period := ⟨hy.1, hy.2.le⟩
  apply hnear (y, s) ⟨hydom, hs⟩ (y, s0) ⟨hydom, hs0⟩
  simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
    max_eq_right (abs_nonneg (s - s0))] using hdist

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Periodicity of an actual C2 slice extends to its first two derivatives.
Source: MT Lemma 19.31, pp. 464-466; horizontal-jet trimming derivation. -/
theorem horizontalSliceJet_periodic {f : ℝ × ℝ → W}
    (hf : ContDiffOn ℝ 2 f S) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {period : ℝ} (hp : Function.Periodic (fun x => f (x, s)) period) :
    Function.Periodic (fun x => horizontalSliceJet f (x, s)) period := by
  have hc := closedStrip_slice_contDiff hf hs
  have hc1 : ContDiff ℝ 1 (deriv (fun x => f (x, s))) := hc.deriv' (n := 1)
  have hp1 := hp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hp2 := hp1.deriv_of_differentiable (hc1.differentiable (by norm_num))
  intro x
  simp only [horizontalSliceJet, hp x, hp1 x, hp2 x]

/-- Within C2 regularity produces uniform convergence of all three actual horizontal jets,
including convergence to each radial boundary. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem exists_closedStrip_jet_tolerance {f : ℝ × ℝ → W}
    (hf : ContDiffOn ℝ 2 f S) {period : ℝ} (hperiod : 0 < period)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1, Function.Periodic (fun x => f (x, s)) period)
    {s0 : ℝ} (hs0 : s0 ∈ Icc (0 : ℝ) 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc (0 : ℝ) 1, |s - s0| < delta → ∀ x,
      ‖f (x, s) - f (x, s0)‖ < epsilon ∧
      ‖deriv (fun y => f (y, s)) x - deriv (fun y => f (y, s0)) x‖ < epsilon ∧
      ‖deriv (deriv (fun y => f (y, s))) x -
        deriv (deriv (fun y => f (y, s0))) x‖ < epsilon := by
  obtain ⟨delta, hdelta, hnear⟩ := exists_periodic_strip_uniform_tolerance
    (horizontalSliceJet_continuousOn hf) hperiod
    (fun s hs => horizontalSliceJet_periodic hf hs (hp s hs)) hs0 hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hdist x
  have h := hnear s hs hdist x
  rw [dist_eq_norm] at h
  change max ‖f (x, s) - f (x, s0)‖
    (max ‖deriv (fun y => f (y, s)) x - deriv (fun y => f (y, s0)) x‖
      ‖deriv (deriv (fun y => f (y, s))) x -
        deriv (deriv (fun y => f (y, s0))) x‖) < epsilon at h
  exact ⟨(max_lt_iff.mp h).1, (max_lt_iff.mp (max_lt_iff.mp h).2).1,
    (max_lt_iff.mp (max_lt_iff.mp h).2).2⟩

end PoincareMT.M64.RampTransport
