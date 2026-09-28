import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ClosedStripSliceJets
import Mathlib.Algebra.Field.Periodic












set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff

namespace PoincareConjecture.M64.RampTransport

local notation "S" => Set.prod (univ : Set ℝ) (Icc (0 : ℝ) 1)





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

end PoincareConjecture.M64.RampTransport
