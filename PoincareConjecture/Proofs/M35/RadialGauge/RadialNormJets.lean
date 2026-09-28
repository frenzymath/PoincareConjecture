import PoincareConjecture.Proofs.M35.Mathlib.SmoothEvenRadial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem norm_unit_sphere_jet_bounds (k : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ k, ∀ x : E, ‖x‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun y : E => ‖y‖) x‖ ≤ D := by
  classical
  let S := ({0} : Set E)ᶜ
  have hS : IsOpen S := isClosed_singleton.isOpen_compl
  have hn : ContDiffOn ℝ ∞ (fun y : E => ‖y‖) S := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa only [S, mem_compl_iff, mem_singleton_iff] using hx
    exact (contDiffAt_id.norm ℝ hx0).contDiffWithinAt
  have hsphere : Metric.sphere (0 : E) 1 ⊆ S := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hx0 : x ≠ 0 := by intro hz; simp only [hz, norm_zero, zero_ne_one] at hxnorm
    exact hx0
  have hb (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E, ‖x‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun y : E => ‖y‖) x‖ ≤ B := by
    have hc := hn.continuousOn_iteratedFDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i) hS.uniqueDiffOn
    have hc' : ContinuousOn (iteratedFDeriv ℝ i (fun y : E => ‖y‖)) S := by
      apply hc.congr
      intro x hx
      exact (iteratedFDerivWithin_of_isOpen i hS hx).symm
    obtain ⟨B, hB⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
      (hc'.mono hsphere)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro x hx
    exact (hB x (by simpa only [Metric.mem_sphere, dist_zero_right] using hx)).trans
      (le_max_left _ _)
  choose B hB0 hB using hb
  let D := 1 + ∑ i ∈ Finset.range (k + 1), B i
  have hD : 1 ≤ D := by
    have := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun i _ => hB0 i)
    dsimp only [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro i hi x hx
  have hh := Finset.single_le_sum (f := B) (fun i _ => hB0 i)
    (show i ∈ Finset.range (k + 1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hi)
  exact (hB i x hx).trans (by dsimp only [D]; linarith)

end PoincareConjecture.M35.RadialGauge
