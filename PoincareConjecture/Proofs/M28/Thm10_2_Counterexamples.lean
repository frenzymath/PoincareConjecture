import PoincareConjecture.Statements.M28BoundedDistance
import Mathlib.Tactic










set_option autoImplicit false

universe u

namespace PoincareConjecture.M28

open Filter



structure SameTimeCounterexample (epsilon C A D₀ D : ℝ) where

  flow : GeneralizedRicciFlowData.{u}

  pinched : generalizedWeakHamiltonIveyPinched flow

  time : ℝ

  time_mem : time ∈ flow.interval

  basepoint : (flow.slice time).carrier

  base_lower : D₀ ≤ flow.scalar ⟨time, basepoint⟩

  canonical : generalizedSliceStrongCanonicalNeighborhoods flow epsilon C
    (4 * flow.scalar ⟨time, basepoint⟩) time

  endpoint : (flow.slice time).carrier

  endpoint_mem : endpoint ∈ (flow.metric time).ball basepoint
    (A * flow.scalar ⟨time, basepoint⟩ ^ (-1 / 2 : ℝ))

  scalar_large : D * flow.scalar ⟨time, basepoint⟩ < flow.scalar ⟨time, endpoint⟩




theorem counterexamples_of_not_same_time {epsilon₀ : ℝ}
    (h : ¬ M28SameTimeEstimateStatement.{u} epsilon₀) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilon₀ ∧
      ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧
        Nonempty (∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)) := by
  classical
  unfold M28SameTimeEstimateStatement RepairedBoundedDistanceEstimate at h
  push Not at h
  obtain ⟨epsilon, hepsilon, hsmall, C, hC, A, hA, hbad⟩ := h
  refine ⟨epsilon, hepsilon, hsmall, C, hC, A, hA, ?_⟩
  have hex : ∀ n : ℕ, Nonempty (SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨F, hpinched, t, ht, x, hx, hcanonical, y, hy, hlarge⟩ :=
      hbad ((n : ℝ) + 1) ((n : ℝ) + 1) hn hn
    exact ⟨⟨F, hpinched, t, ht, x, hx, hcanonical, y, hy, hlarge⟩⟩
  exact ⟨fun n ↦ Classical.choice (hex n)⟩



def counterexampleBlowupSequence {epsilon C A : ℝ}
    (E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)) : GeneralizedBlowupSequence.{u} where
  flow n := (E n).flow
  base n := ⟨(E n).time, (E n).basepoint⟩
  base_scalar_pos n := lt_of_lt_of_le (by positivity) (E n).base_lower
  scalar_diverges := by
    apply tendsto_atTop_mono (fun n ↦ (E n).base_lower)
    apply tendsto_atTop_mono (fun n : ℕ ↦ ?_) tendsto_natCast_atTop_atTop
    linarith



theorem counterexample_ratio_tendsto_atTop {epsilon C A : ℝ}
    (E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)) :
    Tendsto (fun n ↦ (E n).flow.scalar ⟨(E n).time, (E n).endpoint⟩ /
      (E n).flow.scalar ⟨(E n).time, (E n).basepoint⟩) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ ↦ (n : ℝ))
  · intro n
    have hpos := (counterexampleBlowupSequence E).base_scalar_pos n
    have hlarge : (n : ℝ) + 1 <
        (E n).flow.scalar ⟨(E n).time, (E n).endpoint⟩ /
          (E n).flow.scalar ⟨(E n).time, (E n).basepoint⟩ :=
      (lt_div_iff₀ hpos).mpr (E n).scalar_large
    linarith
  · exact tendsto_natCast_atTop_atTop

end PoincareConjecture.M28
