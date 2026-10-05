import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Compatibility
import Mathlib.Tactic

/-!
# Counterexamples to uniform bounded distance

The contradiction setup of Morgan--Tian Theorem 10.2, printed pp. 246-247.
Failure of the actual same-time statement yields a sequence whose base
curvatures and violating curvature ratios tend to infinity. All metric
balls, flows and canonical certificates are retained from the contract.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M28

open Filter

/-- One violation of Theorem 10.2 at specified constants, with all the
original geometric hypotheses. See Morgan--Tian printed pp. 245-246. -/
structure SameTimeCounterexample (epsilon C A D₀ D : ℝ) where
  /-- The actual generalized flow. -/
  flow : GeneralizedRicciFlowData.{u}
  /-- Equation (10.1) holds on the whole original flow, in its original clock. -/
  pinched : generalizedWeakHamiltonIveyPinched flow
  /-- The tested time. -/
  time : ℝ
  /-- The tested slice is included. -/
  time_mem : time ∈ flow.interval
  /-- The base point. -/
  basepoint : (flow.slice time).carrier
  /-- The base scalar exceeds the chosen cutoff. -/
  base_lower : D₀ ≤ flow.scalar ⟨time, basepoint⟩
  /-- Canonical control is on the tested slice above four times the base scalar. -/
  canonical : generalizedSliceStrongCanonicalNeighborhoods flow epsilon C
    (4 * flow.scalar ⟨time, basepoint⟩) time
  /-- A point violating the proposed scalar bound. -/
  endpoint : (flow.slice time).carrier
  /-- Its distance is strictly within the actual normalized open ball. -/
  endpoint_mem : endpoint ∈ (flow.metric time).ball basepoint
    (A * flow.scalar ⟨time, basepoint⟩ ^ (-1 / 2 : ℝ))
  /-- Strict failure of the scalar conclusion. -/
  scalar_large : D * flow.scalar ⟨time, basepoint⟩ < flow.scalar ⟨time, endpoint⟩

/-- Negating the same-time estimate fixes epsilon, C and A before selecting
counterexamples at cutoffs and ratios `n+1`. See Morgan--Tian Theorem 10.2,
printed pp. 246-247. -/
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

/-- The counterexamples give a genuine blowup sequence with diverging
positive base scalars. See Morgan--Tian printed pp. 246-247. -/
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

/-- The violating scalar ratios also tend to infinity, because both
cutoffs were chosen to equal `n+1`. See Morgan--Tian printed p. 246. -/
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

end PoincareMT.M28
