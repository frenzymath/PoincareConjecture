import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Metric line limits with bounded moving anchors

Morgan--Tian Claim 11.34, printed pp. 288-289, and the metric compactness
step used in Theorem 2.13 and Lemma 2.14, printed pp. 28-30.

Re-derived from the read-only declarations
`Poincare.AncientVolume.Splitting.exists_isometric_line_of_dist_tendsto`,
`exists_isometric_line_of_expanding_windows`, and
`exists_isometric_line_of_minimizing_windows` in
`Harnack/Noncompact/AncientVolume/Splitting/LineLimit.lean`.
The anchors here may move in a fixed bounded ball. The same natural-number
hyperfilter retains pointwise convergence at every real parameter.

Reviewed derivation:
`proof-work/tasks/M32/derivations/claim11_34-bounded-anchor-line.md`.
Constructing the minimizing windows and their full pairwise distance
identity remains a separate geometric obligation.
-/

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

namespace PoincareMT.M32

variable {X : Type*} [MetricSpace X] [ProperSpace X]

/-- Expanding minimizing windows with uniformly bounded anchors converge
along one fixed ultrafilter to a metric line with the same anchor bound.
Source: Morgan--Tian Claim 11.34, printed pp. 288-289. -/
theorem exists_isometric_line_of_minimizing_windows_of_bounded_anchor
    {p : X} {B : ℝ} {arc : ℕ → ℝ → X} {radius : ℕ → ℝ}
    (hanchor : ∀ i, dist (arc i 0) p ≤ B)
    (hradius : Tendsto radius atTop atTop)
    (hdist : ∀ i s t, |s| ≤ radius i → |t| ≤ radius i →
      dist (arc i s) (arc i t) = |s - t|) :
    ∃ gamma : ℝ → X, Isometry gamma ∧ dist (gamma 0) p ≤ B ∧
      ∀ t : ℝ, Tendsto (fun i => arc i t)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)) := by
  classical
  have hbounded : ∀ t : ℝ, ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
      arc i t ∈ closedBall p (B + |t| + 1) := by
    intro t
    have hbound : ∀ᶠ i in atTop, arc i t ∈ closedBall p (B + |t| + 1) := by
      filter_upwards [hradius.eventually_ge_atTop |t|,
        hradius.eventually_ge_atTop |(0 : ℝ)|] with i ht hzero
      have hlen := hdist i t 0 ht hzero
      simp only [sub_zero] at hlen
      have htri := dist_triangle (arc i t) (arc i 0) p
      change dist (arc i t) p ≤ B + |t| + 1
      linarith [hanchor i]
    exact hbound.filter_mono Nat.hyperfilter_le_atTop
  have hlimit : ∀ t : ℝ, ∃ q : X,
      Tendsto (fun i => arc i t) (hyperfilter ℕ : Filter ℕ) (𝓝 q) := by
    intro t
    obtain ⟨q, _, hq⟩ := (isCompact_closedBall p (B + |t| + 1)).ultrafilter_le_nhds'
      ((hyperfilter ℕ).map fun i => arc i t) (hbounded t)
    rw [Ultrafilter.coe_map] at hq
    exact ⟨q, hq⟩
  choose gamma hgamma using hlimit
  refine ⟨gamma, ?_, ?_, hgamma⟩
  · apply Isometry.of_dist_eq
    intro s t
    have hlim : Tendsto (fun i => dist (arc i s) (arc i t)) atTop (𝓝 |s - t|) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hradius.eventually_ge_atTop |s|,
        hradius.eventually_ge_atTop |t|] with i hs ht
      exact (hdist i s t hs ht).symm
    rw [Real.dist_eq]
    exact tendsto_nhds_unique ((hgamma s).dist (hgamma t))
      (hlim.mono_left Nat.hyperfilter_le_atTop)
  · exact (isClosed_closedBall : IsClosed (closedBall p B)).mem_of_tendsto
      (hgamma 0) (Eventually.of_forall hanchor)

end PoincareMT.M32
