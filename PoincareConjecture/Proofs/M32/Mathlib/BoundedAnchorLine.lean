import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

namespace PoincareConjecture.M32

variable {X : Type*} [MetricSpace X] [ProperSpace X]

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

end PoincareConjecture.M32
