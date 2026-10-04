import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Metric line limits for splitting at infinity

In a proper metric space, anchored maps whose pairwise distances tend to
the corresponding distances on the real line have an isometric limit.
The same conclusion holds for maps with vanishing distance distortion on
expanding finite windows. No continuity of the approximating maps is needed.

This is the metric compactness step in Morgan--Tian, Theorem 5.35,
printed p. 123, relevant to Kleiner--Lott, corrected 2013 journal version,
Proposition 41.13, printed p. 2678. The pairwise-distance hypothesis is an
explicit input; constructing the arcs, proving the required comparison,
and deducing a Riemannian product decomposition are separate obligations.

The ultrafilter argument is adapted from the pinned Axel source
`MorganTianLib/Ch09/SplittingAtInfinity/Line/Compactness.lean`.
See `notes/ricci-flow/ancient-volume-line-limit.md` for provenance.
-/

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

namespace Poincare.AncientVolume.Splitting

variable {M : Type*} [MetricSpace M] [ProperSpace M]

/-- Anchored maps with asymptotically correct pairwise distances produce a
metric line through the anchor, with pointwise convergence along one fixed
ultrafilter. -/
theorem exists_isometric_line_of_dist_tendsto
    {p : M} {arc : ℕ → ℝ → M}
    (hbase : ∀ i, arc i 0 = p)
    (hdist : ∀ s t : ℝ,
      Tendsto (fun i => dist (arc i s) (arc i t)) atTop (𝓝 |s - t|)) :
    ∃ gamma : ℝ → M, Isometry gamma ∧ gamma 0 = p ∧
      ∀ t : ℝ, Tendsto (fun i => arc i t)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)) := by
  classical
  have hbounded : ∀ t : ℝ, ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
      arc i t ∈ closedBall p (|t| + 1) := by
    intro t
    have hlim : Tendsto (fun i => dist (arc i t) p) atTop (𝓝 |t|) := by
      simpa only [hbase, sub_zero] using hdist t 0
    have hbound := hlim.eventually (eventually_lt_nhds (by linarith : |t| < |t| + 1))
    filter_upwards [hbound.filter_mono Nat.hyperfilter_le_atTop] with i hi
    exact hi.le
  have hlimit : ∀ t : ℝ, ∃ q : M,
      Tendsto (fun i => arc i t) (hyperfilter ℕ : Filter ℕ) (𝓝 q) := by
    intro t
    obtain ⟨q, _, hq⟩ := (isCompact_closedBall p (|t| + 1)).ultrafilter_le_nhds'
      ((hyperfilter ℕ).map fun i => arc i t) (hbounded t)
    rw [Ultrafilter.coe_map] at hq
    exact ⟨q, hq⟩
  choose gamma hgamma using hlimit
  refine ⟨gamma, ?_, ?_, hgamma⟩
  · apply Isometry.of_dist_eq
    intro s t
    rw [Real.dist_eq]
    exact tendsto_nhds_unique ((hgamma s).dist (hgamma t))
      ((hdist s t).mono_left Nat.hyperfilter_le_atTop)
  · have hconst : Tendsto (fun i => arc i 0)
        (hyperfilter ℕ : Filter ℕ) (𝓝 p) := by
      simpa only [hbase] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p)
          (hyperfilter ℕ : Filter ℕ) (𝓝 p))
    exact tendsto_nhds_unique (hgamma 0) hconst

/-- Vanishing distance distortion on expanding two-sided windows suffices
to construct a metric line. Values outside each window are unrestricted. -/
theorem exists_isometric_line_of_expanding_windows
    {p : M} {arc : ℕ → ℝ → M} {radius error : ℕ → ℝ}
    (hbase : ∀ i, arc i 0 = p)
    (hradius : Tendsto radius atTop atTop)
    (herror : Tendsto error atTop (𝓝 0))
    (hdist : ∀ i s t, |s| ≤ radius i → |t| ≤ radius i →
      |dist (arc i s) (arc i t) - (|s - t|)| ≤ error i) :
    ∃ gamma : ℝ → M, Isometry gamma ∧ gamma 0 = p ∧
      ∀ t : ℝ, Tendsto (fun i => arc i t)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)) := by
  apply exists_isometric_line_of_dist_tendsto hbase
  intro s t
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ herror
  filter_upwards [hradius.eventually_ge_atTop |s|, hradius.eventually_ge_atTop |t|]
    with i hs ht
  simpa only [Real.dist_eq] using hdist i s t hs ht

/-- Unit-speed minimizing arcs on expanding two-sided windows produce a
metric line through their common anchor. -/
theorem exists_isometric_line_of_minimizing_windows
    {p : M} {arc : ℕ → ℝ → M} {radius : ℕ → ℝ}
    (hbase : ∀ i, arc i 0 = p)
    (hradius : Tendsto radius atTop atTop)
    (hdist : ∀ i s t, |s| ≤ radius i → |t| ≤ radius i →
      dist (arc i s) (arc i t) = |s - t|) :
    ∃ gamma : ℝ → M, Isometry gamma ∧ gamma 0 = p ∧
      ∀ t : ℝ, Tendsto (fun i => arc i t)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (gamma t)) := by
  apply exists_isometric_line_of_expanding_windows hbase hradius
    (error := fun _ => 0) tendsto_const_nhds
  intro i s t hs ht
  simp only [hdist i s t hs ht, sub_self, abs_zero, le_refl]

end Poincare.AncientVolume.Splitting
