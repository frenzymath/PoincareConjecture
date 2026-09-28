import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.FiniteApproximation

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open Poincare.GromovHausdorff

namespace Poincare.Alexandrov

theorem comparisonAnglePackingBound_of_pointedGHConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace} {Y : FiniteDiameterBasedMetricSpace}
    {α : ℝ} {N : ℕ}
    (hX : ∀ j, ComparisonAnglePackingBound (X j).carrier α N)
    (h : PointedGHConverges X Y) : ComparisonAnglePackingBound Y.carrier α N := by
  obtain ⟨f, hf⟩ := exists_approximating_maps_of_pointedGHConverges h
  intro k p q hq hangle
  have hnonzero (i : Fin k) : ∀ᶠ j in atTop, f j (q i) ≠ f j p := by
    have hpos : 0 < dist (q i) p := dist_pos.mpr (hq i)
    filter_upwards [(hf (q i) p).eventually_const_lt hpos] with j hj heq
    simp only [heq, dist_self, lt_self_iff_false] at hj
  have hseparated (i l : Fin k) : ∀ᶠ j in atTop, i ≠ l →
      α < comparisonAngle (dist (f j p) (f j (q i)))
        (dist (f j p) (f j (q l))) (dist (f j (q i)) (f j (q l))) := by
    by_cases hil : i = l
    · exact Eventually.of_forall (fun _ hne => (hne hil).elim)
    · have hpos (a : Fin k) : 0 < dist p (q a) := dist_pos.mpr (hq a).symm
      have ht := tendsto_comparisonAngle (hf p (q i)) (hf p (q l))
        (hf (q i) (q l)) (hpos i) (hpos l)
      filter_upwards [ht.eventually_const_lt (hangle i l hil)] with j hj _
      exact hj
  obtain ⟨j, hj, hsep⟩ := ((Filter.eventually_all.mpr hnonzero).and
    (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hseparated i))).exists
  exact hX j k (f j p) (fun i => f j (q i)) hj hsep

theorem comparisonAnglePackingBound_of_pointedGHConvergesUnbounded
    {X : ℕ → BasedMetricSpaceBundle} {Y : BasedMetricSpaceBundle}
    {α : ℝ} {N : ℕ}
    (hX : ∀ j, ComparisonAnglePackingBound (X j).carrier α N)
    (h : PointedGHConvergesUnbounded X Y) : ComparisonAnglePackingBound Y.carrier α N := by
  intro k p q hq hangle
  let r : ℝ := 1 + dist p Y.base + ∑ i : Fin k, dist (q i) Y.base
  have hsum : 0 ≤ ∑ i : Fin k, dist (q i) Y.base :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hr : 0 < r := by dsimp [r]; linarith [dist_nonneg (x := p) (y := Y.base)]
  have hpr : p ∈ Metric.ball Y.base r := by
    rw [Metric.mem_ball]
    dsimp [r]
    linarith
  have hqr (i : Fin k) : q i ∈ Metric.ball Y.base r := by
    rw [Metric.mem_ball]
    have hi := Finset.single_le_sum (fun (l : Fin k) _ =>
      show 0 ≤ dist (q l) Y.base from dist_nonneg) (Finset.mem_univ i)
    dsimp [r]
    linarith [dist_nonneg (x := p) (y := Y.base)]
  obtain ⟨δ, _, hpos, hconv⟩ := h r hr
  have hballs (j : ℕ) :
      ComparisonAnglePackingBound (ballModel (X j) (r + δ j) (hpos j)).carrier α N :=
    (hX j).of_isometry (f := Subtype.val) (Isometry.of_dist_eq (fun _ _ => rfl))
  have hlimit := comparisonAnglePackingBound_of_pointedGHConverges hballs hconv
  let p' : (ballModel Y r hr).carrier := ⟨p, hpr⟩
  let q' : Fin k → (ballModel Y r hr).carrier := fun i => ⟨q i, hqr i⟩
  have hq' (i : Fin k) : q' i ≠ p' := fun heq => hq i (congrArg Subtype.val heq)
  exact hlimit k p' q' hq' hangle

end Poincare.Alexandrov
