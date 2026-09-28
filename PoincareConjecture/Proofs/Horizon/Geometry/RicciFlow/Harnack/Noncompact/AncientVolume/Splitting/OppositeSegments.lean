import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Poincare.AncientVolume.Splitting

private theorem tendsto_distance_add_of_squared_comparison
    {s t : ℝ} {d c : ℕ → ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : ∀ i, 0 ≤ d i) (hc : Tendsto c atTop (𝓝 (-1)))
    (hlower : ∀ᶠ i in atTop, s ^ 2 + t ^ 2 - 2 * s * t * c i ≤ d i ^ 2)
    (hupper : ∀ᶠ i in atTop, d i ≤ s + t) :
    Tendsto d atTop (𝓝 (s + t)) := by
  have hlow : Tendsto (fun i => s ^ 2 + t ^ 2 - 2 * s * t * c i)
      atTop (𝓝 ((s + t) ^ 2)) := by
    have h := (tendsto_const_nhds (x := s ^ 2 + t ^ 2)).sub
      ((tendsto_const_nhds (x := 2 * s * t)).mul hc)
    convert h using 1
    congr 1
    ring
  have hupp : ∀ᶠ i in atTop, d i ^ 2 ≤ (s + t) ^ 2 := by
    filter_upwards [hupper] with i hi
    exact pow_le_pow_left₀ (hd i) hi 2
  have hsq : Tendsto (fun i => d i ^ 2) atTop (𝓝 ((s + t) ^ 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds hlower hupp
  simpa only [Real.sqrt_sq (hd _), Real.sqrt_sq (add_nonneg hs ht)] using hsq.sqrt

noncomputable def segmentComparisonCosine {X : Type*} [MetricSpace X]
    (minus plus : ℝ → X) (a b : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 - dist (minus a) (plus b) ^ 2) / (2 * a * b)

theorem exists_two_sided_arcs_of_minimizing_segments
    {X : ℕ → Type*} [∀ i, MetricSpace (X i)]
    (p : ∀ i, X i) (minus plus : ∀ i, ℝ → X i) {a b : ℕ → ℝ}
    (hminus0 : ∀ i, minus i 0 = p i) (hplus0 : ∀ i, plus i 0 = p i)
    (hminus : ∀ i, ∀ s ∈ Icc (0 : ℝ) (a i), ∀ t ∈ Icc (0 : ℝ) (a i),
      dist (minus i s) (minus i t) = |s - t|)
    (hplus : ∀ i, ∀ s ∈ Icc (0 : ℝ) (b i), ∀ t ∈ Icc (0 : ℝ) (b i),
      dist (plus i s) (plus i t) = |s - t|)
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hangle : Tendsto (fun i => segmentComparisonCosine (minus i) (plus i) (a i) (b i))
      atTop (𝓝 (-1)))
    (hcomparison : ∀ i, ∀ s ∈ Icc (0 : ℝ) (a i), ∀ t ∈ Icc (0 : ℝ) (b i),
      s ^ 2 + t ^ 2 - 2 * s * t *
          segmentComparisonCosine (minus i) (plus i) (a i) (b i) ≤
        dist (minus i s) (plus i t) ^ 2) :
    ∃ arc : ∀ i, ℝ → X i,
      (∀ i, arc i 0 = p i) ∧
      (∀ i t, 0 ≤ t → arc i t = plus i t) ∧
      (∀ i t, 0 ≤ t → arc i (-t) = minus i t) ∧
      ∀ s t : ℝ, Tendsto (fun i => dist (arc i s) (arc i t)) atTop (𝓝 |s - t|) := by
  have hcross : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      Tendsto (fun i => dist (minus i s) (plus i t)) atTop (𝓝 (s + t)) := by
    intro s t hs ht
    apply tendsto_distance_add_of_squared_comparison hs ht (fun _ => dist_nonneg) hangle
    · filter_upwards [ha.eventually_ge_atTop s, hb.eventually_ge_atTop t] with i hsi hti
      exact hcomparison i s ⟨hs, hsi⟩ t ⟨ht, hti⟩
    · filter_upwards [ha.eventually_ge_atTop s, hb.eventually_ge_atTop t] with i hsi hti
      have hleft : dist (minus i s) (p i) = s := by
        rw [← hminus0 i, hminus i s ⟨hs, hsi⟩ 0 ⟨le_rfl, hs.trans hsi⟩,
          sub_zero, abs_of_nonneg hs]
      have hright : dist (p i) (plus i t) = t := by
        rw [← hplus0 i, hplus i 0 ⟨le_rfl, ht.trans hti⟩ t ⟨ht, hti⟩,
          zero_sub, abs_neg, abs_of_nonneg ht]
      simpa only [hleft, hright] using dist_triangle (minus i s) (p i) (plus i t)
  let arc : ∀ i, ℝ → X i := fun i t => if 0 ≤ t then plus i t else minus i (-t)
  have hpos (i : ℕ) (t : ℝ) (ht : 0 ≤ t) : arc i t = plus i t := by simp [arc, ht]
  have hneg (i : ℕ) (t : ℝ) (ht : 0 ≤ t) : arc i (-t) = minus i t := by
    rcases eq_or_lt_of_le ht with rfl | ht
    · simp [arc, hplus0, hminus0]
    · simp [arc, show ¬0 ≤ -t by linarith]
  refine ⟨arc, (fun i => by simp [arc, hplus0]), hpos, hneg, ?_⟩
  intro s t
  rcases le_or_gt 0 s with hs | hs
  · rcases le_or_gt 0 t with ht | ht
    · apply tendsto_const_nhds.congr'
      filter_upwards [hb.eventually_ge_atTop s, hb.eventually_ge_atTop t] with i hsi hti
      rw [hpos i s hs, hpos i t ht, hplus i s ⟨hs, hsi⟩ t ⟨ht, hti⟩]
    · have ht' : 0 ≤ -t := by linarith
      have h := hcross (-t) s ht' hs
      convert h using 1
      · funext i
        rw [hpos i s hs, show arc i t = minus i (-t) from by simpa using hneg i (-t) ht',
          dist_comm]
      · rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
        congr 1
        ring
  · have hs' : 0 ≤ -s := by linarith
    rcases le_or_gt 0 t with ht | ht
    · have h := hcross (-s) t hs' ht
      convert h using 1
      · funext i
        rw [hpos i t ht, show arc i s = minus i (-s) from by simpa using hneg i (-s) hs']
      · rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
        congr 1
        ring
    · have ht' : 0 ≤ -t := by linarith
      apply tendsto_const_nhds.congr'
      filter_upwards [ha.eventually_ge_atTop (-s), ha.eventually_ge_atTop (-t)] with i hsi hti
      rw [show arc i s = minus i (-s) from by simpa using hneg i (-s) hs',
        show arc i t = minus i (-t) from by simpa using hneg i (-t) ht',
        hminus i (-s) ⟨hs', hsi⟩ (-t) ⟨ht', hti⟩,
        show -s - -t = -(s - t) by ring, abs_neg]

end Poincare.AncientVolume.Splitting
