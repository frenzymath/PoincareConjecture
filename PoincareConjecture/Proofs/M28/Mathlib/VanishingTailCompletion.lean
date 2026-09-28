import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u v

namespace UniformSpace.Completion

variable {X : Type u} [MetricSpace X]

theorem tendsto_of_uniform_height_tail
    {h : X → ℝ} {E : Completion X}
    (htail : ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, a < 1 ∧
      ∀ x : X, a < h x → dist (x : Completion X) E < eta)
    {ι : Type v} {l : Filter ι} {q : ι → X}
    (hq : Tendsto (fun i => h (q i)) l (𝓝 1)) :
    Tendsto (fun i => (q i : Completion X)) l (𝓝 E) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨a, ha, hclose⟩ := htail eta heta
  exact (hq.eventually (lt_mem_nhds ha)).mono fun i hi => hclose (q i) hi

theorem exists_unique_of_vanishing_height_tails
    (h : X → ℝ) (hcontinuous : Continuous h)
    (hbelow : ∀ x : X, h x < 1)
    (hcofinal : ∀ a : ℝ, a < 1 → ∃ x : X, a < h x)
    (hshrink : ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, a < 1 ∧
      ∀ x y : X, a < h x → a < h y → dist x y < eta) :
    ∃! E : Completion X,
      E ∉ Set.range ((↑) : X → Completion X) ∧
      (∀ eta : ℝ, 0 < eta → ∃ a : ℝ, a < 1 ∧
        ∀ x : X, a < h x → dist (x : Completion X) E < eta) ∧
      (∀ q : ℕ → X, Tendsto (fun n => h (q n)) atTop (𝓝 1) →
        Tendsto (fun n => (q n : Completion X)) atTop (𝓝 E)) ∧
      Continuous (fun x : X => dist (x : Completion X) E) ∧
      (∀ x : X, 0 < dist (x : Completion X) E) ∧
      ∀ x y : X,
        |dist (x : Completion X) E - dist (y : Completion X) E| ≤ dist x y ∧
        dist x y ≤ dist (x : Completion X) E + dist (y : Completion X) E := by
  classical
  have hlevel (n : ℕ) : 1 - 1 / ((n : ℝ) + 1) < 1 := by
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose q hq using fun n : ℕ =>
    hcofinal (1 - 1 / ((n : ℝ) + 1)) (hlevel n)
  have hlevels : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hheight : Tendsto (fun n => h (q n)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlevels tendsto_const_nhds
      (fun n => (hq n).le) (fun n => (hbelow (q n)).le)
  have hcauchy : CauchySeq (fun n => (q n : Completion X)) := by
    apply Metric.cauchySeq_iff.mpr
    intro eta heta
    obtain ⟨a, ha, hpair⟩ := hshrink eta heta
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hheight.eventually (lt_mem_nhds ha))
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [Completion.dist_eq] using hpair (q m) (q n) (hN m hm) (hN n hn)
  obtain ⟨E, hE⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htail : ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, a < 1 ∧
      ∀ x : X, a < h x → dist (x : Completion X) E < eta := by
    intro eta heta
    obtain ⟨a, ha, hpair⟩ := hshrink (eta / 2) (half_pos heta)
    obtain ⟨n, hn⟩ := ((hheight.eventually (lt_mem_nhds ha)).and
      (Metric.tendsto_nhds.mp hE (eta / 2) (half_pos heta))).exists
    refine ⟨a, ha, fun x hx => ?_⟩
    have hxn : dist (x : Completion X) (q n : Completion X) < eta / 2 := by
      simpa only [Completion.dist_eq] using hpair x (q n) hx hn.1
    have htriangle := dist_triangle (x : Completion X) (q n : Completion X) E
    linarith [hn.2]
  have houtside : E ∉ Set.range ((↑) : X → Completion X) := by
    rintro ⟨x, hx⟩
    have hqx : Tendsto q atTop (𝓝 x) := by
      apply ((Completion.isUniformEmbedding_coe X).isEmbedding.tendsto_nhds_iff).mpr
      change Tendsto (fun n => (q n : Completion X)) atTop (𝓝 (x : Completion X))
      rw [hx]
      exact hE
    have hheightx := hcontinuous.continuousAt.tendsto.comp hqx
    exact (hbelow x).ne (tendsto_nhds_unique hheightx hheight)
  have hsequences : ∀ s : ℕ → X,
      Tendsto (fun n => h (s n)) atTop (𝓝 1) →
      Tendsto (fun n => (s n : Completion X)) atTop (𝓝 E) := by
    intro s hs
    exact tendsto_of_uniform_height_tail htail hs
  refine ⟨E, ⟨houtside, htail, hsequences, ?_, ?_, ?_⟩, ?_⟩
  · exact (Completion.continuous_coe X).dist continuous_const
  · intro x
    exact dist_pos.mpr fun hx => houtside ⟨x, hx⟩
  · intro x y
    constructor
    · simpa only [Completion.dist_eq] using
        abs_dist_sub_le (x : Completion X) (y : Completion X) E
    · simpa only [Completion.dist_eq] using
        dist_triangle_right (x : Completion X) (y : Completion X) E
  · intro F hF
    exact tendsto_nhds_unique (hF.2.2.1 q hheight) hE

end UniformSpace.Completion
