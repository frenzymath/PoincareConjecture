import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallSourcePacket
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeLargeInitialBall









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily




theorem exists_retained_criticalBall_large_radius_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∀ W : CriticalBallSourcePacket H,
          (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ ≤ W.radius := by
  obtain ⟨epsilon₀, hpos, hsmall, hbound⟩ :=
    exists_source_tube_large_initial_bound_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W
  by_contra hnot
  have hAr : W.radius < (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ :=
    lt_of_not_ge hnot
  have hsmallRadius : ∀ᶠ j : ℕ in atTop,
      W.radius + 1 / ((j : ℝ) + 1) <
        (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ := by
    have ht : Tendsto (fun j : ℕ => W.radius + 1 / ((j : ℝ) + 1))
        atTop (𝓝 W.radius) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := W.radius)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact ht.eventually (gt_mem_nhds hAr)
  have hlarge : ∀ᶠ j : ℕ in atTop, 64 * (max C 2) ^ 2 < (j : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨j, hbj, hs, hd⟩ :=
    ((W.high_index_strictMono.tendsto_atTop.eventually (hbound H W.tube hepsilon)).and
      (hsmallRadius.and hlarge)).exists
  have hrpos : 0 < (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ :=
    W.radius_pos.trans hAr
  have hball : W.high_point j ∈ (H.tubeMetric W.tube (W.high_index j)).ball
      (H.tubeBase W.tube (W.high_index j))
      ((7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) := by
    change (H.tubeMetric W.tube (W.high_index j)).edist
      (H.tubeBase W.tube (W.high_index j)) (W.high_point j) < _
    have he := (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr
      ((W.high_radius_upper j).trans hs)
    simpa only [ENNReal.ofReal_toReal
      (H.tube_edist_ne_top W.tube (W.high_index j) _ _)] using he
  exact (not_lt_of_ge (hbj (W.high_point j) hball)) (hd.trans (W.high_scalar_lower j))

end PoincareConjecture.M28.CounterexampleNeckFamily
