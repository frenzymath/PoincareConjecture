import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialRadius
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialCore
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.MetricConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in





theorem exists_retained_initial_neck_capture_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∀ (W : CriticalBallSourcePacket H)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          let i := fun k => W.high_index (G.subsequence k)
          ∃ j : ℕ, ∀ᶠ k in atTop, j ≤ k ∧
            ∃ N ∈ (H.segment (i k)).cover.necks, N.epsilon = epsilon ∧
              N.center = (H.segment (i k)).path (H.segment (i k)).lower ∧
              ∀ x ∈ N.carrier, |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4 →
                x ∈ (fun y => (G.embedding k y).val.val) '' G.exhaustion j := by
  obtain ⟨epsilon₀, hpos, hsmall, hradius⟩ :=
    exists_retained_criticalBall_large_radius_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let i := fun k => W.high_index (G.subsequence k)
  dsimp only
  have hepspos : 0 < epsilon :=
    (H.segment 0).cover_epsilon ▸ (H.segment 0).cover.epsilon_pos
  have hCpos : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hdelta : 0 < (4 * max C 2)⁻¹ * epsilon⁻¹ / 32 := by positivity
  have hlarge : (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ ≤ W.radius :=
    hradius (E := E) H hepsilon W
  have hfirst (n : ℕ) :=
    tubeCritical_contains_initial_neck (E := E) H W.tube (hepsilon.trans hsmall)
      (Acrit := W.radius) hlarge n
  choose neck hneck hepsNeck hcenterNeck hcriticalNeck using hfirst
  obtain ⟨j, hcoverage⟩ :=
    G.regular_component_coverage ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32) hdelta
  refine ⟨j, ?_⟩
  filter_upwards [hcoverage] with k hk
  let N := neck (i k)
  have hN := hneck (i k)
  have hepsN := hepsNeck (i k)
  have hcenter := hcenterNeck (i k)
  have hNcritical := hcriticalNeck (i k)
  refine ⟨hk.1, N, hN, hepsN, hcenter, ?_⟩
  intro x hx hheight
  obtain ⟨y, hy, hxy⟩ := hNcritical hx
  have hregular := H.tubeCritical_initial_neck_core_component W.tube W.radius
    W.radius_pos (i k) N hepsN hcenter hNcritical ⟨y, hy⟩
    (by simpa only [hxy] using hx) (by simpa only [hxy] using hheight)
  obtain ⟨q, hq, hqz⟩ := hk.2 hregular
  refine ⟨q, hq, ?_⟩
  exact (congrArg (fun z : H.tubeCriticalRegion W.tube W.radius (i k) => z.val.val)
    hqz).trans hxy

end PoincareConjecture.M28.CounterexampleNeckFamily
