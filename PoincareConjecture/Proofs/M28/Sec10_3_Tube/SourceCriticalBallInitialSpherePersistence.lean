import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialNeck
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallForwardNeck











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in





theorem exists_retained_initial_sphere_persistence_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∀ (W : CriticalBallSourcePacket H)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ D₀ : LeviCivitaData G.limitMetric,
            ∃ j : ℕ, ∃ L : EpsilonNeck G.limitMetric,
              L.epsilon = 3 * epsilon / 2 ∧ L.center = G.base ∧
              L.scale = (4 * max C 2)⁻¹ ∧ L.connection = D₀ ∧
              L.carrier ⊆ G.exhaustion j ∧
              ∀ᶠ k in atTop, j ≤ k ∧ ∃ N : EpsilonNeck
                ((E (W.high_index (G.subsequence k) + H.shift)).flow.metric
                  (E (W.high_index (G.subsequence k) + H.shift)).time),
                N.epsilon = 2 * epsilon ∧
                N.center = ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.center ∧
                N.scale = ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.scale ∧
                N.connection =
                  ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.connection ∧
                N.carrier = (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G k) '' L.region (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ∧
                N.central_sphere = (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G k) '' L.central_sphere ∧
                ∀ z : RoundCylinderSpace, N.coordinate_map z =
                  H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                    W.high_index G k (L.coordinate_map z) := by
  obtain ⟨epsilon₀, hpos, hsmall, hinit⟩ := exists_retained_initial_neck_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  obtain ⟨j, hj⟩ := hinit H hepsilon W G D₀
  obtain ⟨k₀, _, L, hLeps, hLcenter, hLscale, hLconnection, hLstage, _⟩ := hj.exists
  have hepspos : 0 < epsilon := by linarith [L.epsilon_pos]
  have htheta : L.epsilon < 2 * epsilon := by rw [hLeps]; linarith
  have hhalf : 2 * epsilon < 1 / 2 := by linarith [hepsilon.trans hsmall]
  refine ⟨j, L, hLeps, hLcenter, hLscale, hLconnection, hLstage, ?_⟩
  exact (eventually_ge_atTop j).and
    (H.eventually_exists_regularRawStage_forward_neck W.tube W.radius W.radius_pos
      W.high_index G L j hLstage hLcenter hLscale (2 * epsilon) htheta hhalf)

end PoincareConjecture.M28.CounterexampleNeckFamily
