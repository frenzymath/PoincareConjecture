import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialSpherePersistence
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SameCenterSphereGraph











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in





theorem exists_retained_initial_sphere_graph_accuracy :
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
              ∀ᶠ k in atTop, j ≤ k ∧ ∃ f : UnitTwoSphere → ℝ,
                ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
                (∀ p, |f p| < epsilon⁻¹ / 32) ∧
                (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                  W.high_index G k) '' L.central_sphere =
                    range (fun p : UnitTwoSphere =>
                      ((W.tube (W.high_index (G.subsequence k))).list.node 0).2.coordinate_map
                        (p, f p)) := by
  obtain ⟨epsilonP, hPpos, hPsmall, hpersist⟩ :=
    exists_retained_initial_sphere_persistence_accuracy.{u}
  obtain ⟨epsilonG, hGpos, _, hgraph⟩ := exists_same_center_neck_sphere_graph_accuracy.{u}
  refine ⟨min epsilonP (epsilonG / 2), lt_min hPpos (half_pos hGpos),
    (min_le_left _ _).trans hPsmall, ?_⟩
  intro epsilon C A E H hepsilon W G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀
  obtain ⟨j, L, hLeps, hLcenter, hLscale, hLconnection, hLstage, htail⟩ :=
    hpersist H (hepsilon.trans (min_le_left _ _)) W G D₀
  have hepspos : 0 < epsilon := by linarith [L.epsilon_pos]
  have hsmall : 2 * epsilon ≤ epsilonG := by
    linarith [hepsilon.trans (min_le_right _ _)]
  refine ⟨j, L, hLeps, hLcenter, hLscale, hLconnection, hLstage, ?_⟩
  filter_upwards [htail] with k hk
  obtain ⟨hjk, N, hNeps, hcenter, hscale, _, _, hsphere, _⟩ := hk
  let N₀ := ((W.tube (W.high_index (G.subsequence k))).list.node 0).2
  have hN₀eps : N₀.epsilon = epsilon :=
    (W.tube (W.high_index (G.subsequence k))).initial_node_geometry.1
  obtain ⟨f, hf, hheight, himage⟩ := hgraph _ _ N₀.connection N₀ N
    (by rw [hN₀eps]; linarith) (by rw [hNeps]; exact hsmall) hcenter hscale
  refine ⟨hjk, f, hf, ?_, hsphere.symm.trans himage⟩
  intro p
  simpa only [hN₀eps] using hheight p

end PoincareConjecture.M28.CounterexampleNeckFamily
