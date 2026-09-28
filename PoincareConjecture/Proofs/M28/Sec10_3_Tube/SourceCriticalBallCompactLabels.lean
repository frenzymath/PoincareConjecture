import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallGraphLabels
import PoincareConjecture.Proofs.M28.Mathlib.CompactComponentLabels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 2400000 in

theorem eventually_initial_graph_labels_on_compact (H : CounterexampleNeckFamily E)
    (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j : ℕ), L.carrier ⊆ G.exhaustion j →
      ∀ {sigma : ℕ → ℕ}, StrictMono sigma →
      ∀ (f : ℕ → UnitTwoSphere → ℝ),
      (∀ k, Continuous (f k) ∧ (∀ q, |f k q| < epsilon⁻¹ / 32) ∧
        (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
          W.high_index G (sigma k)) '' L.central_sphere =
            range (fun q : UnitTwoSphere =>
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                (q, f k q))) →
      ∀ {U K : Set G.limitCarrier.carrier}, IsOpen U → IsConnected U →
        U ⊆ L.central_sphereᶜ → IsCompact K → K ⊆ U →
        ∀ {a : G.limitCarrier.carrier}, a ∈ U →
          ∀ᶠ k in atTop, ∀ x ∈ K,
            (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
              W.high_index G (sigma k) x ∈
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k) ↔
            H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
              W.high_index G (sigma k) a ∈
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.secondCountable
  let : LocallyConnectedSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) G.limitCarrier.carrier
  let : LocallyCompactSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) G.limitCarrier.carrier
  intro L j hstage sigma hsigma f hf U K hUopen hU hUS hK hKU a ha
  let e := fun k => H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
    W.high_index G k
  let T := fun k => (W.tube (W.high_index (G.subsequence k))).tube.carrier
  have hesource (k : ℕ) : (e k).source = G.exhaustion k :=
    H.regularRawStageDiffeomorph_source _ _ _ _ _ k
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  have htail := hK.eventually_component_mem_iff G.exhaustion G.exhaustion_open
    hmono G.exhaustion_covers (L.central_sphere_subset.trans hstage) (fun k => e k) T
    (fun k => by simpa only [hesource] using (e k).contMDiffOn.continuousOn)
    (fun k => by simpa only [hesource] using (e k).toPartialEquiv.injOn)
    (fun k x _ => (G.embedding k x).val.property) hKU hUopen hU hUS ha
  filter_upwards [hsigma.tendsto_atTop.eventually htail] with k hk
  apply hk
  rw [(hf k).2.2]
  exact ((W.tube (W.high_index (G.subsequence (sigma k)))).initial_graph_negative_region
    (f k) (hf k).1 (hf k).2.1).2.2

end PoincareConjecture.M28.CounterexampleNeckFamily
