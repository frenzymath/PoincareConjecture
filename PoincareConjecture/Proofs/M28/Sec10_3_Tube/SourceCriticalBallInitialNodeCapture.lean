import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem SourceTubeData.initial_node_geometry
    {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    {S : CounterexampleNeckSegment E} (T : SourceTubeData S) :
    (T.list.node 0).2.epsilon = epsilon ∧
      (T.list.node 0).2.carrier ⊆ T.carrierOpen := by
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have hzero : (0 : ℤ) ∈ T.list.active := by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  refine ⟨T.list.node_epsilon hzero, ?_⟩
  intro x hx
  change x ∈ T.tube.carrier
  rw [T.carrier_eq]
  have hactive : (0 : ℤ) ∈ T.chain.shape.active := by
    rw [T.shape_eq]
    exact hzero
  change x ∈ ⋃ i : {i // i ∈ T.chain.shape.active}, (T.chain.neck i.1).carrier
  refine mem_iUnion.mpr ⟨⟨0, hactive⟩, ?_⟩
  simpa only [T.neck_eq, T.list.neckOfList_eq_node] using hx

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem tubeCritical_contains_initial_node (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k))
    (hsmall : epsilon ≤ (1 / 1000 : ℝ)) {Acrit : ℝ}
    (hAcrit : (7 / 4 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹ ≤ Acrit) (k : ℕ) :
    ((T k).list.node 0).2.carrier ⊆ (Subtype.val : (T k).carrierOpen →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) ''
        (H.tubeCriticalRegion T Acrit k : Set (T k).carrierOpen) := by
  let N := ((T k).list.node 0).2
  obtain ⟨hepsilon, hNT⟩ := (T k).initial_node_geometry
  have hcenter := (T k).node_zero_readout.2.2
  intro x hx
  refine ⟨⟨x, hNT hx⟩, ?_, rfl⟩
  have hdist := H.tube_initial_neck_distance_lt T k hsmall N hepsilon hcenter hNT hx
  change (H.tubeMetric T k).edist (H.tubeBase T k) ⟨x, hNT hx⟩ < ENNReal.ofReal Acrit
  apply hdist.trans_le
  apply ENNReal.ofReal_le_ofReal
  apply le_trans ?_ hAcrit
  have hε : 0 < epsilon := hepsilon ▸ N.epsilon_pos
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  nlinarith only [mul_pos (inv_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 4) hB))
    (inv_pos.mpr hε)]

set_option maxHeartbeats 2400000 in

theorem exists_retained_initial_node_capture_accuracy :
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
            let N := ((W.tube (i k)).list.node 0).2
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
  obtain ⟨j, hcoverage⟩ :=
    G.regular_component_coverage ((4 * max C 2)⁻¹ * epsilon⁻¹ / 32) hdelta
  refine ⟨j, ?_⟩
  filter_upwards [hcoverage] with k hk
  let N := ((W.tube (i k)).list.node 0).2
  obtain ⟨hepsN, _⟩ := (W.tube (i k)).initial_node_geometry
  have hcenter := (W.tube (i k)).node_zero_readout.2.2
  have hcritical := H.tubeCritical_contains_initial_node W.tube
    (hepsilon.trans hsmall) hlarge (i k)
  refine ⟨hk.1, ?_⟩
  intro x hx hheight
  obtain ⟨y, hy, hxy⟩ := hcritical hx
  have hregular := H.tubeCritical_initial_neck_core_component W.tube W.radius
    W.radius_pos (i k) N hepsN hcenter hcritical ⟨y, hy⟩
    (by simpa only [hxy] using hx) (by simpa only [hxy] using hheight)
  obtain ⟨q, hq, hqz⟩ := hk.2 hregular
  refine ⟨q, hq, ?_⟩
  exact (congrArg (fun z : H.tubeCriticalRegion W.tube W.radius (i k) => z.val.val)
    hqz).trans hxy

end CounterexampleNeckFamily

end PoincareConjecture.M28
