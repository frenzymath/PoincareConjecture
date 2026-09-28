import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialPair
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FirstNeckGraphFrontier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.SourceTubeData

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}

theorem isLeast_tube_chain_zero (T : SourceTubeData S) :
    IsLeast T.tube.chain.shape.active 0 := by
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  rw [T.tube_chain_readout.1]
  refine ⟨?_, fun _ hi => hi.1⟩
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
  constructor <;> omega

theorem initial_graph_negative_region (T : SourceTubeData S)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hbound : ∀ q, |f q| < epsilon⁻¹ / 32) :
    IsConnected ((T.list.node 0).2.belowGraph_m28 f) ∧
      frontier ((T.list.node 0).2.belowGraph_m28 f) ∩ T.tube.carrier =
        range (fun q => (T.list.node 0).2.coordinate_map (q, f q)) ∧
      ∀ x ∈ (T.list.node 0).2.belowGraph_m28 f,
        connectedComponentIn
          (T.tube.carrier \ range (fun q => (T.list.node 0).2.coordinate_map (q, f q))) x =
            (T.list.node 0).2.belowGraph_m28 f := by
  have hleast := T.isLeast_tube_chain_zero
  have hneck : T.tube.chain.neck 0 = (T.list.node 0).2 :=
    congrFun T.tube_chain_readout.2 0
  have heps : (T.list.node 0).2.epsilon = epsilon := by
    rw [← hneck, T.tube.chain.epsilon_eq 0 hleast.1, T.epsilon_eq]
  have hepspos : 0 < epsilon := heps ▸ (T.list.node 0).2.epsilon_pos
  have hA := inv_pos.mpr hepspos
  have hdom (q : UnitTwoSphere) : f q ∈
      Ioo (-(T.list.node 0).2.epsilon⁻¹) (T.list.node 0).2.epsilon⁻¹ := by
    rw [heps]
    have h := abs_lt.mp (hbound q)
    constructor <;> linarith [h.1, h.2]
  have hchainDom (q : UnitTwoSphere) : f q ∈
      Ioo (-(T.tube.chain.neck 0).epsilon⁻¹) (T.tube.chain.neck 0).epsilon⁻¹ := by
    rw [hneck]
    exact hdom q
  have hc : epsilon⁻¹ / 16 < T.tube.epsilon⁻¹ := by rw [T.epsilon_eq]; linarith
  have hupper (q : UnitTwoSphere) : f q ≤ epsilon⁻¹ / 16 := by
    linarith [(abs_lt.mp (hbound q)).2]
  refine ⟨(T.list.node 0).2.isConnected_belowGraph_m28 f hf hdom, ?_, ?_⟩
  · simpa only [hneck] using
      T.tube.frontier_first_belowGraph hleast f hf hchainDom hc hupper
  · intro x hx
    have hxchain : x ∈ (T.tube.chain.neck 0).belowGraph_m28 f := by rwa [hneck]
    simpa only [hneck] using
      T.tube.connectedComponentIn_first_belowGraph hleast f hf hchainDom hc hupper hxchain

end PoincareConjecture.M28.SourceTubeData
