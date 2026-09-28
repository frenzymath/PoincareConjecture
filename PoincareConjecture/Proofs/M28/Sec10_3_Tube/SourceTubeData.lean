import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceActualTube
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFamilyScales

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

structure SourceTubeData {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    (S : CounterexampleNeckSegment E) where
  list : SourceOrientedList S
  chain : BalancedNeckChain (E.flow.metric E.time) epsilon
  shape_eq : chain.shape = ChainShape.finite 0 (list.nodes.length - 1)
  neck_eq : chain.neck = neckOfList (list.nodes.map Prod.snd)
    (list.nodes.head list.nonempty).2
  source_eq : chain.source_necks = S.cover.necks
  tube : EpsilonTubeCertificate (E.flow.metric E.time) S.cover.X
  epsilon_eq : tube.epsilon = epsilon
  chain_eq : HEq tube.chain chain
  carrier_eq : tube.carrier = chain.unionOpen

theorem exists_source_tube_data_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
          Nonempty (SourceTubeData S) := by
  obtain ⟨epsilon₀, hpos, hsmall, h⟩ := exists_actual_source_tube_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hbound
  obtain ⟨L, B, hshape, hneck, hsource, T, heps, hchain, hcarrier⟩ :=
    h E S hbase hbound
  exact ⟨⟨L, B, hshape, hneck, hsource, T, heps, hchain, hcarrier⟩⟩

namespace SourceTubeData

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}

def carrierOpen (T : SourceTubeData S) : TopologicalSpace.Opens
    (E.flow.slice E.time).carrier := ⟨T.tube.carrier, T.tube.carrier_open⟩

theorem path_mem (T : SourceTubeData S) :
    MapsTo S.path (Icc S.lower S.upper) T.carrierOpen := by
  intro s hs
  apply T.tube.contains_X
  rw [S.cover_set]
  exact mem_image_of_mem _ hs

theorem exists_initial_neck (T : SourceTubeData S) :
    ∃ N ∈ S.cover.necks, N.epsilon = epsilon ∧
      N.center = S.path S.lower ∧ N.carrier ⊆ T.carrierOpen := by
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have hzero : (0 : ℤ) ∈ T.list.active := by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  have hzeroB : (0 : ℤ) ∈ T.chain.shape.active := by
    rw [T.shape_eq]
    exact hzero
  have hhead : T.chain.neck 0 = (T.list.nodes.head T.list.nonempty).2 := by
    rw [T.neck_eq, T.list.neckOfList_eq_node, T.list.node_eq_getElem hzero]
    simp only [Int.toNat_zero, List.getElem_zero_eq_head]
  have hcarrier : (T.list.nodes.head T.list.nonempty).2.carrier ⊆ T.carrierOpen := by
    intro x hx
    change x ∈ T.tube.carrier
    rw [T.carrier_eq]
    change x ∈ ⋃ i : {i // i ∈ T.chain.shape.active}, (T.chain.neck i.1).carrier
    exact mem_iUnion.mpr ⟨⟨0, hzeroB⟩, by simpa only [hhead] using hx⟩
  obtain ⟨_, N, hN, hchoice, hcenter⟩ :=
    T.list.vertex _ (List.head_mem T.list.nonempty)
  rw [T.list.head_time] at hcenter
  refine ⟨N, hN, (S.cover.neck_epsilon N hN).trans S.cover_epsilon, ?_, ?_⟩
  · rcases hchoice with h | h <;>
      simpa only [h, EpsilonNeck.reversed_center] using hcenter.symm
  · rcases hchoice with h | h <;>
      simpa only [h, EpsilonNeck.reversed_carrier] using hcarrier

theorem preconnected (T : SourceTubeData S) : PreconnectedSpace T.carrierOpen := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  let : PreconnectedSpace (Ioo (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  exact T.tube.cylinder.homeomorph.surjective.denseRange.preconnectedSpace
    T.tube.cylinder.homeomorph.continuous

end SourceTubeData

theorem exists_source_tube_family_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E),
        epsilon ≤ epsilon₀ → Nonempty (∀ k, SourceTubeData (H.segment k)) := by
  obtain ⟨epsilon₀, hpos, hsmall, h⟩ := exists_source_tube_data_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hbound
  exact ⟨fun k => Classical.choice
    (h (E (k + H.shift)) (H.segment k) (H.base_scalar_pos k) hbound)⟩

end PoincareConjecture.M28
