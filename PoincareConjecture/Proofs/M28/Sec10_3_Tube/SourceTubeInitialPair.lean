import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeScaleBudget











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

namespace SourceTubeData

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
  {S : CounterexampleNeckSegment E}



theorem node_zero_readout (T : SourceTubeData S) :
    T.list.node 0 = T.list.nodes.head T.list.nonempty ∧
      (T.list.node 0).1 = S.lower ∧
      (T.list.node 0).2.center = S.path S.lower := by
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have hzero : (0 : ℤ) ∈ T.list.active := by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  have hhead : T.list.node 0 = T.list.nodes.head T.list.nonempty := by
    rw [T.list.node_eq_getElem hzero]
    simp only [Int.toNat_zero, List.getElem_zero_eq_head]
  have htime : (T.list.node 0).1 = S.lower := by
    rw [hhead]
    exact T.list.head_time
  refine ⟨hhead, htime, ?_⟩
  simpa only [htime] using (T.list.node_center hzero).symm



theorem tube_chain_readout (T : SourceTubeData S) :
    T.tube.chain.shape = ChainShape.finite 0 (T.list.nodes.length - 1) ∧
      T.tube.chain.neck = fun i => (T.list.node i).2 := by
  have hshape : T.tube.chain.shape = T.chain.shape :=
    congr_heq (congr_arg_heq
      (fun e : ℝ => fun B : BalancedNeckChain (E.flow.metric E.time) e => B.shape)
      T.epsilon_eq) T.chain_eq
  have hneck : T.tube.chain.neck = T.chain.neck :=
    congr_heq (congr_arg_heq
      (fun e : ℝ => fun B : BalancedNeckChain (E.flow.metric E.time) e => B.neck)
      T.epsilon_eq) T.chain_eq
  refine ⟨hshape.trans T.shape_eq, hneck.trans ?_⟩
  funext i
  rw [T.neck_eq, T.list.neckOfList_eq_node]




theorem initial_pair (T : SourceTubeData S) (hlen : 2 ≤ T.list.nodes.length) :
    T.tube.chain.neck 0 = (T.list.node 0).2 ∧
      T.tube.chain.neck 1 = (T.list.node 1).2 ∧
      IsLeast T.tube.chain.shape.active 0 ∧
      (1 : ℤ) ∈ T.tube.chain.shape.active ∧
      (T.list.node 0).2.center = S.path S.lower ∧
      (T.list.node 1).2.epsilon = T.tube.epsilon ∧
      (T.list.node 1).2.center ∈ closure ((T.list.node 0).2.region
        ((255 : ℝ) * T.tube.epsilon⁻¹ / 256) T.tube.epsilon⁻¹) ∧
      ((0.999 : ℝ) * (T.list.node 0).2.scale < (T.list.node 1).2.scale ∧
        (T.list.node 1).2.scale < (1.001 : ℝ) * (T.list.node 0).2.scale) ∧
      ∃ P ∈ S.cover.necks,
        SourceEdgeCommonOrientationPacket (T.list.node 0).2 P (T.list.node 1).2
          (γ := S.path) (T.list.node 0).1 (T.list.node 1).1 ∧
        SourceEdgePacket (T.list.node 0).2 (T.list.node 1).2 epsilon := by
  obtain ⟨hshape, hneck⟩ := T.tube_chain_readout
  have hzero : (0 : ℤ) ∈ T.list.active := by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  have hone : (1 : ℤ) ∈ T.list.active := by
    change 0 ≤ (1 : ℤ) ∧ (1 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega
  have hleast : IsLeast T.tube.chain.shape.active 0 := by
    rw [hshape]
    refine ⟨hzero, ?_⟩
    intro i hi
    exact hi.1
  have honeT : (1 : ℤ) ∈ T.tube.chain.shape.active := by
    rw [hshape]
    exact hone
  obtain ⟨P, hP, H, J⟩ := T.list.node_edge hzero hone
  have hεzero : (T.list.node 0).2.epsilon = T.tube.epsilon :=
    (T.list.node_epsilon hzero).trans T.epsilon_eq.symm
  have hεone : (T.list.node 1).2.epsilon = T.tube.epsilon :=
    (T.list.node_epsilon hone).trans T.epsilon_eq.symm
  refine ⟨congrFun hneck 0, congrFun hneck 1, hleast, honeT,
    T.node_zero_readout.2.2, hεone, ?_, H.scale, P, hP, H, J⟩
  simpa only [hεzero, zero_add] using H.narrow_closure

end SourceTubeData

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}



theorem tubeNodeScale_zero (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    H.tubeNodeScale T k 0 = (4 * max C 2)⁻¹ :=
  H.normalizedSlice_low_neck_scale k ((T k).list.node 0).2
    (T k).node_zero_readout.2.2

end CounterexampleNeckFamily





theorem exists_source_tube_successor_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
          ∀ᶠ k in atTop, 2 ≤ (T k).list.nodes.length := by
  obtain ⟨epsilonR, hRpos, _, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨min epsilonR (1 / 10000), lt_min hRpos (by norm_num),
    min_le_right _ _, ?_⟩
  intro epsilon C A E H T hsmall
  filter_upwards [H.normalizedSlice_upper_scalar_tendsto.eventually
    (eventually_gt_atTop (32 * (max C 2) ^ 2))] with k hk
  by_contra hnot
  have hpositive : 0 < (T k).list.nodes.length :=
    List.length_pos_iff.mpr (T k).list.nonempty
  have hlength : (T k).list.nodes.length = 1 := by omega
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlength
  have hlast : (T k).list.nodes.getLast (T k).list.nonempty =
      (T k).list.node 0 := by
    rw [(T k).node_zero_readout.1]
    simp only [hp, List.getLast_singleton, List.head_cons]
  have hlast_time := ((T k).list.vertex _
    (List.getLast_mem (T k).list.nonempty)).1.2
  have hterminal : (H.segment k).path (H.segment k).upper ∈
      ((T k).list.node 0).2.carrier := by
    have h := (T k).list.terminal (right_mem_Icc.mpr hlast_time)
    simpa only [hlast] using h
  have hzero : (0 : ℤ) ∈ (T k).list.active := by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
    constructor <;> omega
  let N := ((T k).list.node 0).2
  have hε : N.epsilon ≤ epsilonR :=
    ((T k).list.node_epsilon hzero).trans_le
      (hsmall.trans (min_le_left _ _))
  have h := hratio ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time) N hε
    ((H.segment k).path (H.segment k).upper) hterminal N.center
    (N.central_sphere_subset N.center_on_central_sphere)
  change (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).upper⟩ ≤
    2 * (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, N.center⟩ at h
  rw [(T k).node_zero_readout.2.2, (H.segment k).lower_scalar] at h
  have hbound : (H.normalizedSliceConnection k).scalarCurvature
      ((H.segment k).path (H.segment k).upper) ≤ 32 * (max C 2) ^ 2 := by
    rw [H.normalizedSlice_scalar_eq]
    apply (div_le_iff₀ (H.base_scalar_pos k)).mpr
    nlinarith only [h]
  exact (not_le_of_gt hk) hbound

end PoincareConjecture.M28
