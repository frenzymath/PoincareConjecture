import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckPathConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeScaleBudget













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}


structure SourceFiniteWalk
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) where
  initial_time :
    ((T k).list.nodes.head (T k).list.nonempty).1 = (H.segment k).lower
  terminal :
    MapsTo (H.segment k).path
      (Icc ((T k).list.nodes.getLast (T k).list.nonempty).1
        (H.segment k).upper)
      ((T k).list.nodes.getLast (T k).list.nonempty).2.carrier
  path_cover :
    MapsTo (H.segment k).path (Icc (H.segment k).lower (H.segment k).upper)
      {x | ∃ p ∈ (T k).list.nodes, x ∈ p.2.carrier}
  step : ∀ {i : ℤ}, i ∈ (T k).list.active → i + 1 ∈ (T k).list.active →
    ∃ P ∈ (H.segment k).cover.necks,
      SourceEdgeCommonOrientationPacket ((T k).list.node i).2 P
        ((T k).list.node (i + 1)).2 (γ := (H.segment k).path)
          ((T k).list.node i).1 ((T k).list.node (i + 1)).1 ∧
      SourceEdgePacket ((T k).list.node i).2 ((T k).list.node (i + 1)).2 epsilon
  prefix_cost : ∀ (n : ℕ), n < (T k).list.nodes.length →
    ENNReal.ofReal (∑ i ∈ Finset.range n,
      (0.99 : ℝ) * H.tubeNodeScale T k (i : ℤ) * epsilon⁻¹) ≤
      (H.normalizedSliceMetric k).pathELength (H.segment k).path
        (H.segment k).lower ((T k).list.node (n : ℤ)).1
  total_scale :
    ∑ i ∈ Finset.range ((T k).list.nodes.length - 1),
        H.tubeNodeScale T k (i : ℤ) <
      epsilon * (A + 2 * endpointConnectorBudget epsilon C) / (0.99 : ℝ)
  connector : ∀ (i : ℤ), i ∈ (T k).chain.shape.active →
    ∀ x : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier,
      x ∈ ((T k).chain.neck i).carrier →
      ∃ v ∈ Icc (0 : ℝ) 1,
        (H.segment k).path v ∈ ((T k).chain.neck i).carrier ∧
        (((T k).chain.neck i).coordinate_inverse
          ((H.segment k).path v)).2 =
          (((T k).chain.neck i).coordinate_inverse x).2 ∧
        ∃ c ∈ Ioo (0 : ℝ) 1, ∃ d ∈ Ioo (0 : ℝ) 1,
          v ∈ Icc c d ∧
          MapsTo (H.segment k).path (Icc c d)
            ((T k).chain.neck i).carrier ∧
          MapsTo (H.segment k).path
            (Icc (min v ((T k).list.node i).1)
              (max v ((T k).list.node i).1))
            ((T k).chain.neck i).carrier ∧
          intrinsicEDist ((E (k + H.shift)).flow.metric
              (E (k + H.shift)).time)
              ((T k).chain.neck i).carrier x
              ((H.segment k).path v) ≤
            ENNReal.ofReal (((T k).chain.neck i).scale *
              Real.sqrt (1 + epsilon) * Real.sqrt 2 * (Real.pi + 1))




theorem exists_source_finite_walk_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ k, Nonempty (SourceFiniteWalk H T k) := by
  obtain ⟨epsilon₀, hpos, hsmall, hconnector⟩ :=
    exists_source_neck_path_connector_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hsmall k
  refine ⟨{
    initial_time := (T k).list.head_time
    terminal := (T k).list.terminal
    path_cover := (T k).list.covers
    step := ?_
    prefix_cost := ?_
    total_scale := H.tube_scale_sum_bound T k
    connector := ?_ }⟩
  · intro i hi hnext
    exact (T k).list.node_edge hi hnext
  · intro n hn
    exact H.tube_prefix_scale_cost_le T k n hn
  · intro i hi x hx
    exact hconnector (H.segment k) (H.base_scalar_pos k) hsmall (T k) i hi x hx



theorem exists_source_finite_walk_family_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∃ T : ∀ k, SourceTubeData (H.segment k),
          ∀ k, Nonempty (SourceFiniteWalk H T k) := by
  obtain ⟨epsilonT, hTpos, hTsmall, hT⟩ :=
    exists_source_tube_family_accuracy.{u}
  obtain ⟨epsilonW, hWpos, hWsmall, hW⟩ :=
    exists_source_finite_walk_accuracy.{u}
  let epsilon₀ := min epsilonT epsilonW
  refine ⟨epsilon₀, lt_min hTpos hWpos,
    (min_le_left _ _).trans (hTsmall.trans (by norm_num)), ?_⟩
  intro epsilon C A E H hsmall
  obtain ⟨T⟩ := hT H (hsmall.trans (min_le_left _ _))
  refine ⟨T, ?_⟩
  intro k
  exact hW H T (hsmall.trans (min_le_right _ _)) k

end PoincareConjecture.M28.CounterexampleNeckFamily
